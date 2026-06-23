{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SPLL.Typing.PInfer2 (
  addPTypeInfo
, tryAddPTypeInfo
, PTypeError (..)
) where

import Control.Monad.Except
import Control.Monad.State

import Data.List (delete)
import qualified Data.Set as Set

import Data.Monoid()
import Data.Either (lefts)
import Data.Foldable hiding (toList)
import qualified Data.Map as Map
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.PType
import SPLL.Typing.RType hiding (TV)
import Control.Monad (replicateM)
import SPLL.Lang.Types (CompilerError, ADTDecl)
import PredefinedFunctions (isFieldConstructor)

data PTypeError
  = UnificationFail PType PType
  | InfiniteType TVar PType
  | UnboundVariable String
  deriving (Show)

type Infer = ExceptT PTypeError (State InferState)

-- Scheme: Forall [a b c] [a=(b|c), a=(b + c)] (a->b->c)
data DScheme = DScheme [TVar] [DConstraint] PType
  deriving (Show, Eq)


-- Tree of constraints. Leafes are types and constraints connect one or more nodes
data ChainConstraint = PlusConstraint TypeOrChain TypeOrChain | EnumPlusConstraint TypeOrChain TypeOrChain | CompConstraint TypeOrChain TypeOrChain
  deriving (Show, Eq)
-- Node of the tree
type TypeOrChain = Either PType DowngradeChain
-- Collection of children constraints of a node or a leaf
type DowngradeChain = [Either PType ChainConstraint]
-- A type variable with constraints on it
-- E.g.: plusF :: a -> b -> c has constraint (c, PlusConstraint a b)
type DConstraint = (PType, DowngradeChain)

-- | Downgrade PNormal/PLogNormal to Integrate for contexts where Gaussian
-- structure cannot be preserved (containers, mixtures, unknown InjFs).
degradeNormal :: PType -> PType
degradeNormal PNormal    = Integrate
degradeNormal PLogNormal = Integrate
degradeNormal p          = p

-- | Post-process the result of inferBinOp for container/mixture expressions to
-- ensure the result PType never carries Normal/LogNormal structure.
--
-- When the result is still a TVar, we inspect the constraint chain for that TVar
-- (which by the time Cons/TCons/Apply return will have concrete leaves) to check
-- whether it would resolve to PNormal or PLogNormal. Only in that case do we
-- remove the constraint and inject TVar→Integrate into the substitution.
-- This avoids incorrectly degrading Deterministic results (which would cascade
-- into resolvePlusCons returning Bottom for outer expressions).
--
-- When the result is already a concrete type, we degrade it directly.
degradeNormalResult :: (Subst, [DConstraint], PType, Expr)
                    -> (Subst, [DConstraint], PType, Expr)
degradeNormalResult (s, cs, TVar tv, e) =
  case lookup (TVar tv) cs of
    Just chain | wouldBeNormal chain ->
      let cs'        = filter (\(ty, _) -> ty /= TVar tv) cs
          forceSubst = Subst $ Map.singleton tv Integrate
      in ( compose forceSubst s
         , apply forceSubst cs'
         , Integrate
         , setTypeInfo e (getTypeInfo e){pType = Integrate}
         )
    _ -> (s, cs, TVar tv, setTypeInfo e (getTypeInfo e){pType = TVar tv})
  where
    wouldBeNormal chain = case collapseChain chain Deterministic [] of
      [Left PNormal]    -> True
      [Left PLogNormal] -> True
      _                 -> False
degradeNormalResult (s, cs, t, e) =
  let t' = degradeNormal t
  in (s, cs, t', setTypeInfo e (getTypeInfo e){pType = t'})

resolvePlusCons :: PType -> PType -> PType
resolvePlusCons Integrate   Integrate   = Bottom
resolvePlusCons PNormal     PNormal     = Bottom
resolvePlusCons PNormal     Integrate   = Bottom
resolvePlusCons Integrate   PNormal     = Bottom
resolvePlusCons PLogNormal  PLogNormal  = Bottom
resolvePlusCons PLogNormal  Integrate   = Bottom
resolvePlusCons Integrate   PLogNormal  = Bottom
resolvePlusCons PNormal     PLogNormal  = Bottom
resolvePlusCons PLogNormal  PNormal     = Bottom
resolvePlusCons _ _ = Deterministic

-- Enumerability allows us to still infer prob in cases in which normal inference would fail
resolveEnumPlusCons :: PType -> PType -> PType
resolveEnumPlusCons Integrate Integrate = Integrate
resolveEnumPlusCons _ _ = Deterministic

resolveCompCons :: PType -> PType -> PType
resolveCompCons Integrate   Integrate   = Bottom
resolveCompCons PNormal     Integrate   = Bottom
resolveCompCons Integrate   PNormal     = Bottom
-- Two Gaussians: left - right is Normal, so the comparison reduces to a Gaussian
-- CDF evaluated at 0 (see the both-PNormal LessThan/GreaterThan IR-gen). The
-- result is a Bool with a closed-form probability, i.e. Integrate -- never PNormal
-- (a Bool can never be Gaussian; leaving it PNormal makes the function compiler try
-- to extract (mu, sigma) from the comparison and crash in toIRNormalParams).
resolveCompCons PNormal     PNormal     = Integrate
-- Gaussian (or log-Gaussian) vs a constant bound: the existing Deterministic-side
-- LessThan/GreaterThan path integrates the distribution's CDF up to that bound.
resolveCompCons PNormal     Deterministic = Integrate
resolveCompCons Deterministic PNormal     = Integrate
resolveCompCons PLogNormal  Deterministic = Integrate
resolveCompCons Deterministic PLogNormal  = Integrate
resolveCompCons PLogNormal  Integrate   = Bottom
resolveCompCons Integrate   PLogNormal  = Bottom
resolveCompCons PLogNormal  PLogNormal  = Bottom
resolveCompCons PNormal     PLogNormal  = Bottom
resolveCompCons PLogNormal  PNormal     = Bottom
resolveCompCons _ _ = Deterministic

addPTypeInfo :: Program -> Either CompilerError Program
addPTypeInfo p = do
    case inferProgram mempty p of
       Left err -> Left ("Error in addPTypeInfo: " ++ show err)
       Right (_, _, p) -> Right p

tryAddPTypeInfo :: Program -> Either PTypeError Program
tryAddPTypeInfo p = do
  (_,_,p2) <- inferProgram mempty p
  return p2

newtype TEnv
  = TypeEnv {types :: Map.Map Name PType}
  deriving (Eq, Show)

instance Semigroup TEnv where
  (TypeEnv a) <> (TypeEnv b) = TypeEnv (Map.union a b)

instance Monoid TEnv where
  mempty = TypeEnv Map.empty
  mappend = (<>)

-- | Inference state
-- adtEnv carries the program's ADT declarations so the InjF inference branch
-- can recognise field constructors (Cons/TCons/user-ADT constructors) and give
-- them product/downgrade semantics instead of additive PlusConstraint semantics.
data InferState = InferState { var_count :: Int, adtEnv :: [ADTDecl] }

-- | Initial inference state
initInfer :: InferState
initInfer = InferState { var_count = 0, adtEnv = [] }

newtype Subst = Subst (Map.Map TVar PType)
  deriving (Eq, Show, Monoid, Semigroup)

newtype DSubst = DSubst (Map.Map TVar DowngradeChain)
  deriving (Eq, Show, Monoid, Semigroup)

class DSubstitutable a where
  dapply :: DSubst -> a -> a

instance DSubstitutable [(PType, DowngradeChain)] where
  dapply = map . dapply

instance DSubstitutable (PType, DowngradeChain) where
  dapply s (ty, dc) = (ty, dapply s dc)

instance DSubstitutable DowngradeChain where
  dapply s dc = concatMap (substChain s) dc

instance DSubstitutable ChainConstraint where
  dapply s (PlusConstraint ty1 ty2) = PlusConstraint (dapply s ty1) (dapply s ty2)
  dapply s (EnumPlusConstraint ty1 ty2) = EnumPlusConstraint (dapply s ty1) (dapply s ty2)
  dapply s (CompConstraint ty1 ty2) = CompConstraint (dapply s ty1) (dapply s ty2)


instance DSubstitutable TypeOrChain where
  dapply  (DSubst s) (Left (TVar ty)) =
    case res of
       Nothing -> Left (TVar ty)
       (Just f) -> Right f
       where res = Map.lookup ty s
  dapply  (DSubst _) (Left ty) = Left ty
  dapply s (Right dc) = Right $ dapply s dc

dcompose :: DSubst -> DSubst -> DSubst
(DSubst s1) `dcompose` (DSubst s2) = DSubst $ Map.map (dapply (DSubst s1)) s2 `Map.union` s1

substChain :: DSubst -> Either PType ChainConstraint -> [Either PType ChainConstraint]
substChain (DSubst s) (Left (TVar ty)) = Map.findWithDefault [Left (TVar ty)] ty s
substChain (DSubst _) (Left ty) = [Left ty]
substChain dsubst (Right cs)  = [Right $ dapply dsubst cs]


-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------
inferProgram::  TEnv -> Program -> Either PTypeError ([DConstraint], DScheme, Program)
inferProgram env = runInferProg env . inferProg env

runInferProg :: TEnv -> Infer (Subst, [DConstraint], PType, Program) -> Either PTypeError ([DConstraint], DScheme, Program)
runInferProg env m = case evalState (runExceptT m) initInfer of
  Left err  -> Left err
  Right (s, c, t, p) -> Right $ closeProg env c t (apply s p)

buildConstraint ::  [DConstraint] -> [DConstraint] -> Subst -> ([DConstraint], Subst)
buildConstraint resList [] s = (resList, s)
buildConstraint resList cons s = case consElem of
  Just dcons -> buildConstraint (apply subst resList) (apply subst (delete dcons cons)) (compose s subst)
    where (_, subst, _) = isConsResolved [collapse dcons]
  Nothing -> (resList ++ cons, s)
  where consElem = find isConsResolvable cons

-- insert constraint chains into each other, so only the ones with direct cyclic dependencies remain
bundleConstraints :: DConstraint -> [DConstraint] -> [DConstraint]
bundleConstraints topD@(topTy, _) dcons = case nonRecType of
  Nothing -> topD:dcons
  Just tvar -> let (tv, dc) = extractType (TVar tvar) dcons
                   dsubst = DSubst $ Map.singleton tvar dc in
               bundleConstraints (dapply dsubst topD) (dapply dsubst (delete (tv, dc) dcons))

  where (TVar topTyVar) = topTy
        dftv = delete topTyVar (Set.toList $ ftv topD)
        nonRecType = getNonRecType dftv dcons

getNonRecType :: [TVar] -> [DConstraint] -> Maybe TVar
getNonRecType [] _ = Nothing
getNonRecType (tvar:tvar_rem) dConsList =
  if elem tvar (ftv dcons)
  then getNonRecType tvar_rem dConsList
  else Just tvar
  where dcons = extractType (TVar tvar) dConsList

isRecType ::  DConstraint -> Bool
isRecType (TVar tv, dc) = let freeVars = ftv dc in Set.null freeVars || (tv `Set.member` freeVars && Set.size freeVars == 1)
isRecType (_, _) = error "non tvar variable in fixpoint iterations"

--collapses the constraint and checks if is resolved.
-- A constraint is resolved if it collapses to var = basicType
isConsResolvable :: DConstraint -> Bool
isConsResolvable dcons =  ret
  where (_, _, ret) = isConsResolved [collapsedCons]
        collapsedCons = collapse dcons

extractType :: PType -> [DConstraint] -> DConstraint
extractType _ [] = error "Could not find top type"
extractType ty ((pty, dc):b) = if ty == pty then (pty, dc) else extractType ty b

-- we iterate through the DowngradeChain.
--  whenever we find a Left BasicType, we downgrade the "resulting type" (snd arg)
--  whenever we find a Left non-basic, we put it in the third argument, the output chain.
--  whenever we find a constraint, we try to force it down to two simple types, which we resolve and continue.
--    if we can not force it, we eventually return the constraint. 
collapseChain :: DowngradeChain -> PType -> DowngradeChain -> DowngradeChain
collapseChain [] ty dcOut = Left ty : dcOut
collapseChain ((Left ty1):b) ty2 dcOut = if isBasicType ty1
                                         then collapseChain b (downgrade ty1 ty2) dcOut
                                         else collapseChain b ty2 dcOut ++ [Left ty1]
collapseChain ((Right (PlusConstraint (Left Deterministic) _)):b) ty3 dcOut = collapseChain b (downgrade Deterministic ty3) dcOut
collapseChain ((Right (PlusConstraint _ (Left Deterministic))):b) ty3 dcOut = collapseChain b (downgrade Deterministic ty3) dcOut
collapseChain ((Right (PlusConstraint ty1 ty2)):b) ty3 dcOut = if isResolved
   then collapseChain b (downgrade (resolvePlusCons rty1 rty2) ty3) dcOut
   else collapseChain b ty3 dcOut ++ [Right (PlusConstraint (subCollapse ty1) (subCollapse ty2))]
   where (b1, rty1) = getResType ty1
         (b2, rty2) = getResType ty2
         isResolved = b1 && b2
collapseChain ((Right (EnumPlusConstraint ty1 ty2)):b) ty3 dcOut = if isResolved
   then collapseChain b (downgrade (resolveEnumPlusCons rty1 rty2) ty3) dcOut
   else collapseChain b ty3 dcOut ++ [Right (EnumPlusConstraint (subCollapse ty1) (subCollapse ty2))]
   where (b1, rty1) = getResType ty1
         (b2, rty2) = getResType ty2
         isResolved = b1 && b2
collapseChain ((Right (CompConstraint ty1 ty2)):b) ty3 dcOut =
    if isResolved
    then collapseChain b (downgrade (resolveCompCons rty1 rty2) ty3) dcOut
    else collapseChain b ty3 dcOut ++ [Right (CompConstraint (subCollapse ty1) (subCollapse ty2))]
    where (b1, rty1) = getResType ty1
          (b2, rty2) = getResType ty2
          isResolved = b1 && b2
subCollapse :: TypeOrChain -> TypeOrChain
subCollapse (Left ty) = Left  ty
subCollapse (Right dc) = Right $ collapseChain dc Deterministic []

-- tries to force a chain down to a single basictype element.
getResType :: TypeOrChain -> (Bool, PType)
getResType (Left ty) = if isBasicType ty then (True, ty) else (False, Bottom)
getResType (Right dc) = if length nestedCollapse == 1 && length (lefts nestedCollapse) == 1
  then (True, head (lefts nestedCollapse)) else (False, Bottom)
  where nestedCollapse = collapseChain dc Deterministic []

collapse :: DConstraint -> DConstraint
collapse (ty, dc) = (ty, collapseChain dc Deterministic [])

isConsResolved :: [DConstraint] -> ([DConstraint], Subst, Bool)
isConsResolved [(TVar a, [Left ty])] | isBasicType ty = ([], Subst $ Map.singleton a ty, True)
isConsResolved cons = (cons, emptySubst, False)

resolveStep ::  [DConstraint] -> PType -> ([DConstraint], PType, Bool, Subst)
resolveStep [] ty = ([], ty, True, emptySubst)
resolveStep cons ty = (consRes, resType, isResolvedRes, substRes)
  where (cons', subst1) = buildConstraint [] cons emptySubst

        topConsB =  extractType ty cons'
        consNoTopB = delete topConsB cons'
        consBundles = map collapse $ bundleConstraints topConsB consNoTopB

        noCycleType = apply subst1  ty
        (consRes, resType, isResolvedRes, substRes) =
          if null cons'
          then ([], apply subst1 ty, True, subst1)
          else (consBundles, noCycleType, False, subst1)



fixpointIteration :: DConstraint -> Subst
fixpointIteration dcons@(TVar tv, _) = compose (Subst $ Map.singleton tv ty) substRes
  where (ty, substRes) = fixpointStep Deterministic dcons emptySubst

fixpointStep :: PType -> DConstraint -> Subst -> (PType, Subst)
fixpointStep curType (TVar tv, dc) subst =
  if isResolved
  then
    (if curType == stepTy
     then (curType, subst')
     else fixpointStep stepTy (TVar tv, dc) subst'
    )
  else error "non resolved fixpoint step"
  where replacedDC = apply (Subst $ Map.singleton tv curType) dc
        collapsedCons = collapse (TVar tv, replacedDC)
        (_, consSubst ,isResolved) = isConsResolved [collapsedCons]
        stepTy = apply consSubst (TVar tv)
        subst' = compose consSubst subst

solveCyclicConstraints :: [DConstraint] -> PType -> Subst -> ([DConstraint], PType, Subst)
solveCyclicConstraints dcons pty s | isBasicType pty = (dcons, pty, s)
solveCyclicConstraints dcons pty s = case nextCons of
  Nothing -> error "no rec cons in fixpoint, but final type not resolved"
  Just d -> let fixSubst = fixpointIteration d in
    solveCyclicConstraints (apply fixSubst (delete d dcons)) (apply fixSubst pty) (compose s fixSubst)
  where nextCons = find isRecType dcons

closeProg :: TEnv -> [DConstraint] -> PType -> Program -> ([DConstraint], DScheme, Program )
closeProg env cons ty tp = (cons', DScheme alph consRes  resType', apply finalSubst tp)
  where alph = Set.toList $ Set.difference (Set.union (ftv cons') (ftv resType)) (ftv env)
        (cons', resType, isResolved, su) = resolveStep cons ty
        (consRes, resType', su2) = if isResolved then (cons', resType, emptySubst) else
                   solveCyclicConstraints cons' resType emptySubst
        -- after cyclic constraints are resolved we needs subst to fill missing ptypes in expr tree
        (_, _, _, su3) = if isResolved then (cons', resType, isResolved, emptySubst) else resolveStep (apply su2 cons) resType
        finalSubst = su `compose` (su2 `compose` su3)

-- Substitutes such that the two types are equal
unify ::  PType -> PType -> Infer Subst
unify a b | a == b = return emptySubst
unify (l `PArr` r) (l' `PArr` r')  = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  return (s2 `compose` s1)
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify t1 t2 = throwError $ UnificationFail t1 t2

-- Substitutes such that the variable maps to the specified type
bind ::  TVar -> PType -> Infer Subst
bind a t
  | t == TVar a     = return emptySubst
  | occursCheck t a = throwError $ InfiniteType a t
  | otherwise       = return $ Subst $ Map.singleton a t

occursCheck ::  Substitutable a => a -> TVar ->  Bool
occursCheck t a =  a `Set.member` ftv t

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

-- Creates a fresh variable
fresh :: Infer PType
fresh = do
    s <- get
    put s{var_count = var_count s + 1}
    return $ TVar $ TV (letters !! var_count s)

-- infer an argument of an operator (function) and applies it to the operator. Reduces the arity of the operator by one
-- E.g. plusF with one expression yielding a float will result in a pType of Float -> Float
-- Environment -> Expression -> (Initial substitution) -> (Initial constraints) -> (PType of the operator) -> (Resulting substitution, resulting constraints, Return type of this application, typed expresison)
applyOpArg :: TEnv -> Expr -> Subst -> [DConstraint] -> PType -> Infer (Subst, [DConstraint], PType, Expr)
applyOpArg env expr s1 cs1 t1 = do
  -- Infer the argument expression
  (s2, cs2, t2, exprt) <- infer (apply s1 env) expr
  -- This will be the return type of this application
  tv1 <- fresh
  -- Unify the expected pType of the operator with this application of an argument. This will reduce the arity of the operator by one
  s3 <- unify (apply s2 t1) (PArr t2 tv1)
  -- Compose all the substitutions found
  return (s3 `compose` s2 `compose` s1,
    -- Return newly found constraints
    apply (s3 `compose` s2) cs1 ++ apply s3 cs2,
    -- The return type of the application of the argument to the operator
    apply s3 tv1,
    -- The same expression but typed
    exprt)

-- if we already know the type of the first argument in a binary operator..
applyOpTy :: TEnv -> PType -> Subst -> [DConstraint] -> PType -> Infer (Subst, [DConstraint], PType)
applyOpTy _ ty s1 cs1 t1 = do
  tv1 <- fresh
  s3       <- unify t1 (PArr ty tv1)
  return (s3 `compose` s1,
    apply s3  cs1,
    apply s3 tv1)

freshVars :: Int -> [PType] -> Infer [PType]
freshVars 0 rts = do
    return rts
freshVars n rts = do
    s <- get
    put s{var_count = var_count s + 1}
    freshVars (n - 1)  (TVar (TV (letters !! var_count s)):rts)

fst4 :: (Subst, [DConstraint], PType, Expr) -> Subst
fst4 (x, _, _, _) = x
snd4 :: (Subst, [DConstraint], PType, Expr) -> [DConstraint]
snd4 (_, x, _, _) = x
trd4 :: (Subst, [DConstraint], PType, Expr) -> PType
trd4 (_, _, x, _) = x
frth4 :: (Subst, [DConstraint], PType, Expr) -> Expr
frth4 (_, _, _, x) = x

plusInf :: Infer (Subst, [DConstraint], PType)
plusInf = do
   tv1 <- fresh
   tv2 <- fresh
   tv3 <- fresh
   return (emptySubst, [(tv3, [Left tv1, Left tv2, Right (PlusConstraint (Left tv1) (Left tv2))])], tv1 `PArr` tv2 `PArr` tv3)

negInf :: Infer (Subst, [DConstraint], PType)
negInf = do
  tv1 <- fresh
  tv2 <- fresh
  return (emptySubst, [(tv2, [Left tv1])], tv1 `PArr` tv2)

compInf :: Infer (Subst, [DConstraint], PType)
compInf = do
   tv1 <- fresh
   tv2 <- fresh
   tv3 <- fresh
   return (emptySubst, [(tv3, [Left tv1, Left tv2, Right (CompConstraint (Left tv1) (Left tv2))])], tv1 `PArr` tv2 `PArr` tv3)

downgradeInf :: Infer (Subst, [DConstraint], PType)
downgradeInf = do
   tv1 <- fresh
   tv2 <- fresh
   tv3 <- fresh
   return (emptySubst, [(tv3, [Left tv1, Left tv2])], tv1 `PArr` tv2 `PArr` tv3)

makeEqConstraint :: PType -> PType -> DConstraint
makeEqConstraint t1 t2 = (t1, [Left t2])

inferProg :: TEnv -> Program -> Infer (Subst, [DConstraint], PType, Program)
inferProg env (Program decls nns adts enc) = do
  -- Make the ADT declarations available to the InjF inference branch so it can
  -- detect field constructors (Cons/TCons/user-ADT constructors).
  modify (\s -> s { adtEnv = adts })
  -- init type variable for all function decls beforehand so we can build constraints for
  -- calls between these functions
  tv_rev <- freshVars (length decls) []
  let tvs = reverse tv_rev
  -- env building with (name, ptype) for infer methods
  let func_tvs = zip (map fst decls) tvs
  -- Distribution primitives are prelude-bound Vars (reserved names), seeded here so
  -- `Var "Uniform"`/`Var "Normal"` resolve to their probabilistic types.
  let fenv = TypeEnv $ Map.unions [Map.fromList func_tvs, types env, Map.fromList distributionPrimitives]
  -- infer the type and constraints of the declaration expressions
  cts <- mapM (infer fenv . snd) decls
  let Just expr = lookup "main" decls
  -- inferring the type of the top level expression
  (s1, cs1, t1, _) <- infer fenv expr
  -- building the constraints that the built type variables of the functions equal
  -- the inferred function type
  let tcs = zipWith makeEqConstraint tvs (map trd4 cts)
  -- combine all constraints
  return (s1, cs1 ++ concatMap snd4 cts ++ tcs , t1, Program (zip (map fst decls) (map frth4 cts)) nns adts enc)

-- | Probabilistic types of the prelude-primitive distributions, keyed by their
-- reserved Var names. Uniform has a known CDF (Integrate); Normal admits the
-- closed-form Gaussian shortcut (PNormal).
distributionPrimitives :: [(Name, PType)]
distributionPrimitives = [("Uniform", Integrate), ("Normal", PNormal)]

isEnumerable :: Expr -> Bool
isEnumerable e = foldr (\tag b -> b || isEnum tag) False (tags (getTypeInfo e))
  where isEnum (DiscreteValues _) = True
        isEnum _ = False

-- | Determine whether an InjF operation on arguments with given PTypes preserves
-- Normal or LogNormal structure, and if so, return the resulting PType.
tryNormalClosure :: String -> [PType] -> Maybe PType
-- Normal arithmetic closure (linear space)
tryNormalClosure "plus" [PNormal, PNormal]       = Just PNormal
tryNormalClosure "plus" [PNormal, Deterministic] = Just PNormal
tryNormalClosure "plus" [Deterministic, PNormal] = Just PNormal
tryNormalClosure "mult" [PNormal, Deterministic] = Just PNormal
tryNormalClosure "mult" [Deterministic, PNormal] = Just PNormal
-- Negation: preserves Gaussian structure (mu → -mu); deterministic stays deterministic.
-- Required so that `a - b` = `a + neg(b)` propagates PNormal through the outer `plus`.
tryNormalClosure "neg"  [PNormal]               = Just PNormal
tryNormalClosure "neg"  [Deterministic]         = Just Deterministic
-- exp of Normal yields LogNormal; log of LogNormal yields Normal
tryNormalClosure "exp"  [PNormal]               = Just PLogNormal
tryNormalClosure "log"  [PLogNormal]            = Just PNormal
-- LogNormal multiplicative closure (log space)
tryNormalClosure "mult" [PLogNormal, PLogNormal]    = Just PLogNormal
tryNormalClosure "mult" [PLogNormal, Deterministic] = Just PLogNormal
tryNormalClosure "mult" [Deterministic, PLogNormal] = Just PLogNormal
-- LogNormal analytic transforms (each follows from f(exp x) = exp(g x), so the
-- log-space variable stays Gaussian): sqrt → exp(x/2), sq → exp(2x), recip → exp(-x).
-- The corresponding (mu_log, sigma) rescalings live in toIRLogNormalParams.
tryNormalClosure "sqrt"  [PLogNormal]               = Just PLogNormal
tryNormalClosure "sq"    [PLogNormal]               = Just PLogNormal
tryNormalClosure "recip" [PLogNormal]               = Just PLogNormal
tryNormalClosure _      _                           = Nothing


-- | Infer a binary operator expression using a given constraint function and constructor
inferBinOp :: TEnv -> TypeInfo -> Expr -> Expr
           -> Infer (Subst, [DConstraint], PType)
           -> (TypeInfo -> Expr -> Expr -> Expr)
           -> Infer (Subst, [DConstraint], PType, Expr)
inferBinOp env ti e1 e2 getInf constructor = do
  (s1, cs1, t1) <- getInf
  (s2, cs2, t2, et1) <- applyOpArg env e1 s1 cs1 t1
  (s3, cs3, t3, et2) <- applyOpArg env e2 s2 cs2 t2
  return (s3, cs3, t3, constructor (setPType ti t3) et1 et2)

infer :: TEnv -> Expr -> Infer (Subst, [DConstraint], PType, Expr)
infer env expr = case expr of

  ThetaI ti a i  -> return (emptySubst, [], Deterministic, ThetaI (setPType ti Deterministic) a i)
  Subtree ti a i  -> return (emptySubst, [], Deterministic, Subtree (setPType ti Deterministic) a i)
  Constant ti val  -> return (emptySubst, [], Deterministic, Constant (setPType ti Deterministic) val)
  InjF ti (Named name) paramsExpr -> do
    p_inf <- mapM (infer env) paramsExpr
    let pts = map trd4 p_inf
    let s_acc = foldl compose emptySubst (map fst4 p_inf)
    let accCs = concatMap snd4 p_inf
    let inferredExprs = map frth4 p_inf
    adts <- gets adtEnv
    case tryNormalClosure name pts of
      Just pt ->
        return (s_acc, accCs, pt, InjF (setPType ti pt) (Named name) inferredExprs)
      _ | isFieldConstructor adts name -> do
        -- Field constructors (Cons/TCons/user-ADT constructors) combine
        -- independent fields, so the result is as inferable as the weakest
        -- field (the meet of the field PTypes) — not the additive PlusConstraint
        -- of correlated operands, which would collapse two probabilistic fields
        -- to Bottom. A flat chain of Left constraints encodes this meet;
        -- degradeNormalResult then strips any residual Normal structure, since
        -- the container leaves are concrete by the time it runs.
        tv <- fresh
        return $ degradeNormalResult (s_acc, accCs ++ [(tv, map Left pts)], tv, InjF (setPType ti tv) (Named name) inferredExprs)
      Nothing -> do
        -- PNormal/PLogNormal must not propagate through InjFs that aren't in
        -- tryNormalClosure — downgrade them to Integrate so the general
        -- constraint machinery doesn't accidentally assign a Normal type.
        let pts' = map degradeNormal pts
        -- If all parameters are enumerable, we can use weaker constraints
        let constraint = if all isEnumerable paramsExpr then EnumPlusConstraint else PlusConstraint
        tv <- fresh
        let cs = case pts' of
              (p_fst:p_rst) ->
                let leftPts = map Left pts'
                in leftPts ++ foldr (\p acc -> [Right $ constraint (Left p) (Right acc)]) [Left p_fst] p_rst
              [] -> []
        return (s_acc, accCs ++ [(tv,cs)], tv, InjF (setPType ti tv) (Named name) inferredExprs)

  GreaterThan ti e1 e2 -> inferBinOp env ti e1 e2 compInf GreaterThan
  LessThan ti e1 e2   -> inferBinOp env ti e1 e2 compInf LessThan

  Var ti name ->
      case Map.lookup name (types env) of
          Nothing -> return (emptySubst, [], Deterministic, Var (setPType ti Deterministic) name)
          Just t  -> return (emptySubst, [], t, Var (setPType ti t) name)

  IfThenElse ti cond tr fl -> do
    (s1, cs1, t1) <- downgradeInf
    (s2, cs2, t2, condt) <- applyOpArg env cond s1 cs1 t1
    (s3, cs3, t3, trt) <- applyOpArg env tr s2 cs2 t2

    (s4, cs4, t4) <- downgradeInf
    (s5, cs5, t5) <- applyOpTy env t3 (s4 `compose` s3) (cs3 ++ cs4) t4
    (s6, cs6, t6, flt) <- applyOpArg env fl s5 cs5 t5
    let (s6', cs6', t6', flt') = degradeNormalResult (s6, cs6, t6, flt)
    return (s6', cs6', t6', IfThenElse (setPType ti t6') condt trt flt')

  Lambda ti name e -> do
    (s, cs, t, et) <- infer env e
    return (s, cs, t, Lambda (setPType ti t) name et)

  Apply ti l v -> inferBinOp env ti l v downgradeInf Apply


  ReadNN ti name e -> do
      (s, cs, _, et) <- infer env e
      -- Continuous (TFloat) NNs output (mu, sigma) logits and are treated as
      -- PNormal so that toIRNormalParams can extract the parameters symbolically.
      let pt = if rType ti == TFloat then PNormal else Integrate
      return (s, cs, pt, ReadNN (setPType ti pt) name et)


-- | The empty substitution
emptySubst :: Subst
emptySubst = mempty
-- | Compose substitutions
compose :: Subst -> Subst -> Subst
(Subst s1) `compose` (Subst s2) = Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1
class Substitutable a where
  apply :: Subst -> a -> a
  -- Free type variables
  ftv   :: a -> Set.Set TVar

instance Substitutable Program where
  apply s (Program decls nns adts enc) = Program (zip (map fst decls) (map (apply s . snd) decls)) nns adts enc
  ftv _ = Set.empty
instance Substitutable Expr where
  apply s = tMap (apply s . getTypeInfo)
  ftv _ = Set.empty
instance Substitutable TypeInfo where
  apply s ti@(TypeInfo {pType = pt}) = setPType ti (apply s pt)
  ftv _ = Set.empty
instance Substitutable PType where
  apply _ Deterministic = Deterministic
  apply _ Integrate = Integrate
  apply s (PArr p1 p2) = apply s p1 `PArr` apply s p2
  apply (Subst s) t@(TVar a) = Map.findWithDefault t a s
  apply _ t = t

  ftv (TVar a)       = Set.singleton a
  ftv (PArr p1 p2) = ftv p1 `Set.union` ftv p2
  ftv _ = Set.empty

instance Substitutable DConstraint where
   apply s (var, chain) = (apply s var, apply s chain)
   ftv (_, t2) =  ftv t2

instance Substitutable (Either PType DowngradeChain) where
   apply s (Left ty) = Left $ apply s ty
   apply s (Right dc) = Right $ apply s dc
   ftv (Left ty) = ftv ty
   ftv (Right dc) = ftv dc

instance Substitutable (Either PType ChainConstraint) where
   apply s (Left pt) = Left (apply s pt)
   apply s (Right (PlusConstraint pt1 pt2)) = Right (PlusConstraint (apply s pt1) (apply s pt2))
   apply s (Right (EnumPlusConstraint pt1 pt2)) = Right (EnumPlusConstraint (apply s pt1) (apply s pt2))
   apply s (Right (CompConstraint pt1 pt2)) = Right (CompConstraint (apply s pt1) (apply s pt2))
   ftv (Left pt) = ftv pt
   ftv (Right (PlusConstraint pt1 pt2)) = ftv pt1 `Set.union` ftv pt2
   ftv (Right (EnumPlusConstraint pt1 pt2)) = ftv pt1 `Set.union` ftv pt2
   ftv (Right (CompConstraint pt1 pt2)) = ftv pt1 `Set.union` ftv pt2

instance Substitutable a => Substitutable [a] where
  apply = map . apply
  ftv   = foldr (Set.union . ftv) Set.empty

instance Substitutable TEnv where
  apply s (TypeEnv env) = TypeEnv $ Map.map (apply s) env
  ftv (TypeEnv env) = ftv $ Map.elems env