{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SPLL.Typing.PInfer2 (
  showResults
, showResultsProg
, inferType
, makeTmpMain
, addPTypeInfo
, showResultsProgDebug
, tryAddPTypeInfo
, PTypeError (..)
) where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Debug.Trace

import Data.List (nub, delete)
import qualified Data.Set as Set

import SPLL.Typing.RInfer hiding (showResults, showResultsProg, Scheme (..), RTypeError (..))
import Data.Monoid
import Data.Either (lefts)
import Data.Foldable hiding (toList)
import qualified Data.Map as Map
import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.PType
import SPLL.Typing.RType hiding (TVar, TV)
import SPLL.Examples

data PTypeError
  = UnificationFail PType PType
  | InfiniteType TVar PType
  | UnboundVariable String
  deriving (Show)

type Var = String
type Infer = ExceptT PTypeError (State InferState)

-- Scheme: Forall [a b c] [a=b, b=c] (a->b->c)
--Forall vars con result
-- vars sind die TVars in scope in Constraint und PType. Wenn Constraint, dann resultiert in PType 
data Scheme = Forall [TVar] [Constraint] PType
  deriving (Show, Eq)
type Constraint = (Var, PType)

-- Scheme: Forall [a b c] [a=(b|c), a=(b + c)] (a->b->c)
data DScheme = DScheme [TVar] [DConstraint] PType
  deriving (Show, Eq)

type DConstraint = (PType, DowngradeChain)
data ChainConstraint = PlusConstraint TypeOrChain TypeOrChain | CompConstraint TypeOrChain TypeOrChain
  | LetInDConstraint TypeOrChain
  deriving (Show, Eq)
type DowngradeChain = [Either PType ChainConstraint]
--Downgradechain of all Left PTypes resolves into the

type TypeOrChain = Either PType DowngradeChain

resolveLetInDCons :: PType -> PType
resolveLetInDCons Deterministic = Deterministic
resolveLetInDCons _ = Bottom

resolvePlusCons :: PType -> PType -> PType
resolvePlusCons Integrate Integrate = Bottom
resolvePlusCons Integrate Prob = Bottom
resolvePlusCons Prob Integrate = Bottom
resolvePlusCons Prob Prob = Bottom
resolvePlusCons ty1 ty2 = Deterministic

resolveCompCons :: PType -> PType -> PType
resolveCompCons Integrate Integrate = Bottom
resolveCompCons Integrate Prob = Bottom
resolveCompCons Prob Integrate = Bottom
resolveCompCons Prob Prob = Bottom
resolveCompCons Prob Deterministic = Bottom
resolveCompCons Deterministic Prob = Bottom
resolveCompCons ty1 ty2 = Deterministic

showResults :: (Num a, Show a) => TypedExpr a -> IO ()
showResults expr = do
  case inferExpr mempty expr of
    Left err -> print err
    Right (cons, scheme, ee) -> do
      putStrLn $ "B:\n" ++ show cons
      putStrLn $ "Type (No Resolution, No normalize):\n" ++ show scheme
      putStrLn $ "Type (No Resolution):\n" ++ show (normalize scheme)
      putStrLn $ "Type:\n" ++ show (normalize scheme)
      putStrLn $ "Expr: "
      putStrLn $ unlines $ prettyPrint ee
      putStrLn "-----"

inferType :: (Show a) => TypedProg a -> PType
inferType prog = do
  case inferProgram mempty prog of
     Left err -> error "error in infer scheme"
     Right (_, DScheme _ b ty, _) ->  ty

addPTypeInfo :: (Show a) => Program TypeInfo a -> Program TypeInfo a
addPTypeInfo p = do
    case inferProgram mempty p of
       Left err -> error "error in addPTypeInfo"
       Right (_, _, p) ->  p

tryAddPTypeInfo :: (Show a) => Program TypeInfo a -> Either PTypeError (Program TypeInfo a)
tryAddPTypeInfo p = do
  (_,_,p2) <- inferProgram mempty p
  return p2

showResultsProgDebug :: (Num a, Show a) => TypedProg a -> IO ()
showResultsProgDebug prog = do
  case inferProgramDebug mempty prog of
    Left err -> print err
    Right (cons, scheme, p) -> do
      putStrLn $ "B:\n" ++ show cons
      putStrLn $ "Constraints (No Resolution):\n" ++ show cons
      putStrLn $ "Type:\n" ++ show scheme
      putStrLn "-----"
      putStrLn $ "Program: "
      putStrLn $ unlines $ prettyPrintProg p

showResultsProg :: (Num a, Show a) => TypedProg a -> IO ()
showResultsProg prog = do
  case inferProgram mempty prog of
    Left err -> print err
    Right (cons, scheme, p) -> do
      putStrLn $ "B:\n" ++ show cons
      putStrLn $ "Constraints (No Resolution):\n" ++ show cons
      putStrLn $ "Type:\n" ++ show scheme
      putStrLn "-----"
      putStrLn $ "Program: "
      putStrLn $ unlines $ prettyPrintProg p

newtype TEnv
  = TypeEnv {types :: Map.Map Name [Scheme]}
  deriving (Eq, Show)

instance Semigroup TEnv where
  (TypeEnv a) <> (TypeEnv b) = TypeEnv (Map.union a b)

instance Monoid TEnv where
  mempty = TypeEnv Map.empty
  mappend = (<>)

makeMain :: Expr () a -> Program () a
makeMain expr = Program [("main", expr)] (Call () "main")
-- TODO: Why does order of functions matter?
makeTmpMain :: Expr () a -> Program () a -> Program () a
makeTmpMain expr (Program decls _) = Program (decls ++ [("tmp_main", expr)]) (Call () "tmp_main")
-- | Inference state
data InferState = InferState { var_count :: Int }

-- | Initial inference state
initInfer :: InferState
initInfer = InferState { var_count = 0 }


type Unifier = (Subst, [Constraint])

-- | Constraint solver monad
type Solve a = ExceptT PTypeError Identity a

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
  dapply s (CompConstraint ty1 ty2) = CompConstraint (dapply s ty1) (dapply s ty2)


instance DSubstitutable TypeOrChain where
  dapply  (DSubst s) (Left (TVar ty)) =
    case res of
       Nothing -> Left (TVar ty)
       (Just f) -> Right f
       where res = Map.lookup ty s
  dapply  (DSubst s) (Left ty) = Left ty
  dapply s (Right dc) = Right $ dapply s dc

dcompose :: DSubst -> DSubst -> DSubst
(DSubst s1) `dcompose` (DSubst s2) = DSubst $ Map.map (dapply (DSubst s1)) s2 `Map.union` s1

substChain :: DSubst -> Either PType ChainConstraint -> [Either PType ChainConstraint]
substChain (DSubst s) (Left (TVar ty)) = Map.findWithDefault [Left (TVar ty)] ty s
substChain (DSubst s) (Left ty) = [Left ty]
substChain dsubst (Right cs)  = [Right $ dapply dsubst cs]


-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------
inferProgram:: (Show a) => TEnv -> TypedProg a -> Either PTypeError ([DConstraint], DScheme, TypedProg a)
inferProgram env = runInferProg env . inferProg env

inferProgramDebug :: (Show a) => TEnv -> TypedProg a -> Either PTypeError ([DConstraint], DScheme, TypedProg a)
inferProgramDebug env = runInferProgDebug env . inferProg env

inferExpr :: (Show a) => TEnv -> TypedExpr a -> Either PTypeError ([DConstraint], DScheme, TypedExpr a)
inferExpr env = runInfer env . infer env

runInferProgDebug :: TEnv -> Infer (Subst, [DConstraint], PType, TypedProg a) -> Either PTypeError ([DConstraint], DScheme, TypedProg a)
runInferProgDebug env m = case evalState (runExceptT m) initInfer of
  Left err  -> Left err
  Right (s, c, t, p) -> Right $ (c, DScheme [] [] t, p)

runInferProg :: TEnv -> Infer (Subst, [DConstraint], PType, TypedProg a) -> Either PTypeError ([DConstraint], DScheme, TypedProg a)
runInferProg env m = case evalState (runExceptT m) initInfer of
  Left err  -> Left err
  Right (s, c, t, p) -> Right $ closeProg env c t (apply s p)
  -- (c, DScheme [] [] t, p)
-- Right (c, (Forall [] [] t, Forall [] [] t))
--  Right $ simpleClose env c t

runInfer :: TEnv -> Infer (Subst, [DConstraint], PType, TypedExpr a) -> Either PTypeError ([DConstraint], DScheme, TypedExpr a)
runInfer env m = case evalState (runExceptT m) initInfer of
  Left err  -> Left err
  Right (_, c, t, p) -> Right $ close env c t p
-- Right (c, (Forall [] [] t, Forall [] [] t))
--  Right $ simpleClose env c t

buildConstraint ::  [DConstraint] -> [DConstraint] -> Subst -> ([DConstraint], Subst)
buildConstraint resList [] s = (resList, s)
buildConstraint resList cons s = case consElem of
  Just dcons -> buildConstraint (apply subst resList) (apply subst (delete dcons cons)) (compose s subst)
    where (_, subst, _) = isConsResolved [collapse dcons]
  Nothing -> (resList ++ cons, s)
  where consElem = find isConsResolvable cons

--TODO Cleanup dconstraint remaining
-- insert constraint chains into each other, so only the ones with direct cyclic dependencies remain
bundleConstraints :: DConstraint -> [DConstraint] -> [DConstraint]
bundleConstraints topD@(topTy, acc) dcons = case nonRecType of
  Nothing -> topD:dcons
  Just tvar -> let (tv, dc) = extractType (TVar tvar) dcons
                   dsubst = DSubst $ Map.singleton tvar dc in
               bundleConstraints (dapply dsubst topD) (dapply dsubst (delete (tv, dc) dcons))

  where (TVar topTyVar) = topTy
        dftv = delete topTyVar (Set.toList $ ftv topD)
        nonRecType = getNonRecType dftv dcons

getNonRecType :: [TVar] -> [DConstraint] -> Maybe TVar
getNonRecType [] dcons = Nothing
getNonRecType (tvar:tvar_rem) dConsList =
  if elem tvar (ftv dcons)
  then getNonRecType tvar_rem dConsList
  else Just tvar
  where dcons = extractType (TVar tvar) dConsList

isRecType ::  DConstraint -> Bool
isRecType (TVar tv, dc) = length (ftv dc) == 0 || (elem tv (ftv dc) && length (ftv dc) == 1)
isRecType (_, _) = error "non tvar variable in fixpoint iterations"

getSubstFromCons :: DConstraint -> Subst
getSubstFromCons cons = subst
  where (_, subst, _) = isConsResolved [cons]

isConsResolvable :: DConstraint -> Bool
isConsResolvable dcons =  ret
  where (cons', _, ret) = isConsResolved [collapsedCons]
        collapsedCons = collapse dcons

extractType :: PType -> [DConstraint] -> DConstraint
extractType ty [] = error "Could not find top type"
extractType ty ((pty, dc):b) = if ty == pty then (pty, dc) else extractType ty b

collapseChain :: DowngradeChain -> PType -> DowngradeChain -> DowngradeChain
collapseChain [] ty dcOut = [Left ty] ++ dcOut
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
collapseChain ((Right (CompConstraint ty1 ty2)):b) ty3 dcOut =
    if isResolved
    then collapseChain b (downgrade (resolveCompCons rty1 rty2) ty3) dcOut
    else collapseChain b ty3 dcOut ++ [Right (CompConstraint (subCollapse ty1) (subCollapse ty2))]
    where (b1, rty1) = getResType ty1
          (b2, rty2) = getResType ty2
          isResolved = b1 && b2
collapseChain ((Right (LetInDConstraint (Left Deterministic))):b) ty3 dcOut = collapseChain b ty3 dcOut
collapseChain ((Right (LetInDConstraint ty1)):b) ty3 dcOut = if isResolved
   then collapseChain b (downgrade (resolveLetInDCons rty1) ty3) dcOut
   else collapseChain b ty3 dcOut ++ [Right (LetInDConstraint (subCollapse ty1))]
   where (isResolved, rty1) = getResType ty1

subCollapse :: TypeOrChain -> TypeOrChain
subCollapse (Left ty) = Left  ty
subCollapse (Right dc) = Right $ collapseChain dc Deterministic []


getResType :: TypeOrChain -> (Bool, PType)
getResType (Left ty) = if isBasicType ty then (True, ty) else (False, Bottom)
getResType (Right dc) = if length nestedCollapse == 1 && length (lefts nestedCollapse) == 1
  then (True, head (lefts nestedCollapse)) else (False, Bottom)
  where nestedCollapse = collapseChain dc Deterministic []

collapse :: DConstraint -> DConstraint
collapse (ty, dc) = (ty, collapseChain dc Deterministic [])

isConsResolved :: [DConstraint] -> ([DConstraint], Subst, Bool)
isConsResolved [(TVar a, [Left ty])] | isBasicType ty = ([], Subst $ Map.singleton a ty, True)
--isConsResolved [(ty1, [Left ty2])] | isBasicType ty1 && ty1 == ty2 = ([], emptySubst, True)
--isConsResolved [(ty1, [Left ty2])] | isBasicType ty1 && ty1 /= ty2 = error "false constraint pinfer"
isConsResolved cons = (cons, emptySubst, False)

resolveStep ::  [DConstraint] -> PType -> ([DConstraint], PType, Bool, Subst)
resolveStep [] ty = ([], ty, True, emptySubst)
resolveStep cons ty = (consRes, resType, isResolvedRes, substRes)
  where --topCons = extractType ty cons
        --consNoTop = delete topCons cons
        (cons', subst1) = buildConstraint [] cons emptySubst

        topConsB =  extractType ty cons'
        consNoTopB = delete topConsB cons'
        consBundles = map collapse $ bundleConstraints topConsB consNoTopB
        
        noCycleType = apply subst1  ty
        (consRes, resType, isResolvedRes, substRes) =
          if null cons'
          then ([], apply subst1 ty, True, subst1)
          else (consBundles, noCycleType, False, subst1)



fixpointIteration :: DConstraint -> Subst
fixpointIteration dcons@(TVar tv, dc) = compose (Subst $ Map.singleton tv ty) substRes
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
    solveCyclicConstraints (apply fixSubst (delete d dcons))(apply fixSubst pty)(compose s fixSubst)
  where nextCons = find isRecType dcons

close :: TEnv -> [DConstraint] -> PType -> TypedExpr a -> ([DConstraint], DScheme, TypedExpr a)
close env cons ty tex = (cons', DScheme alph consRes  resType', tex)
  where alph = Set.toList $ Set.difference (Set.union (ftv cons') (ftv resType)) (ftv env)
        (cons', resType, isResolved, _) = resolveStep cons ty
        (consRes, resType', _) = if isResolved then (cons', resType, emptySubst) else
                   solveCyclicConstraints cons' resType emptySubst
closeProg :: TEnv -> [DConstraint] -> PType -> TypedProg a -> ([DConstraint], DScheme, TypedProg a )
closeProg env cons ty tp = (cons', DScheme alph consRes  resType', apply finalSubst tp)
  where alph = Set.toList $ Set.difference (Set.union (ftv cons') (ftv resType)) (ftv env)
        (cons', resType, isResolved, su) = resolveStep cons ty
        (consRes, resType', su2) = if isResolved then (cons', resType, emptySubst) else
                   solveCyclicConstraints cons' resType emptySubst
        -- after cyclic constraints are resolved we needs subst to fill missing ptypes in expr tree
        (_, _, _, su3) = if isResolved then (cons', resType, isResolved, emptySubst) else resolveStep (apply su2 cons) resType
        finalSubst = su `compose` (su2 `compose` su3)

extend :: TEnv -> (Var, Scheme) -> TEnv
extend (TypeEnv env) (x, s) = TypeEnv $ Map.insertWith (++) x [s] env

unify ::  PType -> PType -> Infer Subst
unify a b | a == b = return emptySubst
unify (l `PArr` r) (l' `PArr` r')  = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  return (s2 `compose` s1)
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify t1 t2 = throwError $ UnificationFail t1 t2

bind ::  TVar -> PType -> Infer Subst
bind a t
  | t == TVar a     = return emptySubst
  | occursCheck t a = throwError $ InfiniteType a t
  | otherwise       = return $ Subst $ Map.singleton a t

occursCheck ::  Substitutable a => a -> TVar ->  Bool
occursCheck t a =  a `Set.member` ftv t

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer PType
fresh = do
    s <- get
    put s{var_count = var_count s + 1}
    return $ TVar $ TV (letters !! var_count s)

-- TODO: Other Constraints?
instantiate :: Scheme -> Infer ([Constraint], PType)
instantiate (Forall as cs t) = do
  as' <- mapM (const fresh) as
  let s = Subst $ Map.fromList $ zip as as'
  return ([],apply s t)

generalize :: TEnv -> PType -> Scheme
generalize env t  = Forall as [] t
    where as = Set.toList $ ftv t `Set.difference` ftv env

-- infer an argument of a binary operator expression and build constraint + subst accordingly
applyOpArg :: (Show a) => TEnv -> Expr TypeInfo a -> Subst -> [DConstraint] -> PType -> Infer (Subst, [DConstraint], PType, Expr TypeInfo a)
applyOpArg env expr s1 cs1 t1 = do
  (s2, cs2, t2, exprt) <- infer (apply s1 env) expr
  tv1 <- fresh
  s3       <- unify (apply s2 t1) (PArr t2 tv1)
  return (s3 `compose` s2 `compose` s1,
    apply (s3 `compose` s2) cs1 ++ apply s3 cs2,
    apply s3 tv1,
    exprt)

-- if we already know the type of the first argument in a binary operator..
applyOpTy :: TEnv -> PType -> Subst -> [DConstraint] -> PType -> Infer (Subst, [DConstraint], PType)
applyOpTy env ty s1 cs1 t1 = do
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

rtFromScheme :: Scheme -> PType
rtFromScheme (Forall _ _ rt) = rt

fst3 :: (Subst, [DConstraint], PType, TypedExpr a ) -> Subst
fst3 (x, _, _, _) = x
snd3 :: (Subst, [DConstraint], PType, TypedExpr a ) -> [DConstraint]
snd3 (_, x, _, _) = x
trd3 :: (Subst, [DConstraint], PType, TypedExpr a ) -> PType
trd3 (_, _, x, _) = x
frth3 :: (Subst, [DConstraint], PType, TypedExpr a ) ->  TypedExpr a
frth3 (_, _, _, x) = x

lookupEnv :: TEnv -> Var -> Infer (Subst, [DConstraint], PType)
lookupEnv (TypeEnv env) x =
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable (show x)
    Just [s] -> do (cs, t) <- instantiate s
                   return (emptySubst, [], t)
    Just _ -> error "unresolved function call"

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

inferProg :: (Show a) => TEnv -> TypedProg a -> Infer (Subst, [DConstraint], PType, TypedProg a)
inferProg env (Program decls expr) = do
  -- init type variable for all function decls beforehand so we can build constraints for
  -- calls between these functions
  tv_rev <- freshVars (length decls) []
  let tvs = reverse tv_rev
  -- env building with (name, scheme) for infer methods
  let func_tvs = zip (map fst decls) (map (Forall [] []) tvs)
  let fenv = foldl extend env func_tvs
  -- infer the type and constraints of the declaration expressions
  cts <- mapM (infer fenv . snd) decls
  -- inferring the type of the top level expression
  (s1, cs1, t1, pt) <- infer fenv expr
  -- building the constraints that the built type variables of the functions equal
  -- the inferred function type
  let tcs = zipWith makeEqConstraint tvs (map trd3 cts)
  -- combine all constraints
  return (s1, cs1 ++ concatMap snd3 cts ++ tcs , t1, Program (zip (map fst decls) (map frth3 cts)) pt)

infer :: (Show a) => TEnv -> Expr TypeInfo a -> Infer (Subst, [DConstraint], PType, Expr TypeInfo a)
infer env expr = case expr of

  ThetaI ti a  -> return (emptySubst, [], Deterministic, ThetaI (setPType ti Deterministic) a)
  Uniform ti  -> return (emptySubst, [], Integrate, Uniform (setPType ti Integrate))
  Normal ti  -> return (emptySubst, [], Integrate, Normal (setPType ti Integrate))
  Constant ti val  -> return (emptySubst, [], Deterministic, Constant (setPType ti Deterministic) val)
  -- Assuming unbound variables are caught in RInfer (laziness tbh)
  Var ti s -> return (emptySubst, [], Deterministic, Var (setPType ti Deterministic) s)
  LetIn ti s x b -> do
    (s1, cs1, t1, xt) <- infer env x
    (s2, cs2, t2, bt) <- infer env b
    return (compose s2 s1, apply s2 cs1 ++ cs2, t2, LetIn (setPType ti t2) s xt bt)

  InjF ti name paramsExpr expr -> do
    (s1, cs1, t1, xt) <- infer env expr
    p_inf <- mapM (infer env) paramsExpr
    tv <- fresh
    let s_acc = foldl compose emptySubst (map fst3 p_inf)
    let cts_d d = Right (LetInDConstraint(Left d))
    let p_fst = map (cts_d . trd3) p_inf
    return (compose s1 s_acc, cs1 ++ concatMap snd3 p_inf ++ [(tv,Left t1:p_fst)]
      , tv, InjF (setPType ti tv) name (map frth3 p_inf) xt)

  PlusF ti e1 e2 -> do
    (s1, cs1, t1) <- plusInf
    (s2, cs2, t2, et1) <- applyOpArg env e1 s1 cs1 t1
    (s3, cs3, t3, et2) <- applyOpArg env e2 s2 cs2 t2
    return (s3, cs3, t3, PlusF (setPType ti t3) et1 et2)

  PlusI ti e1 e2 -> do
    (s1, cs1, t1) <- plusInf
    (s2, cs2, t2, et1) <- applyOpArg env e1 s1 cs1 t1
    (s3, cs3, t3, et2) <- applyOpArg env e2 s2 cs2 t2
    return (s3, cs3, t3, PlusI (setPType ti t3) et1 et2)

  MultF ti e1 e2 -> do
      (s1, cs1, t1) <- plusInf
      (s2, cs2, t2, et1) <- applyOpArg env e1 s1 cs1 t1
      (s3, cs3, t3, et2) <- applyOpArg env e2 s2 cs2 t2
      return (s3, cs3, t3, MultF (setPType ti t3) et1 et2)

  MultI ti e1 e2 -> do
      (s1, cs1, t1) <- plusInf
      (s2, cs2, t2, et1) <- applyOpArg env e1 s1 cs1 t1
      (s3, cs3, t3, et2) <- applyOpArg env e2 s2 cs2 t2
      return (s3, cs3, t3, MultI (setPType ti t3) et1 et2)
      
  NegF ti e -> do
      (s1, cs1, t1) <- negInf
      (s2, cs2, t2, et) <- applyOpArg env e s1 cs1 t1
      return (s2, cs2, t2, NegF (setPType ti t2) et)

  GreaterThan ti e1 e2 -> do
      (s1, cs1, t1) <- compInf
      (s2, cs2, t2, et1) <- applyOpArg env e1 s1 cs1 t1
      (s3, cs3, t3, et2) <- applyOpArg env e2 s2 cs2 t2
      return (s3, cs3, t3, GreaterThan (setPType ti t3) et1 et2)

  Call ti name -> do
      (s1, cs, t1) <- lookupEnv env name
      return (s1, cs, t1, Call (setPType ti t1) name)

  Null ti -> return (emptySubst, [], Deterministic, Null (setPType ti Deterministic))

  Cons ti e1 e2 -> do
    (s1, cs1, t1) <- downgradeInf
    (s2, cs2, t2, et1) <- applyOpArg env e1 s1 cs1 t1
    (s3, cs3, t3, et2) <- applyOpArg env e2 s2 cs2 t2
    return (s3, cs3, t3, Cons (setPType ti t3) et1 et2)

  TCons ti e1 e2 -> do
    (s1, cs1, t1) <- downgradeInf
    (s2, cs2, t2, et1) <- applyOpArg env e1 s1 cs1 t1
    (s3, cs3, t3, et2) <- applyOpArg env e2 s2 cs2 t2
    return (s3, cs3, t3, TCons (setPType ti t3) et1 et2)

  IfThenElse ti cond tr fl -> do
    (s1, cs1, t1) <- downgradeInf
    (s2, cs2, t2, condt) <- applyOpArg env cond s1 cs1 t1
    (s3, cs3, t3, trt) <- applyOpArg env tr s2 cs2 t2

    (s4, cs4, t4) <- downgradeInf
    (s5, cs5, t5) <- applyOpTy env t3 (s4 `compose` s3) (cs3 ++ cs4) t4
    (s6, cs6, t6, flt) <- applyOpArg env fl s5 cs5 t5
    return (s6, cs6, t6, IfThenElse (setPType ti t6) condt trt flt)
  
  Lambda ti name expr -> do
    undefined
  
  _ -> error (show expr)
       

normalize :: DScheme -> DScheme
normalize (DScheme _ c body) = DScheme (map snd ord) (normcs c) (normtype body)
  where
    ord = zip (nub $ concatMap fvcs c ++ fv body ) (map TV letters)

    fv (TVar a)   = [a]
    fv (PArr a b) = fv a ++ fv b
    fv Deterministic = []
    fv Integrate = []
    fv Bottom = []

    fvcs (ty, dc) = fv ty ++ fvcd dc

    fvOr (Left ty) = fv ty
    fvOr (Right cd) = fvcd cd
    fvcd ((Left ty):b) = fv ty ++ fvcd b
    fvcd (Right(PlusConstraint ty1 ty2):b) = fvOr ty1 ++ fvOr ty2 ++ fvcd b
    fvcd (Right(CompConstraint ty1 ty2):b) = fvOr ty1 ++ fvOr ty2 ++ fvcd b
    fvcd [] = []

    normcs ((ty, dc): b) = (normtype ty, normdc dc):normcs b
    normcs [] = []

    normdc ((Left ty):b) =  Left (normtype ty): normdc b
    normdc (Right(PlusConstraint ty1 ty2):b) = Right(PlusConstraint (normOr ty1) (normOr ty2)): normdc b
    normdc (Right(CompConstraint ty1 ty2):b) = Right(CompConstraint (normOr ty1) (normOr ty2)): normdc b
    normdc [] = []

    normOr (Left ty) = Left $ normtype ty
    normOr (Right dc) = Right $ normdc dc

    normtype (PArr a b) = PArr (normtype a) (normtype b)
    normtype Deterministic = Deterministic
    normtype Integrate = Integrate
    normtype Bottom = Bottom

    normtype (TVar a)   =
      case Prelude.lookup a ord of
        Just x -> TVar x
        Nothing -> error "type variable not in signature"


-- | The empty substitution
emptySubst :: Subst
emptySubst = mempty
emptyDSubst :: DSubst
emptyDSubst = mempty
-- | Compose substitutions
compose :: Subst -> Subst -> Subst
(Subst s1) `compose` (Subst s2) = Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1
class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance Substitutable (Program TypeInfo a) where
  apply s (Program decls expr) = Program (zip (map fst decls) (map (apply s . snd) decls)) (apply s expr)
  ftv _ = Set.empty
instance Substitutable (Expr TypeInfo a) where
  apply s = tMap (apply s . getTypeInfo)
  ftv _ = Set.empty
instance Substitutable TypeInfo where
  apply s (TypeInfo rt pt) = TypeInfo rt (apply s pt)
  ftv _ = Set.empty
instance Substitutable PType where
  apply _ Deterministic = Deterministic
  apply _ Integrate = Integrate
  apply s (PArr p1 p2) = apply s p1 `PArr` apply s p2
  apply (Subst s) t@(TVar a) = Map.findWithDefault t a s
  -- rest of PType arent used as of now
  apply _ t = t

  ftv (TVar a)       = Set.singleton a
  ftv (PArr p1 p2) = ftv p1 `Set.union` ftv p2
  ftv _ = Set.empty

instance Substitutable Scheme where
  apply (Subst s) (Forall as c t)   = Forall as c $ apply s' t
                            where s' = Subst $ foldr Map.delete s as
  ftv (Forall as _ t) = ftv t `Set.difference` Set.fromList as

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
   apply s (Right (CompConstraint pt1 pt2)) = Right (CompConstraint (apply s pt1) (apply s pt2))
   apply s (Right (LetInDConstraint pt1)) = Right (LetInDConstraint (apply s pt1))
   ftv (Left pt) = ftv pt
   ftv (Right (PlusConstraint pt1 pt2)) = ftv pt1 `Set.union` ftv pt2
   ftv (Right (CompConstraint pt1 pt2)) = ftv pt1 `Set.union` ftv pt2
   ftv (Right (LetInDConstraint pt1)) = ftv pt1

instance Substitutable Constraint where
   apply s (v, t1) = (v, apply s t1)
   ftv (_, t2) =  ftv t2

instance Substitutable a => Substitutable [a] where
  apply = map . apply
  ftv   = foldr (Set.union . ftv) Set.empty

instance Substitutable TEnv where
  apply s (TypeEnv env) = TypeEnv $ Map.map (apply s) env
  ftv (TypeEnv env) = ftv $ Map.elems env