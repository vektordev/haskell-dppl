
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SPLL.Typing.RInfer (
  RTypeError (..)
, addRTypeInfo
, tryAddRTypeInfo
, testFunction
) where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity

import Data.List (nub)
import qualified Data.Set as Set

import Data.Monoid
import Data.Foldable hiding (toList)
import qualified Data.Map as Map

import Text.Pretty.Simple

import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
--import SPLL.Typing.PType( PType(..) )
import SPLL.InferenceRule
import PredefinedFunctions (globalFenv, FPair(..), FDecl(..))
import Debug.Trace
import SPLL.Lang.Types (FnDecl)

-- changes: in infer and inferProg; also changed TypeSigs to remove RType of main expression.

-- unchanged:
data TEnv = TypeEnv { types :: Map.Map Name Scheme }
  deriving (Eq, Show)

empty :: TEnv
empty = TypeEnv Map.empty

extend :: TEnv -> (Name, Scheme) -> TEnv
extend env (x, s) = env { types = Map.insert x s (types env) }

remove :: TEnv -> Name -> TEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

extends :: TEnv -> [(Name, Scheme)] -> TEnv
extends env xs = env { types = Map.union (Map.fromList xs) (types env) }

lookupE :: Name -> TEnv -> Maybe Scheme
lookupE key (TypeEnv tys) = Map.lookup key tys

merge :: TEnv -> TEnv -> TEnv
merge (TypeEnv a) (TypeEnv b) = TypeEnv (Map.union a b)

mergeTEnvs :: [TEnv] -> TEnv
mergeTEnvs = foldl' merge empty

singleton :: Name -> Scheme -> TEnv
singleton x y = TypeEnv (Map.singleton x y)

keys :: TEnv -> [Name]
keys (TypeEnv env) = Map.keys env

fromList :: [(Name, Scheme)] -> TEnv
fromList xs = TypeEnv (Map.fromList xs)

toList :: TEnv -> [(Name, Scheme)]
toList (TypeEnv env) = Map.toList env

instance Semigroup TEnv where
  (<>) = merge

instance Monoid TEnv where
  mempty = empty
  mappend = (<>)

data RTypeError
  = UnificationFail RType RType
  | InfiniteType TVarR RType
  | UnboundVariable String
  | Ambigious [Constraint]
  | UnificationMismatch [RType] [RType]
  | ExprInfo [String]
  | FalseParameterFail String
  deriving (Show, Eq)

-- | Inference monad
type Infer a = (ReaderT
                  TEnv             -- Typing TEnvironment
                  (StateT         -- Inference state
                  InferState
                  (Except         -- Inference errors
                    RTypeError))
                  a)              -- Result

-- | Inference state
data InferState = InferState { var_count :: Int }

-- | Initial inference state
initInfer :: InferState
initInfer = InferState { var_count = 0 }

type Constraint = (RType, RType)

type Unifier = (Subst, [Constraint])

-- | Constraint solver monad
type Solve a = ExceptT RTypeError Identity a

newtype Subst = Subst (Map.Map TVarR RType)
  deriving (Eq, Show, Monoid, Semigroup)

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVarR

instance Substitutable Program where
  apply s (Program decls nns) = Program (zip (map fst decls) (map (apply s . snd) decls)) nns
  ftv _ = Set.empty

instance Substitutable Expr where
  apply s = tMap (apply s . getTypeInfo)
  ftv _ = Set.empty

instance Substitutable TypeInfo where
  apply s ti@(TypeInfo {rType=rt}) = setRType ti (apply s rt)
  ftv _ = Set.empty

instance Substitutable RType where
  apply _ TBool = TBool
  apply _ TInt = TInt
  apply _ TSymbol = TSymbol
  apply _ TFloat = TFloat
  apply _ NullList = NullList
  apply _ BottomTuple = BottomTuple
  apply _ TThetaTree = TThetaTree
  apply s (ListOf t) = ListOf $ apply s t
  apply s (Tuple t1 t2) = Tuple (apply s t1) (apply s t2)
  apply s (TEither t1 t2) = TEither (apply s t1) (apply s t2)
  apply s (TArrow t1 t2) = apply s t1 `TArrow` apply s t2
  apply (Subst s) t@(TVarR a) = Map.findWithDefault t a s
  apply s (GreaterType t1 t2) = apply s t1 `GreaterType` apply s t2
  -- rest of RType arent used as of now
  apply _ val = error ("Missing Substitute: " ++ show val)

  ftv (ListOf t) = ftv t
  ftv (Tuple t1 t2) = Set.union (ftv t1) (ftv t2)
  ftv (TEither t1 t2) = Set.union (ftv t1) (ftv t2)
  ftv (TVarR a)       = Set.singleton a
  ftv (t1 `TArrow` t2) = ftv t1 `Set.union` ftv t2
  ftv (t1 `GreaterType` t2) = ftv t1 `Set.union` ftv t2
  ftv _ = Set.empty

instance Substitutable Scheme where
  apply (Subst s) (Forall as t)   = Forall as $ apply s' t
                            where s' = Subst $ foldr Map.delete s as
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

instance Substitutable Constraint where
   apply s (t1, t2) = (apply s t1, apply s t2)
   ftv (t1, t2) = ftv t1 `Set.union` ftv t2

instance Substitutable a => Substitutable [a] where
  apply = map . apply
  ftv   = foldr (Set.union . ftv) Set.empty

instance Substitutable TEnv where
  apply s (TypeEnv env) = TypeEnv $ Map.map (apply s) env
  ftv (TypeEnv env) = ftv $ Map.elems env

showConstraint :: Constraint -> String
showConstraint (a, b) = prettyRType a ++ " :==: " ++ prettyRType b

--build the basic type environment: Take all invertible functions; ignore their inverses
basicTEnv :: TEnv
basicTEnv = TypeEnv $ Map.fromList $ map (\(name, FPair FDecl {contract=ty} _) -> (name, ty)) globalFenv
  where
    -- plain RTypes as they exist in globalFEnv are implicitly forall'd. Make it explicit.
    toScheme :: RType -> Scheme
    toScheme rty = Forall freeVars rty
      where
        freeVars :: [TVarR]
        freeVars = Set.toList $ ftv rty

addRTypeInfo :: Program -> Program
addRTypeInfo p =
  case runInfer basicTEnv (inferProg p) of
    Left err -> error ("error in addRTypeInfo: " ++ show err)
    Right (cs, p2) -> case runSolve cs of
      Left err -> error (
        "error in solve addRTypeInfo: " ++ show err
        ++ "\n\nprog = \n" ++ (unlines $ prettyPrintProgRTyOnly p2)
        ++ "\n\nconstraints = \n" ++ (unlines $ map showConstraint cs)
        ++ "\n\nsimplified prog = \n" ++ (unlines $ prettyPrintProgRTyOnly (subst `apply` p2))
        ++ "\n\nleftover constraints = \n" ++ (unlines $ map showConstraint leftoverConstraints))
          where
            (subst, leftoverConstraints) = simplify (emptySubst, cs)
      Right subst -> apply subst p2

tryAddRTypeInfo :: Program -> Either RTypeError Program
tryAddRTypeInfo p@(Program decls _) = do
  (cs, p) <- runInfer basicTEnv (inferProg p)
  subst <- runSolve cs
  return $ apply subst p

--TODO Remove
testFunction :: Program -> IO ()
testFunction p@(Program decls _) = do
  let res2 = runExcept $ evalStateT (runReaderT (testInferProg p) empty) initInfer
  pPrint res2

testInferProg :: Program -> Infer ([Constraint], Program)
testInferProg p = do
  Program decls nns <- addTVarsEverywhere p
  -- init type variable for all function decls beforehand so we can build constraints for
  -- calls between these functions
  tv_rev <- trace ("\n decl:\n" ++ show decls ++ "\n\n") freshVars (length decls) []
  let tvs = reverse tv_rev
  -- env building with (name, scheme) for infer methods
  let func_tvs = zip (map fst decls) (map (Forall []) tvs)
  -- infer the type and constraints of the declaration expressions
  cts <- trace ("func_tvs:" ++ show func_tvs) $ mapM ((inTEnvF func_tvs . infer) . snd) decls
  -- building the constraints that the built type variables of the functions equal
  -- the inferred function type
  let tcs = zip (map (rtFromScheme . snd) func_tvs) (map fst3cts cts)
  -- combine all constraints
  return (tcs ++ concatMap snd3cts cts, Program (zip (map fst decls) (map trd3cts cts)) nns)

--unchanged up to here.


rtFromScheme :: Scheme -> RType
rtFromScheme (Forall _ rt) = rt

--TODO: Simply give everything a fresh var as a unified first pass.
inferProg :: Program -> Infer ([Constraint], Program)
inferProg p = do
  Program decls nns <- addTVarsEverywhere p

  -- init type variable for all function decls beforehand so we can build constraints for
  -- calls between these functions
  tv_rev <- freshVars (length decls) []
  let tvs = reverse tv_rev
  -- env building with (name, scheme) for infer methods
  let func_tvs = zip (map fst decls) (map (Forall []) tvs)
  -- infer the type and constraints of the declaration expressions
  cts <- mapM ((inTEnvF func_tvs . infer) . snd) decls
  -- building the constraints that the built type variables of the functions equal
  -- the inferred function type
  let tcs = zip (map (rtFromScheme . snd) func_tvs) (map fst3cts cts)
  -- combine all constraints
  return (tcs ++ concatMap snd3cts cts, Program (zip (map fst decls) (map trd3cts cts)) nns)

addTVarsEverywhere :: Program -> Infer Program
addTVarsEverywhere (Program decls nns) = do
    newdecls <- mapM addTVarsToDecl decls
    return (Program newdecls nns)
  where
    addTVarsToDecl :: FnDecl -> Infer FnDecl
    addTVarsToDecl (name, expr) = do
      e2 <- tMapM replaceIfUnset expr
      return (name, e2)
    replaceIfUnset :: Expr -> Infer TypeInfo
    replaceIfUnset expr = case rType $ getTypeInfo expr  of
      NotSetYet -> do
        tvar <- fresh
        return $ setRType (getTypeInfo expr) tvar
      _ -> return $ getTypeInfo expr

specialTreatment :: Expr -> Bool
specialTreatment e = toStub e `elem` [StubConstant, StubLambda, StubVar, StubApply, StubInjF]

--TODO: Error on ambiguous InferenceRule
infer :: Expr -> Infer (RType, [Constraint], Expr)
--infer expr | trace (show expr ++ show (specialTreatment expr) ++ show (solvesSimply expr)) False = undefined
infer expr
    | specialTreatment expr =
      --we're dealing with StubConstant here.
      case expr of
        (Constant ty val) -> do
          let tVal = getRType val
          let constraint = (rType ty, tVal)
          return (rType ty, [constraint], expr)
        (Lambda ti name inExpr) -> do
          -- rare case of needing an extra TV, because the var doesn't get one initially
          tv <- fresh
          -- give the lambda var a tv, with that TEnv infer the lambda expression
          (functionTy, cs, inExprTy) <- inTEnvF [(name, Forall [] tv)] (infer inExpr)
          -- resulting type is tv -> functionTy; propagate constraints from inner Expr.
          return (tv `TArrow` functionTy, cs, Lambda (setRType ti (tv `TArrow` functionTy)) name inExprTy)
        (Var ti name) -> do
          t <- lookupTEnv name
          return (t, [], Var (setRType ti t) name)
        e@(Apply ti func arg) -> do
          (funcTy, c1, funcExprTy) <- infer func
          (argTy, c2, argExprTy) <- infer arg
          let argConstraint = (funcTy, argTy `TArrow` (rType ti))
          return (rType ti, [argConstraint] ++ c1 ++ c2, Apply ti funcExprTy argExprTy)
          --expr `usingScheme` (Forall [TV "a", TV "b"] (((TVarR $ TV "a") `TArrow` (TVarR $ TV "b")) `TArrow` (TVarR $ TV "a") `TArrow` (TVarR $ TV "b")))
        e@(InjF ti name params) -> do
          let Just (FPair FDecl {contract=scheme} _) = lookup name globalFenv
          e `usingScheme` scheme
    | solvesSimply expr =
        let
          plausibleAlgs = filter (checkExprMatches expr) allAlgorithms
          --since we don't care about ambiguous inference rules (i.e. multiple plausible rules)
          -- we just make sure that they agree on resulting types.
          allSchemesEq = all (\alg -> assumedRType (head plausibleAlgs) == assumedRType alg) (tail plausibleAlgs)
          scheme = assumedRType (head plausibleAlgs)
        in
          if not allSchemesEq
            then error ("unviable Inference Rule configuration" ++ (show $ map algName plausibleAlgs))
            else
              -- use ForAll scheme from InferenceRule.
              expr `usingScheme` scheme
    | otherwise = error ("no inference implemented for " ++ show expr)

usingScheme :: Expr -> Scheme -> Infer (RType, [Constraint], Expr)
usingScheme expr scheme = do
  -- use ForAll scheme from InferenceRule.
  let subexprs = getSubExprs expr
  tuples <- mapM infer subexprs
  let localConstraints = concatMap snd3cts tuples
  let subExprTypes = map fst3cts tuples
  let typedSubExprs = map trd3cts tuples
  rescoped <- rescope scheme
  (resultingtype, recursiveConstraints) <- inferResultingType rescoped subExprTypes
  return (resultingtype, recursiveConstraints ++ localConstraints, reformExpr expr typedSubExprs resultingtype)

solvesSimply :: Expr -> Bool
solvesSimply e = (not (null plausibleAlgs)) && (not ((toStub e) == StubConstant))
  where
    plausibleAlgs = filter (checkExprMatches e) allAlgorithms

--put all new TVars into a scheme
--TODO: could probably be reduced to instantiate, depending on context.
rescope :: Scheme -> Infer Scheme
rescope (Forall tvars rty) = do
  newTVars <- mapM (const fresh) tvars
  let newvars = map unwrap newTVars
  let substitution = Subst $ Map.fromList (zip tvars newTVars)
  let substituted = apply substitution rty
  return (Forall newvars substituted)
    where unwrap (TVarR tv) = tv

-- instantiate a Scheme: Substitute each ForAll'd TV with a fresh var.
instantiate :: Scheme -> Infer RType
instantiate (Forall as t) = do
    as2 <- mapM (const fresh) as
    let s = Subst $ Map.fromList $ zip as as2
    return $ apply s t

-- into an existing expression, replace a subexpresison and rtype.
reformExpr :: Expr -> [Expr] -> RType -> Expr
reformExpr original subexprs ownTy = tMapHead (const newTy) $ setSubExprs original subexprs
  where
    newTy = setRType (getTypeInfo original) ownTy

--take a scheme like Forall [a,b,c] (a -> b -> c) and apply a list of types Int, Float to the scheme.
-- should yield (c, [a=Int, b=Float])
inferResultingType :: Scheme -> [RType] -> Infer (RType, [Constraint])
inferResultingType (Forall vars rtype) [] = return (rtype, [])
inferResultingType (Forall vars (TArrow fromTy toTy)) (fstTy:rtypes2) =
  do
    let constraint = (fromTy, fstTy)
    (resultingType, moreConstraints) <- inferResultingType (Forall vars toTy) rtypes2
    return (resultingType, constraint:moreConstraints)
inferResultingType (Forall vars fTy) (fstTy:rtypes2) = do
  --introduce a new TV for the result.
  resultingTV <- fresh
  let constraint = (fTy, fstTy `TArrow` (resultingTV))
  (resultingType, moreConstraints) <- inferResultingType (Forall vars resultingTV) rtypes2
  return (resultingType, constraint:moreConstraints)
--inferResultingType a b = error ("undefined inferResulting from " ++ show a ++ " //// " ++ show b)


-- | Extend type TEnvironment
inTEnvF :: [(Name, Scheme)] -> Infer a -> Infer a
inTEnvF [] m = m
inTEnvF ((x, sc): []) m = do
  let scope e = remove e x `extend` (x, sc)
  local scope m
inTEnvF ((x, sc): r) m = do
  let scope e = remove e x `extend` (x, sc)
  inTEnvF r (local scope m)

-- | Lookup type in the TEnvironment
lookupTEnv :: Name -> Infer RType
lookupTEnv x = do
  (TypeEnv env) <- ask
  case Map.lookup x env of
      Nothing   ->  throwError $ UnboundVariable x
      Just s    ->  do t <- instantiate s
                       return t

fst3cts ::  (RType, [Constraint], Expr) -> RType
fst3cts (t, _, _) = t
snd3cts ::  (RType, [Constraint], Expr) -> [Constraint]
snd3cts (_, cts, _) = cts
trd3cts ::  (RType, [Constraint], Expr) -> Expr
trd3cts (_, _, e) = e

-------------------------------------------------------------------------------
-- Type Variable management
-------------------------------------------------------------------------------
letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer RType
fresh = do
    s <- get
    put s{var_count = var_count s + 1}
    return $ TVarR $ TV (letters !! var_count s)

freshVars :: Int -> [RType] -> Infer [RType]
freshVars 0 rts = do
    return rts
freshVars n rts = do
    s <- get
    put s{var_count = var_count s + 1}
    freshVars (n - 1)  (TVarR (TV (letters !! var_count s)):rts)


-- | Run the inference monad
runInfer :: TEnv -> Infer ([Constraint], Program) -> Either RTypeError ([Constraint], Program)
runInfer env m = runExcept $ evalStateT (runReaderT m env) initInfer


-------------------------------------------------------------------------------
-- Constraint Solver
-------------------------------------------------------------------------------

-- | The empty substitution
emptySubst :: Subst
emptySubst = mempty

-- | Compose substitutions
compose :: Subst -> Subst -> Subst
(Subst s1) `compose` (Subst s2) = Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1

-- | Run the constraint solver
runSolve :: [Constraint] -> Either RTypeError Subst
runSolve cs = runIdentity $ runExceptT $ solver st
  where st = (emptySubst, cs)

-- same logic as a constraint solver,
-- except it skips but records all failing constraints
-- and produces a somewhat-informative substitution
simplify :: Unifier -> Unifier
simplify (su, []) = (su, [])
simplify (su, ((t1, t2): cs0)) =
  case runIdentity $ runExceptT $ unifies t1 t2 of
    -- can't simplify the t1, t2 constraint, put it in the unusable bin.
    Left err -> addLeftoverConstraint (simplify (su, cs0)) (t1, t2)
    Right newSubst -> simplify (newSubst `compose` su, apply newSubst cs0)
  where
    addLeftoverConstraint :: Unifier -> Constraint -> Unifier
    addLeftoverConstraint (su, cs) cs2 = (su, cs2:cs)

-- Unification solver
solver :: Unifier -> Solve Subst
solver (su, cs) =
  case cs of
    [] -> return su
    ((t1, t2): cs0) -> do
      su1  <- unifies t1 t2
      solver (su1 `compose` su, apply su1 cs0)

unifies :: RType -> RType -> Solve Subst
unifies t1 t2 | t1 `matches` t2 = return emptySubst
unifies (Tuple t1 t2) BottomTuple = return emptySubst
unifies BottomTuple (Tuple t1 t2) = return emptySubst
unifies (ListOf t) NullList = return emptySubst
unifies NullList (ListOf t) = return emptySubst
unifies (ListOf t1) (ListOf t2) = unifies t1 t2
unifies t1 (GreaterType (TVarR v) t3) = if t1 `matches` t3 then v `bind` t1 else
  throwError $ UnificationFail t1 t3
unifies t1 (GreaterType t3 (TVarR v)) = if t1 `matches` t3 then v `bind` t1 else
  throwError $ UnificationFail t1 t3
unifies (TVarR v) (GreaterType t2 t3) = case greaterType t2 t3 of
  Nothing -> throwError $ UnificationFail t2 t3
  Just t -> v `bind` t
unifies t1 (GreaterType t2 t3) = if t1 `matches` t2 && t2 `matches` t3 then return emptySubst else
  (case greaterType t2 t3 of
    Nothing -> throwError $ UnificationFail t1 (GreaterType t2 t3)
    Just tt -> if t1 `matches` tt then return emptySubst else throwError $  UnificationFail t1 (GreaterType t2 t3))
unifies (TVarR v) t = v `bind` t
unifies t (TVarR v) = v `bind` t
unifies (TArrow t1 t2) (TArrow t3 t4) = unifyMany [t1, t2] [t3, t4]
unifies (Tuple t1 t2) (Tuple t3 t4) = unifyMany [t1, t2] [t3, t4]
unifies (TEither t1 t2) (TEither t3 t4) = unifyMany [t1, t2] [t3, t4]
unifies t1 t2 = throwError $ UnificationFail t1 t2

unifyMany :: [RType] -> [RType] -> Solve Subst
unifyMany [] [] = return emptySubst
unifyMany (t1 : ts1) (t2 : ts2) =
  do su1 <- unifies t1 t2
     su2 <- unifyMany (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyMany t1 t2 = throwError $ UnificationMismatch t1 t2

bind ::  TVarR -> RType -> Solve Subst
bind a t | t `matches` TVarR a = return emptySubst
         | occursCheck a t     = throwError $ InfiniteType a t
         | otherwise           = return (Subst $ Map.singleton a t)
         
occursCheck ::  Substitutable a => TVarR -> a -> Bool
occursCheck a t = a `Set.member` ftv t
