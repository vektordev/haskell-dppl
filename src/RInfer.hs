{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module RInfer (
  showResults, showResultsProg
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
import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Examples

data RTypeError
  = UnificationFail RType RType
  | InfiniteType TVar RType
  | UnboundVariable String
  | Ambigious [Constraint]
  | UnificationMismatch [RType] [RType]
  deriving (Show)

data Scheme = Forall [TVar] RType
  deriving (Show, Eq)

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


makeMain :: Expr () a -> Program () a
makeMain expr = Program [("main", expr)] (Call () "main")

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

newtype Subst = Subst (Map.Map TVar RType)
  deriving (Eq, Show, Monoid, Semigroup)

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance Substitutable RType where
  apply _ TBool = TBool
  apply _ TInt = TInt
  apply _ TSymbol = TSymbol
  apply _ TFloat = TFloat
  apply _ NullList = NullList
  apply s (ListOf t) = ListOf $ apply s t
  apply s (TArr t1 t2) = apply s t1 `TArr` apply s t2
  apply (Subst s) t@(TVar a) = Map.findWithDefault t a s
  apply s (GreaterType t1 t2) = apply s t1 `GreaterType` apply s t2
  -- rest of RType arent used as of now
  apply _ _ = error "Missing Substitue"

  ftv (ListOf t) = ftv t
  ftv (TVar a)       = Set.singleton a
  ftv (t1 `TArr` t2) = ftv t1 `Set.union` ftv t2
  ftv (t1 `GreaterType` t2) = ftv t1 `Set.union` ftv t2
  ftv _ = Set.empty
  ftv _ = error "Missing ftv"

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

showResultsProg :: Program () a -> IO ()
showResultsProg p@(Program decls expr) = do
  case constraintsExprProg empty p of
    Left x -> print x
    Right (cs, subst, ty, scheme) -> do
      putStrLn "Constraints: "
      listConstraints cs
      putStrLn $ "Subst: " ++ show subst
      putStrLn $ "Type:\n" ++ show ty
      putStrLn $ "Top-level Scheme: " ++ show scheme
      putStrLn "-----"

showResults :: Expr () a -> IO ()
showResults expr = do
  case constraintsExpr empty expr of
    Left x -> print x
    Right (cs, subst, ty, scheme) -> do
      putStrLn "Constraints: "
      listConstraints cs
      putStrLn $ "Subst: " ++ show subst
      putStrLn $ "Type:\n" ++ show ty
      putStrLn $ "Top-level Scheme: " ++ show scheme
      putStrLn "-----"

listConstraints :: [Constraint] -> IO ()
listConstraints ((t1, t2):cons1) = do
  putStrLn "1."
  print t1
  putStrLn "2."
  print t2
  listConstraints cons1
listConstraints [] = putStrLn "-----"
-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------

-- | Run the inference monad
runInfer :: TEnv -> Infer (RType, [Constraint]) -> Either RTypeError (RType, [Constraint])
runInfer env m = runExcept $ evalStateT (runReaderT m env) initInfer

-- | Solve for the toplevel type of an expression in a given TEnvironment
inferExpr :: TEnv -> Expr () a -> Either RTypeError Scheme
inferExpr env ex = case runInfer env (infer ex) of
  Left err -> Left err
  Right (ty, cs) -> case runSolve cs of
    Left err -> Left err
    Right subst -> Right $ closeOver $ apply subst ty

-- | Return the internal constraints used in solving for the type of an expression
constraintsExpr :: TEnv -> Expr () a -> Either RTypeError ([Constraint], Subst, RType, Scheme)
constraintsExpr env ex = case runInfer env (infer ex) of
  Left err -> Left err
  Right (ty, cs) -> case runSolve cs of
    Left err -> Left err
    Right subst -> Right (cs, subst, ty, sc)
      where
        sc = closeOver $ apply subst ty

-- | Return the internal constraints used in solving for the type of an expression
constraintsExprProg :: TEnv -> Program () a -> Either RTypeError ([Constraint], Subst, RType, Scheme)
constraintsExprProg env p@(Program decls expr) =
  case runInfer env (inferProg p) of
    Left err -> Left err
    Right (ty, cs) -> case runSolve cs of
      Left err -> Left err
      Right subst -> Right (cs, subst, ty, sc)
        where
          sc = closeOver $ apply subst ty

-- | Canonicalize and return the polymorphic toplevel type.
closeOver :: RType -> Scheme
closeOver = normalize . generalize empty

-- | Extend type TEnvironment
inTEnv :: (Name, Scheme) -> Infer a -> Infer a
inTEnv (x, sc) m = do
  let scope e = remove e x `extend` (x, sc)
  local scope m

-- | Extend type TEnvironment
inTEnvF :: [(Name, Scheme)] -> Infer a -> Infer a
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

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer RType
fresh = do
    s <- get
    put s{var_count = var_count s + 1}
    return $ TVar $ TV (letters !! var_count s)

freshVars :: Int -> [RType] -> Infer [RType]
freshVars 0 rts = do
    return $ rts
freshVars n rts = do
    s <- get
    put s{var_count = var_count s + 1}
    freshVars (n - 1)  (TVar (TV (letters !! var_count s)):rts)

instantiate ::  Scheme -> Infer RType
instantiate (Forall as t) = do
    as' <- mapM (const fresh) as
    let s = Subst $ Map.fromList $ zip as as'
    return $ apply s t

generalize :: TEnv -> RType -> Scheme
generalize env t  = Forall as t
    where as = Set.toList $ ftv t `Set.difference` ftv env

getListType :: RType -> RType -> RType
getListType t1 NullList = t1
getListType _ (ListOf t2) = t2

rtFromScheme :: Scheme -> RType
rtFromScheme (Forall _ rt) = rt

inferProg :: Program () a -> Infer (RType, [Constraint])
inferProg (Program decls expr) = do
  -- init type variable for all function decls beforehand so we can build constraints for
  -- calls between these functions
  tv_rev <- freshVars (length decls) []
  let tvs = reverse tv_rev
  -- env building with (name, scheme) for infer methods
  let func_tvs = zip (map fst decls) (map (Forall []) tvs)
  -- infer the type and constraints of the declaration expressions
  cts <- mapM ((inTEnvF func_tvs . infer) . snd) decls
  -- inferring the type of the top level expression
  (t1, c1) <- inTEnvF func_tvs (infer expr)
  -- building the constraints that the built type variables of the functions equal
  -- the inferred function type
  let tcs = zip (map (rtFromScheme . snd) func_tvs) (map fst cts)
  -- combine all constraints
  return (t1, tcs ++ concatMap snd cts ++ c1)

-- TODO Make greater number type for type instance constraint ("Overloaded operator")
infer :: Expr () a -> Infer (RType, [Constraint])
infer expr = case expr of
  ThetaI () a  -> return (TFloat, [])
  Uniform ()  -> return (TFloat, [])
  Normal ()  -> return (TFloat, [])
  Constant () val  -> return (getRType val, [])
  Call () name -> do
      t <- lookupTEnv name
      return (t, [])

  Plus x e1 e2 -> do
    (t1, c1) <- infer e1
    (t2, c2) <- infer e2
    tv <- fresh
    let u1 = t1 `TArr` (t2 `TArr` tv)
        u2 = TFloat `TArr` (TFloat `TArr` TFloat)
    return (tv, c1 ++ c2 ++ [(u1, u2)])

  Mult x e1 e2 -> do
      (t1, c1) <- infer e1
      (t2, c2) <- infer e2
      tv <- fresh
      let u1 = t1 `TArr` (t2 `TArr` tv)
          u2 = TFloat `TArr` (TFloat `TArr` TFloat)
      return (tv, c1 ++ c2 ++ [(u1, u2)])

  GreaterThan x e1 e2 -> do
      (t1, c1) <- infer e1
      (t2, c2) <- infer e2
      tv <- fresh
      let u1 = t1 `TArr` (t2 `TArr` tv)
          u2 = TFloat `TArr` (TFloat `TArr` TBool)
      return (tv, c1 ++ c2 ++ [(u1, u2)])

  IfThenElse x cond tr fl -> do
    (t1, c1) <- infer cond
    (t2, c2) <- infer tr
    (t3, c3) <- infer fl
    tv <- fresh
    return (tv, c1 ++ c2 ++ c3 ++ [(t1, TBool), (tv, GreaterType t2 t3)])

  Null x -> return (NullList, [])

  Cons x e1 e2 -> do
    (t1, c1) <- infer e1
    (t2, c2) <- infer e2
    return (ListOf t1, c1 ++ c2 ++ [(ListOf t1, t2)])

  Lambda y x e -> do
      tv <- fresh
      (t, c) <- inTEnv (x, Forall [] tv) (infer e)
      return (tv `TArr` t, c)

  Var y x -> do
        t <- lookupTEnv x
        return (t, [])

  Fix x e1 -> do
    (t1, c1) <- infer e1
    tv <- fresh
    return (tv, c1 ++ [(tv `TArr` tv, t1)])

inferTop :: TEnv -> [(String, Expr () a)] -> Either RTypeError TEnv
inferTop env [] = Right env
inferTop env ((name, ex):xs) = case inferExpr env ex of
  Left err -> Left err
  Right ty -> inferTop (extend env (name, ty)) xs

normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (map TV letters)

    fv (TVar a)   = [a]
    fv (TArr a b) = fv a ++ fv b
    fv (ListOf t)    = fv t
    fv TBool = []
    fv TInt = []
    fv TSymbol = []
    fv TFloat = []
    fv NullList = []
    fv (GreaterType a b) = fv a ++ fv b

    normtype (TArr a b) = TArr (normtype a) (normtype b)
    normtype (GreaterType a b) = normtype $ greaterType a b
    normtype (ListOf a) = ListOf (normtype a)
    normtype TBool = TBool
    normtype TInt = TInt
    normtype TFloat = TFloat
    normtype TSymbol = TBool
    normtype NullList = NullList
    normtype (TVar a)   =
      case Prelude.lookup a ord of
        Just x -> TVar x
        Nothing -> error "type variable not in signature"

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

unifyMany :: [RType] -> [RType] -> Solve Subst
unifyMany [] [] = return emptySubst
unifyMany (t1 : ts1) (t2 : ts2) =
  do su1 <- unifies t1 t2
     su2 <- unifyMany (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyMany t1 t2 = throwError $ UnificationMismatch t1 t2

unifies :: RType -> RType -> Solve Subst
unifies t1 t2 | t1 == t2 = return emptySubst
unifies (ListOf t) NullList = return emptySubst
unifies NullList (ListOf t) = return emptySubst
unifies (TVar v) t = v `bind` t
unifies t (TVar v) = v `bind` t
unifies (TArr t1 t2) (TArr t3 t4) = unifyMany [t1, t2] [t3, t4]
unifies (GreaterType t1 t2) t3 = unifies (greaterType t1 t2) t3
unifies t1 (GreaterType t2 t3) = unifies t1 (greaterType t2 t3)
unifies t1 t2 = throwError $ UnificationFail t1 t2

-- Unification solver
solver :: Unifier -> Solve Subst
solver (su, cs) =
  case cs of
    [] -> return su
    ((t1, t2): cs0) -> do
      su1  <- unifies t1 t2
      solver (su1 `compose` su, apply su1 cs0)

bind ::  TVar -> RType -> Solve Subst
bind a t | t == TVar a     = return emptySubst
         | occursCheck a t = throwError $ InfiniteType a t
         | otherwise       = return (Subst $ Map.singleton a t)

occursCheck ::  Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t
