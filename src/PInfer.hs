{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module PInfer (
    showResults
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
import SPLL.Typing.PType
import SPLL.Examples

data PTypeError
  = UnificationFail PType PType
  | InfiniteType TVar PType
  | UnboundVariable String
  | Ambigious [Constraint]
  | UnificationMismatch [PType] [PType]
  deriving (Show)

data Scheme = Forall [TVar] PType
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

type Name = String

data Program x a = Program [Decl x a] (Expr x a) deriving Eq

type Decl x a = (String, Expr x a)

makeMain :: Expr () a -> Program () a
makeMain expr = Program [("main", expr)] (Call () "main")

-- | Inference monad
type Infer a = (ReaderT
                  TEnv             -- Typing TEnvironment
                  (StateT         -- Inference state
                  InferState
                  (Except         -- Inference errors
                    PTypeError))
                  a)              -- Result

-- | Inference state
data InferState = InferState { var_count :: Int }

-- | Initial inference state
initInfer :: InferState
initInfer = InferState { var_count = 0 }

type Constraint = (PType, PType)

type Unifier = (Subst, [Constraint])

-- | Constraint solver monad
type Solve a = ExceptT PTypeError Identity a

newtype Subst = Subst (Map.Map TVar PType)
  deriving (Eq, Show, Monoid, Semigroup)

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance Substitutable PType where
  apply _ Deterministic = Deterministic
  apply _ Integrate = Integrate
  apply _ Chaos = Chaos
  apply s (PComb p1 p2) = apply s p1 `PComb` apply s p2
  apply (Subst s) t@(TVar a) = Map.findWithDefault t a s
  -- rest of PType arent used as of now
  apply _ t = t

  ftv (TVar a)       = Set.singleton a
  ftv (PComb p1 p2) = ftv p1 `Set.union` ftv p2
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

showResultsProg :: Program () a -> IO ()
showResultsProg p@(Program decls expr) = do
  case constraintsExprProg empty expr of
    Left x -> print x
    Right (cs, subst, ty, scheme) -> do
      putStrLn "Constraints: "
      listConstraints cs
      putStrLn $ "Subst: " ++ show subst
      putStrLn $ "Type:\n" ++ show ty
      putStrLn $ "Top-level Scheme: " ++ show scheme
      putStrLn "-----"

-- | Return the internal constraints used in solving for the type of an expression
constraintsExprProg :: TEnv -> Expr () a -> Either PTypeError ([Constraint], Subst, PType, Scheme)
constraintsExprProg env ex = case runInfer env (infer ex) of
  Left err -> Left err
  Right (ty, cs) -> case runSolve cs of
    Left err -> Left err
    Right subst -> Right (cs, subst, ty, sc)
      where
        sc = closeOver $ apply subst ty
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
runInfer :: TEnv -> Infer (PType, [Constraint]) -> Either PTypeError (PType, [Constraint])
runInfer env m = runExcept $ evalStateT (runReaderT m env) initInfer

-- | Solve for the toplevel type of an expression in a given TEnvironment
inferExpr :: TEnv -> Expr () a -> Either PTypeError Scheme
inferExpr env ex = case runInfer env (infer ex) of
  Left err -> Left err
  Right (ty, cs) -> case runSolve cs of
    Left err -> Left err
    Right subst -> Right $ closeOver $ apply subst ty

-- | Return the internal constraints used in solving for the type of an expression
constraintsExpr :: TEnv -> Expr () a -> Either PTypeError ([Constraint], Subst, PType, Scheme)
constraintsExpr env ex = case runInfer env (infer ex) of
  Left err -> Left err
  Right (ty, cs) -> case runSolve cs of
    Left err -> Left err
    Right subst -> Right (cs, subst, ty, sc)
      where
        sc = closeOver $ apply subst ty

-- | Canonicalize and return the polymorphic toplevel type.
closeOver :: PType -> Scheme
closeOver = normalize . generalize empty

-- | Extend type TEnvironment
inTEnv :: (Name, Scheme) -> Infer a -> Infer a
inTEnv (x, sc) m = do
  let scope e = (remove e x) `extend` (x, sc)
  local scope m

-- | Lookup type in the TEnvironment
lookupTEnv :: Name -> Infer PType
lookupTEnv x = do
  (TypeEnv env) <- ask
  case Map.lookup x env of
      Nothing   ->  throwError $ UnboundVariable x
      Just s    ->  do t <- instantiate s
                       return t

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer PType
fresh = do
    s <- get
    put s{var_count = var_count s + 1}
    return $ TVar $ TV (letters !! var_count s)

instantiate ::  Scheme -> Infer PType
instantiate (Forall as t) = do
    as' <- mapM (const fresh) as
    let s = Subst $ Map.fromList $ zip as as'
    return $ apply s t

generalize :: TEnv -> PType -> Scheme
generalize env t  = Forall as t
    where as = Set.toList $ ftv t `Set.difference` ftv env

-- TODO Make greater number type for type instance constraint ("Overloaded operator")
infer :: Expr () a -> Infer (PType, [Constraint])
infer expr = case expr of
  ThetaI () a  -> return (Deterministic, [])
  Uniform ()  -> return (Integrate, [])
  Normal ()  -> return (Integrate, [])
  Constant () val  -> return (Deterministic, [])



inferTop :: TEnv -> [(String, Expr () a)] -> Either PTypeError TEnv
inferTop env [] = Right env
inferTop env ((name, ex):xs) = case inferExpr env ex of
  Left err -> Left err
  Right ty -> inferTop (extend env (name, ty)) xs

normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (map TV letters)

    fv (TVar a)   = [a]
    fv (PComb a b) = fv a ++ fv b
    fv Deterministic = []
    fv Integrate = []
    fv Chaos = []

    normtype (PComb a b) = PComb (normtype a) (normtype b)
    normtype Deterministic = Deterministic
    normtype Integrate = Integrate
    normtype Chaos = Chaos
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
runSolve :: [Constraint] -> Either PTypeError Subst
runSolve cs = runIdentity $ runExceptT $ solver st
  where st = (emptySubst, cs)

unifyMany :: [PType] -> [PType] -> Solve Subst
unifyMany [] [] = return emptySubst
unifyMany (t1 : ts1) (t2 : ts2) =
  do su1 <- unifies t1 t2
     su2 <- unifyMany (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyMany t1 t2 = throwError $ UnificationMismatch t1 t2

unifies :: PType -> PType -> Solve Subst
unifies t1 t2 | t1 == t2 = return emptySubst
unifies t1 t2 = throwError $ UnificationFail t1 t2

-- Unification solver
solver :: Unifier -> Solve Subst
solver (su, cs) =
  case cs of
    [] -> return su
    ((t1, t2): cs0) -> do
      su1  <- unifies t1 t2
      solver (su1 `compose` su, apply su1 cs0)

bind ::  TVar -> PType -> Solve Subst
bind a t | t == TVar a     = return emptySubst
         | occursCheck a t = throwError $ InfiniteType a t
         | otherwise       = return (Subst $ Map.singleton a t)

occursCheck ::  Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t
