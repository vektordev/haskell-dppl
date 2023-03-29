{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module PInferBranched (
    showResults, showResultsProg, makeMain, inferType
) where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity

import Data.List (nub)
import qualified Data.Set as Set

import Data.Monoid
import Data.Foldable hiding (toList)
import Data.Either
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


defValue :: ([Constraint], Subst, PType, Scheme)
defValue = ([], mempty, TVar $ TV "None", Forall [] (TVar $ TV "None"))

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
                  Identity)
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
  apply s (PArr p1 p2) = apply s p1 `PArr` apply s p2
  apply (Subst s) t@(TVar a) = Map.findWithDefault t a s
  -- rest of PType arent used as of now
  apply _ t = t

  ftv (TVar a)       = Set.singleton a
  ftv (PArr p1 p2) = ftv p1 `Set.union` ftv p2
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

inferType :: Program () a -> PType
inferType prog = if length res /= 1 then error "non-unique solution"
  else ty
  where res = rights $ constraintsExprProg empty prog
        (_, _, _, (Forall _ ty)) = head res

showResults :: Expr () a -> IO ()
showResults e = do
  let res = constraintsExpr empty e
  putStrLn $ "Branches: "  ++ show (length res)
  showResult res
showResult :: [Either PTypeError ([Constraint], Subst, PType, Scheme)] -> IO ()
showResult (Left err: rest)  =  do
      showResult rest
showResult (Right (cs, subst, ty, scheme):rest)  =  do
      putStrLn "-----"
    --  putStrLn "Constraints: "
    --  listConstraints cs
      putStrLn $ "Subst: " ++ show subst
      putStrLn $ "Type:\n" ++ show ty
      putStrLn $ "Top-level Scheme: " ++ show scheme
      putStrLn "-----"
      showResult rest
showResult [] = do
      putStrLn "Finished"

showResultsProg :: Program () a -> IO ()
showResultsProg p@(Program decls expr) =
  do
       let res = constraintsExprProg empty p
       putStrLn $ "Branches: "  ++ show (length res)
       showResult res
-- | Return the internal constraints used in solving for the type of an expression
constraintsExprProg :: TEnv -> Program () a -> [Either PTypeError ([Constraint], Subst, PType, Scheme)]
constraintsExprProg env p = map getP (runInfer env (inferProg p))
        where getP j = case j of  Left err -> Left err
                                  Right inf_list -> doAllSolve inf_list

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
runInfer :: TEnv -> Infer [Branch] -> [Branch]
runInfer env m = runIdentity $ evalStateT (runReaderT m env) initInfer


-- | Return the internal constraints used in solving for the type of an expression
constraintsExpr :: TEnv -> Expr () a -> [Either PTypeError ([Constraint], Subst, PType, Scheme)]
constraintsExpr env ex = map getP (runInfer env (infer ex))
  where getP j = case j of  Left err -> Left err
                            Right inf_list -> doAllSolve inf_list

doAllSolve :: (PType, [Constraint]) -> Either PTypeError ([Constraint], Subst, PType, Scheme)
doAllSolve (ty, cs) = case runSolve cs of
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
lookupTEnv :: Name -> Infer (Either PTypeError PType)
lookupTEnv x = do
  (TypeEnv env) <- ask
  case Map.lookup x env of
      Nothing   ->  return $ Left (UnboundVariable x)
      Just s    ->  do t <- instantiate s
                       return (Right t)

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

-- | Extend type TEnvironment
inTEnvF :: [(Name, Scheme)] -> Infer a -> Infer a
inTEnvF [] m = m
inTEnvF ((x, sc): r) m = do
  let scope e = remove e x `extend` (x, sc)
  inTEnvF r (local scope m)


freshVars :: Int -> [PType] -> Infer [PType]
freshVars 0 rts = do
    return $ rts
freshVars n rts = do
    s <- get
    put s{var_count = var_count s + 1}
    freshVars (n - 1)  (TVar (TV (letters !! var_count s)):rts)


combineBranch :: Branch -> Branch -> Either PTypeError ((PType, PType), [Constraint])
combineBranch b1 b2 = case b1 of
  Left err1 -> Left err1
  Right (ty1, cs1) -> case b2 of
                      Left err2 -> Left err2
                      Right (ty2, cs2) -> Right ((ty1, ty2), cs1 ++ cs2)

combineBranches :: [Branch] -> [Branch] -> [Either PTypeError ((PType, PType), [Constraint])]
combineBranches b1 b2 = combineBranch <$> b1 <*> b2

-- here we add the function body type constraint to its passed function name
combineBranchFunc :: PType -> Branch -> Branch -> Branch
combineBranchFunc f_tv b1 b2 = case b1 of
  Left err1 -> Left err1
  Right (ty1, cs1) -> case b2 of
                      Left err2 -> Left err2
                      Right (ty2, cs2) -> Right (ty1, [(ty2, f_tv)] ++ cs1 ++ cs2 )

combineBranchesFunc :: [Branch] -> ([Branch], PType) -> [Branch]
combineBranchesFunc b1 (b2, f_tv) = combineBranchFunc f_tv <$> b1 <*> b2

basicTypes :: [PType]
basicTypes = [Deterministic, Integrate, Chaos]
-- det is for plus/mult where integrate integrate results in chaos
buildDet :: Either PTypeError ((PType, PType), [Constraint]) -> [Branch]
buildDet b = case b of
    Left err -> [Left err]
    Right ((t1, t2), cs) -> if elem t1 basicTypes && elem t2 basicTypes then [Right (downgrade2 t1 t2, cs)] else
                            [Right (Integrate, cs ++ [(t1, Deterministic), (t2, Integrate)]),
                            Right (Integrate, cs ++ [(t2, Deterministic), (t1, Integrate)]),
                            Right (Deterministic, cs ++ [(t2, Deterministic), (t1, Deterministic)]),
                            Right (Chaos, cs ++ [(t2, Integrate), (t1, Integrate)]),
                            Right (Chaos, cs ++ [(t2, Chaos), (t1, Chaos)]),
                            Right (Chaos, cs ++ [(t2, Integrate), (t1, Chaos)]),
                            Right (Chaos, cs ++ [(t2, Chaos), (t1, Integrate)]),
                            Right (Chaos, cs ++ [(t2, Chaos), (t1, Deterministic)]),
                            Right (Chaos, cs ++ [(t2, Deterministic), (t1, Chaos)])]

-- this is straight downgrade method (Chaos will produce UnificationFail)
buildInt :: Either PTypeError ((PType, PType), [Constraint]) -> [Branch]
buildInt b = case b of
   Left err -> [Left err]
   
   Right ((t1, t2), cs) -> if elem t1 basicTypes && elem t2 basicTypes then [Right (downgrade t1 t2, cs)]else
                           [Right (Integrate, cs ++ [(t1, Deterministic), (t2, Integrate)]),
                           Right (Integrate, cs ++ [(t2, Deterministic), (t1, Integrate)]),
                           Right (Deterministic, cs ++ [(t2, Deterministic), (t1, Deterministic)]),
                           Right (Integrate, cs ++ [(t2, Integrate), (t1, Integrate)]),
                           Right (Chaos, cs ++ [(t2, Chaos), (t1, Chaos)]),
                           Right (Chaos, cs ++ [(t2, Integrate), (t1, Chaos)]),
                           Right (Chaos, cs ++ [(t2, Chaos), (t1, Integrate)]),
                           Right (Chaos, cs ++ [(t2, Chaos), (t1, Deterministic)]),
                           Right (Chaos, cs ++ [(t2, Deterministic), (t1, Chaos)])
                           ]

rtFromScheme :: Scheme -> PType
rtFromScheme (Forall _ rt) = rt

type Branch = Either PTypeError (PType, [Constraint])

inferProg :: Program () a -> Infer [Branch]
inferProg (Program decls expr) = do
  -- init type variable for all function decls beforehand so we can build constraints for
  -- calls between these functions
  tv_rev <- freshVars (length decls) []
  let tvs = reverse tv_rev
  -- env building with (name, scheme) for infer methods
  let func_tvs = zip (map fst decls) (map (Forall []) tvs)
  -- infer the type and constraints of the declaration expressions
  -- [[Branch]]
  func_branches_list <- mapM ((inTEnvF func_tvs . infer) . snd) decls
  -- inferring the type of the top level expression
  -- [Branch]
  top_branches <- inTEnvF func_tvs (infer expr)
  let f_names = map (rtFromScheme . snd) func_tvs
  -- combine all constraints
  return $ foldl combineBranchesFunc top_branches (zip func_branches_list f_names)

-- TODO Make greater number type for type instance constraint ("Overloaded operator")
infer :: Expr () a -> Infer [Branch]
infer expr = case expr of
  ThetaI () a  -> return [Right (Deterministic, [])]
  Uniform ()  -> return [Right (Integrate, [])]
  Normal ()  -> return [Right (Integrate, [])]
  Constant () val  -> return [Right (Deterministic, [])]

  Plus x e1 e2 -> do
      list1 <- infer e1
      list2 <- infer e2
      let comb = combineBranches list1 list2
      return $ concatMap buildDet comb

  Mult x e1 e2 -> do
      list1 <- infer e1
      list2 <- infer e2
      let comb = combineBranches list1 list2
      return $ concatMap buildDet comb

  GreaterThan x e1 e2 -> do
      list1 <- infer e1
      list2 <- infer e2
      let comb = combineBranches list1 list2
      return $ concatMap buildInt comb

  IfThenElse x cond tr fl -> do
    list1 <- infer cond
    list2 <- infer tr
    list3 <- infer fl
    let comb1 = combineBranches list2 list3
    let b1 = concatMap buildInt comb1
    let comb2 = combineBranches list1 b1
    return $ concatMap buildInt comb2

  Null x -> return [Right (Deterministic, [])]

  Cons x e1 e2 -> do
    list1 <- infer e1
    list2 <- infer e2
    let comb = combineBranches list1 list2
    return $ concatMap buildInt comb

  Call () name -> do
      t <- lookupTEnv name
      return (case t of
                Left err ->  [Left err]
                Right ty -> [Right (ty, [])])


normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (map TV letters)

    fv (TVar a)   = [a]
    fv (PArr a b) = fv a ++ fv b
    fv Deterministic = []
    fv Integrate = []
    fv Chaos = []

    normtype (PArr a b) = PArr (normtype a) (normtype b)
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
unifies (TVar v) t = v `bind` t
unifies t (TVar v) = v `bind` t
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
