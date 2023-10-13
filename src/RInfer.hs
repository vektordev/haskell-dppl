{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module RInfer (
  showResults, showResultsProg, inferRType, RTypeError, addRTypeInfo
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

import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Examples
import SPLL.Typing.PType( PType(..) )

import InjectiveFunctions
data RTypeError
  = UnificationFail RType RType
  | InfiniteType TVarR RType
  | UnboundVariable String
  | Ambigious [Constraint]
  | UnificationMismatch [RType] [RType]
  | ExprInfo [String]
  | FalseParameterFail String
  deriving (Show)

data Scheme = Forall [TVarR] RType
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


makeMain :: Expr TypeInfo a -> Program TypeInfo a
makeMain expr = Program [("main", expr)] (Call (getTypeInfo expr) "main")

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
instance Substitutable (Program TypeInfo a) where
  apply s (Program decls expr) = Program (zip (map fst decls) (map (apply s . snd) decls)) (apply s expr)
  ftv _ = Set.empty
instance Substitutable (Expr TypeInfo a) where
  apply s = tMap (apply s . getTypeInfo)
  ftv _ = Set.empty
instance Substitutable TypeInfo where
  apply s (TypeInfo rt pt) = TypeInfo (apply s rt) pt
  ftv _ = Set.empty

instance Substitutable RType where
  apply _ TBool = TBool
  apply _ TInt = TInt
  apply _ TSymbol = TSymbol
  apply _ TFloat = TFloat
  apply _ NullList = NullList
  apply _ BottomTuple = BottomTuple
  apply s (ListOf t) = ListOf $ apply s t
  apply s (Tuple t1) = Tuple $ map (apply s) t1 
  apply s (TArrow t1 t2) = apply s t1 `TArrow` apply s t2
  apply (Subst s) t@(TVarR a) = Map.findWithDefault t a s
  apply s (GreaterType t1 t2) = apply s t1 `GreaterType` apply s t2
  -- rest of RType arent used as of now
  apply _ val = error ("Missing Substitute: " ++ show val)

  ftv (ListOf t) = ftv t
  ftv (Tuple t1) = foldl Set.union Set.empty (map ftv t1)
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
  
addRTypeInfo :: (Show a) => Program TypeInfo a -> Program TypeInfo a
addRTypeInfo p@(Program decls expr) =
  case runInfer empty (inferProg p) of
    Left err -> error ("error in addRTypeInfo: " ++ show err)
    Right (ty, cs, p) -> case runSolve cs of
      Left err -> error ("error in solve addRTypeInfo: " ++ show err)
      Right subst -> apply subst p
      
showResultsProg :: (Num a, Show a) => Program TypeInfo a -> IO ()
showResultsProg p@(Program decls expr) = do
  case constraintsExprProg empty p of
    Left x -> print x
    Right (cs, subst, ty, scheme, p) -> do
      putStrLn "Constraints: "
      listConstraints cs
      putStrLn $ "Subst: " ++ show subst
      putStrLn $ "Type:\n" ++ show ty
      putStrLn $ "Top-level Scheme: " ++ show scheme
      putStrLn $ "Program: "
      putStrLn $ unlines $ prettyPrintProg p
      putStrLn "-----"

showResults :: (Num a, Show a) => Expr TypeInfo a -> IO ()
showResults expr = do
  case constraintsExpr empty expr of
    Left x -> print x
    Right (cs, subst, ty, scheme, p) -> do
      putStrLn "Constraints: "
      listConstraints cs
      putStrLn $ "Subst: " ++ show subst
      putStrLn $ "Type:\n" ++ show ty
      putStrLn $ "Top-level Scheme: " ++ show scheme
      putStrLn $ "Expr: " 
      putStrLn $ unlines $ prettyPrint p
      putStrLn "-----"

listConstraints :: [Constraint] -> IO ()
listConstraints ((t1, t2):cons1) = do
  putStrLn "1."
  pPrint t1
  putStrLn "2."
  pPrint t2
  listConstraints cons1
listConstraints [] = putStrLn "-----"
-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------

inferRType :: (Show a) => Program TypeInfo a -> Either RTypeError RType
inferRType prog@(Program decls expr) = do
  case runInfer mempty (inferProg prog) of
      Left err -> Left (ExprInfo $ prettyPrintProgNoReq prog)
      Right (ty, cs, p) -> case runSolve cs of
        Left err -> Left (err)
        Right subst -> Right $ apply subst ty
          where
            sc = closeOver $ apply subst ty

-- | Run the inference monad
runInfer :: TEnv -> Infer (RType, [Constraint], Program TypeInfo a) -> Either RTypeError (RType, [Constraint], Program TypeInfo a)
runInfer env m = runExcept $ evalStateT (runReaderT m env) initInfer

runInferExpr :: TEnv -> Infer (RType, [Constraint], Expr TypeInfo a) -> Either RTypeError (RType, [Constraint], Expr TypeInfo a)
runInferExpr env m = runExcept $ evalStateT (runReaderT m env) initInfer
-- | Solve for the toplevel type of an expression in a given TEnvironment
inferExpr :: (Show a) => TEnv -> Expr TypeInfo a -> Either RTypeError Scheme
inferExpr env ex = case runInferExpr env (infer ex) of
  Left err -> Left err
  Right (ty, cs, _) -> case runSolve cs of
    Left err -> Left err
    Right subst -> Right $ closeOver $ apply subst ty

-- | Return the internal constraints used in solving for the type of an expression
constraintsExpr :: (Show a) => TEnv -> Expr TypeInfo a -> Either RTypeError ([Constraint], Subst, RType, Scheme, Expr TypeInfo a)
constraintsExpr env ex = case runInferExpr env (infer ex) of
  Left err -> Left err
  Right (ty, cs, p) -> case runSolve cs of
    Left err -> Left err
    Right subst -> Right (cs, subst, ty, sc, apply subst p)
      where
        sc = closeOver $ apply subst ty

-- | Return the internal constraints used in solving for the type of an expression
constraintsExprProg :: (Show a) => TEnv -> Program TypeInfo a -> Either RTypeError ([Constraint], Subst, RType, Scheme, Program TypeInfo a)
constraintsExprProg env p@(Program decls expr) =
  case runInfer env (inferProg p) of
    Left err -> Left err
    Right (ty, cs, p) -> case runSolve cs of
      Left err -> Left err
      Right subst -> Right (cs, subst, apply subst ty, sc, apply subst p)
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

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer RType
fresh = do
    s <- get
    put s{var_count = var_count s + 1}
    return $ TVarR $ TV (letters !! var_count s)

freshVars :: Int -> [RType] -> Infer [RType]
freshVars 0 rts = do
    return $ rts
freshVars n rts = do
    s <- get
    put s{var_count = var_count s + 1}
    freshVars (n - 1)  (TVarR (TV (letters !! var_count s)):rts)

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

inferProg :: (Show a) => Program TypeInfo a -> Infer (RType, [Constraint], Program TypeInfo a)
inferProg p@(Program decls expr) = do
  -- init type variable for all function decls beforehand so we can build constraints for
  -- calls between these functions
  tv_rev <- freshVars (length decls) []
  let tvs = reverse tv_rev
  -- env building with (name, scheme) for infer methods
  let func_tvs = zip (map fst decls) (map (Forall []) tvs)
  -- infer the type and constraints of the declaration expressions
  cts <- mapM ((inTEnvF func_tvs . infer) . snd) decls
  -- inferring the type of the top level expression
  (t1, c1, et) <- inTEnvF func_tvs (infer expr)
  -- building the constraints that the built type variables of the functions equal
  -- the inferred function type
  let tcs = zip (map (rtFromScheme . snd) func_tvs) (map fst3cts cts)
  -- combine all constraints
  return (t1, tcs ++ concatMap snd3cts cts ++ c1, Program (zip (map fst decls) (map trd3cts cts)) et)
fst3cts ::  (RType, [Constraint], Expr TypeInfo a) -> RType
fst3cts (t, _, _) = t
snd3cts ::  (RType, [Constraint], Expr TypeInfo a) -> [Constraint]
snd3cts (_, cts, _) = cts
trd3cts ::  (RType, [Constraint], Expr TypeInfo a) -> Expr TypeInfo a
trd3cts (_, _, e) = e

    
buildFuncConstraints :: RType -> RType -> [RType] -> [Constraint] -> String -> Infer (RType, [Constraint])
buildFuncConstraints (TArrow inpT (TArrow _ _)) _ [] cons name  = throwError $ FalseParameterFail name  
buildFuncConstraints (TArrow inpT (TArrow t1 t2)) ft (rt1:rts) cons name  = 
  buildFuncConstraints (TArrow t1 t2) ft rts ((inpT, rt1):cons) name
buildFuncConstraints (TArrow inpT t1) finalType [] cons name  = return (t1, (inpT, finalType):cons)
buildFuncConstraints (TArrow inpT t1) finalType _ cons name  = throwError $ FalseParameterFail name
buildFuncConstraints _ finalType _ cons name  = error "buildFuncConstraints with non function type"

lookupRConstraint :: Expr TypeInfo a -> Infer RType
lookupRConstraint (ThetaI _ _) = return TFloat
lookupRConstraint (Uniform _ ) = return TFloat
lookupRConstraint (Normal _  ) = return TFloat
lookupRConstraint (PlusF _ _ _) = return $ TFloat `TArrow` (TFloat `TArrow` TFloat)
lookupRConstraint (PlusI _ _ _) = return $ TInt   `TArrow` (TInt   `TArrow` TInt  )
lookupRConstraint (MultF _ _ _) = return $ TFloat `TArrow` (TFloat `TArrow` TFloat)
lookupRConstraint (MultI _ _ _) = return $ TInt   `TArrow` (TInt   `TArrow` TInt  )
lookupRConstraint (GreaterThan _ _ _) = return $ TFloat `TArrow` (TFloat `TArrow` TBool)

-- TODO Make greater number type for type instance constraint ("Overloaded operator")
infer :: Show a =>Expr TypeInfo a -> Infer (RType, [Constraint], Expr TypeInfo a)
infer expr = case expr of
  ThetaI ti a  -> return (TFloat, [], ThetaI (setRType ti TFloat) a)
  Uniform ti  -> return (TFloat, [], Uniform (setRType ti TFloat))
  Normal ti  -> return (TFloat, [], Normal (setRType ti TFloat))
  Constant ti val  -> return (getRType val, [], Constant(setRType ti (getRType val)) val)
  Call ti name -> do
      t <- lookupTEnv name
      return (t, [], Call (setRType ti t) name)

  PlusF x e1 e2 -> do
    (t1, c1, et1) <- infer e1
    (t2, c2, et2) <- infer e2
    tv <- fresh
    let u1 = t1 `TArrow` (t2 `TArrow` tv)
    -- Can't handle Int and Float at same time....
        u2 = TFloat `TArrow` (TFloat `TArrow` TFloat)
    return (tv, c1 ++ c2 ++ [(u1, u2)], PlusF (setRType x tv) et1 et2)

  PlusI x e1 e2 -> do
    (t1, c1, et1) <- infer e1
    (t2, c2, et2) <- infer e2
    tv <- fresh
    let u1 = t1 `TArrow` (t2 `TArrow` tv)
    -- Can't handle Int and Float at same time....
        u2 = TInt `TArrow` (TInt `TArrow` TInt)
    return (tv, c1 ++ c2 ++ [(u1, u2)], PlusI (setRType x tv) et1 et2)

  MultF x e1 e2 -> do
      (t1, c1, et1) <- infer e1
      (t2, c2, et2) <- infer e2
      tv <- fresh
      let u1 = t1 `TArrow` (t2 `TArrow` tv)
          u2 = TFloat `TArrow` (TFloat `TArrow` TFloat)
      return (tv, c1 ++ c2 ++ [(u1, u2)], MultF (setRType x tv)  et1 et2)

  MultI x e1 e2 -> do
      (t1, c1, et1) <- infer e1
      (t2, c2, et2) <- infer e2
      tv <- fresh
      let u1 = t1 `TArrow` (t2 `TArrow` tv)
          u2 = TInt `TArrow` (TInt `TArrow` TInt)
      return (tv, c1 ++ c2 ++ [(u1, u2)], MultI (setRType x tv)  et1 et2)

  GreaterThan x e1 e2 -> do
      (t1, c1, et1) <- infer e1
      (t2, c2, et2) <- infer e2
      tv <- fresh
      let u1 = t1 `TArrow` (t2 `TArrow` tv)
          u2 = TFloat `TArrow` (TFloat `TArrow` TBool)
      return (tv, c1 ++ c2 ++ [(u1, u2)], GreaterThan (setRType x tv)  et1 et2)

  IfThenElse x cond tr fl -> do
    (t1, c1, condt) <- infer cond
    (t2, c2, trt) <- infer tr
    (t3, c3, flt) <- infer fl
    tv <- fresh
    return (tv, c1 ++ c2 ++ c3 ++ [(t1, TBool), (tv, GreaterType t2 t3)], IfThenElse (setRType x tv)  condt trt flt)
  
  InjF x name e1 e -> do
      (t1, c1, et1) <- infer e
      p_inf <- mapM infer e1
      let (Just (FPair fPair)) = lookup name globalFenv
      let (funcTy, _, _, _) = fPair
      (retT, cFunc) <- buildFuncConstraints funcTy t1 (map fst3cts p_inf) [] name
      return (retT, c1 ++ (concatMap snd3cts p_inf) ++ cFunc, InjF (setRType x retT) name (map trd3cts p_inf) et1)

  LetIn x name e1 e2 -> do
      env <- ask
      (t1, c1, et1) <- infer e1
      case runSolve c1 of
          Left err -> throwError err
          Right sub -> do
              let sc = generalize (apply sub env) (apply sub t1)
              (t2, c2, et2) <- inTEnv (name, sc) $ local (apply sub) (infer e2)
              return (t2, c1 ++ c2, LetIn (setRType x t2)  name et1 et2 )
  
  Lambda x name e2 -> do
    tv <- fresh
    let sc = Forall [] tv
    (t1, c1, et1) <- inTEnv (name, sc) (infer e2)
    return (tv `TArrow` t1, c1, Lambda (setRType x (tv `TArrow` t1)) name et1)
    
  
  Null x -> return (NullList, [], Null (setRType x NullList))

  Cons x e1 e2 -> do
    (t1, c1, et1) <- infer e1
    (t2, c2, et2) <- infer e2
    return (ListOf t1, c1 ++ c2 ++ [(ListOf t1, t2)], Cons (setRType x (ListOf t1)) et1 et2)

  TNull x -> return (Tuple [], [], TNull (setRType x (Tuple [])))
  
  TCons x e1 e2 -> do
      (t1, c1, et1) <- infer e1
      (t2, c2, et2) <- infer e2
      let (Tuple t2t) = t2
      return (Tuple $ t1:t2t, c1 ++ c2 ++ [(BottomTuple, t2)], TCons (setRType x (Tuple $ t1:t2t)) et1 et2)

  Var y x -> do
      t <- lookupTEnv x
      return (t, [], Var (setRType y t) x)
  
  ReadNN x name e1 -> do
      (t1, c1, et1) <- infer e1
      return (TInt, c1 ++ [(t1, TSymbol)], ReadNN (setRType x TInt) name et1)
  
  _ -> error (show expr)


inferTop :: (Show a) => TEnv -> [(String, Expr TypeInfo a)] -> Either RTypeError TEnv
inferTop env [] = Right env
inferTop env ((name, ex):xs) = case inferExpr env ex of
  Left err -> Left err
  Right ty -> inferTop (extend env (name, ty)) xs

normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (map TV letters)

    fv (TVarR a)   = [a]
    fv (TArrow a b) = fv a ++ fv b
    fv (ListOf t)    = fv t
    fv TBool = []
    fv TInt = []
    fv TSymbol = []
    fv TFloat = []
    fv NullList = []
    fv (GreaterType a b) = fv a ++ fv b

    normtype (TArrow a b) = TArrow (normtype a) (normtype b)
    normtype (GreaterType a b) = case gt of
       Nothing -> error "normalized greater type"
       Just rt -> normtype rt
       where gt = greaterType a b
    normtype (ListOf a) = ListOf (normtype a)
    normtype TBool = TBool
    normtype TInt = TInt
    normtype TFloat = TFloat
    normtype TSymbol = TBool
    normtype NullList = NullList
    normtype (TVarR a)   =
      case Prelude.lookup a ord of
        Just x -> TVarR x
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
unifies (Tuple t) BottomTuple = return emptySubst
unifies BottomTuple (Tuple t) = return emptySubst
unifies (ListOf t) NullList = return emptySubst
unifies NullList (ListOf t) = return emptySubst
unifies t1 (GreaterType (TVarR v) t3) = if t1 == t3 then v `bind` t1 else
  throwError $ UnificationFail t1 t3
unifies t1 (GreaterType t3 (TVarR v)) = if t1 == t3 then v `bind` t1 else
  throwError $ UnificationFail t1 t3
unifies (TVarR v) (GreaterType t2 t3) = case greaterType t2 t3 of
  Nothing -> throwError $ UnificationFail t2 t3
  Just t -> v `bind` t
unifies t1 (GreaterType t2 t3) = if t1 == t2 && t2 == t3 then return emptySubst else
  (case greaterType t2 t3 of
   Nothing -> throwError $ UnificationFail t1 (GreaterType t2 t3)
   Just tt -> if t1 == tt then return emptySubst else throwError $  UnificationFail t1 (GreaterType t2 t3))

unifies (TVarR v) t = v `bind` t
unifies t (TVarR v) = v `bind` t
unifies (TArrow t1 t2) (TArrow t3 t4) = unifyMany [t1, t2] [t3, t4]
unifies (Tuple []) (Tuple []) = return emptySubst
unifies (Tuple t1) (Tuple t2) = unifyMany t1 t2
unifies t1 t2 = throwError $ UnificationFail t1 t2

-- Unification solver
solver :: Unifier -> Solve Subst
solver (su, cs) =
  case cs of
    [] -> return su
    ((t1, t2): cs0) -> do
      su1  <- unifies t1 t2
      solver (su1 `compose` su, apply su1 cs0)

bind ::  TVarR -> RType -> Solve Subst
bind a t | t == TVarR a     = return emptySubst
         | occursCheck a t = throwError $ InfiniteType a t
         | otherwise       = return (Subst $ Map.singleton a t)

occursCheck ::  Substitutable a => TVarR -> a -> Bool
occursCheck a t = a `Set.member` ftv t
