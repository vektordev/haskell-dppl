{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SPLL.Typing.PInfer (
    showResults, showResultsProg, inferType
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
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.PType
import SPLL.Examples

data PTypeError
  = UnificationFail PType PType
  | InfiniteType TVar PType
  | UnboundVariable String
  deriving (Show)
type Var = String
type Infer = ExceptT PTypeError (State InferState)
data Scheme = Forall [TVar] [Constraint] PType
  deriving (Show, Eq)

plusEnv :: TEnv
plusEnv = TypeEnv $ Map.fromList [plus, greaterThan]

--Deterministic <= Integrable <= Chaos
--tv1 -> tv2 -> tv3 
-- (Integrable -> Integrable -> Integrable) <= (Deterministic -> Deterministic -> Chaos) 
plus :: (Var, [Scheme])
plus = ("+", [Forall [] [] (Deterministic `PArr` Deterministic `PArr` Deterministic),
              Forall [] [] (Integrate `PArr` Deterministic `PArr` Integrate),
              Forall [] [] (Deterministic `PArr` Integrate `PArr` Integrate),
              Forall [] [] (Deterministic `PArr` Bottom `PArr` Bottom),
              Forall [] [] (Bottom `PArr` Deterministic `PArr` Bottom),
              Forall [] [] (Bottom `PArr` Integrate `PArr` Bottom),
              Forall [] [] (Integrate `PArr` Bottom `PArr` Bottom),
              Forall [] [] (Bottom `PArr` Bottom `PArr` Bottom),
              Forall [] [] (Integrate `PArr` Integrate `PArr` Bottom)
              ])
-- Forall [] [] (a `PArr` b `PArr` downgrade(a,b))
greaterThan :: (Var, [Scheme])
greaterThan = (">=", [Forall [] [] (Deterministic `PArr` Deterministic `PArr` Deterministic),
                    Forall [] [] (Integrate `PArr` Deterministic `PArr` Integrate),
                    Forall [] [] (Deterministic `PArr` Integrate `PArr` Integrate),
                    Forall [] [] (Deterministic `PArr` Bottom `PArr` Bottom),
                    Forall [] [] (Bottom `PArr` Deterministic `PArr` Bottom),
                    Forall [] [] (Bottom `PArr` Integrate `PArr` Bottom),
                    Forall [] [] (Integrate `PArr` Bottom `PArr` Bottom),
                    Forall [] [] (Bottom `PArr` Bottom `PArr` Bottom),
                    Forall [] [] (Integrate `PArr` Integrate `PArr` Integrate)
                    ])

showResults :: Expr a -> IO ()
showResults expr = do
  case inferExpr plusEnv expr of
    Left err -> print err
    Right (cons, (scheme, schemeRes)) -> do
      putStrLn $ "B:\n" ++ show cons
      putStrLn $ "Type (No Resolution, No normalize):\n" ++ show scheme
      putStrLn $ "Type (No Resolution):\n" ++ show (normalize scheme)
      putStrLn $ "Type:\n" ++ show (normalize schemeRes)
      putStrLn "-----"

inferType :: Program a -> PType
inferType prog = do
  case inferProgram plusEnv prog of
     Left err -> error "error in infer scheme"
     Right (_, (_, Forall _ b ty)) -> if null b then ty else error "non-empty constraints inferred"
     
showResultsProg :: Program a -> IO ()
showResultsProg prog = do
  case inferProgram plusEnv prog of
    Left err -> print err
    Right (cons, (scheme, schemeRes)) -> do
      putStrLn $ "B:\n" ++ show cons
      putStrLn $ "Type (No Resolution, No normalize):\n" ++ show scheme
      putStrLn $ "Type (No Resolution):\n" ++ show (normalize scheme)
      putStrLn $ "Type:\n" ++ show (normalize schemeRes)
      putStrLn "-----"
type Constraint = (Var, PType)



newtype TEnv
  = TypeEnv {types :: Map.Map Name [Scheme]}
  deriving (Eq, Show)


instance Semigroup TEnv where
  (TypeEnv a) <> (TypeEnv b) = TypeEnv (Map.union a b)

instance Monoid TEnv where
  mempty = TypeEnv Map.empty
  mappend = (<>)

makeMain :: Expr a -> Program a
makeMain expr = Program [("main", expr)] [] (Call makeTypeInfo "main")

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

-- | The empty substitution
emptySubst :: Subst
emptySubst = mempty

-- | Compose substitutions
compose :: Subst -> Subst -> Subst
(Subst s1) `compose` (Subst s2) = Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1


class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance Substitutable PType where
  apply _ Deterministic = Deterministic
  apply _ Integrate = Integrate
  apply _ Bottom = Bottom
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

instance Substitutable Constraint where
   apply s (v, t1) = (v, apply s t1)
   ftv (_, t2) =  ftv t2

instance Substitutable a => Substitutable [a] where
  apply = map . apply
  ftv   = foldr (Set.union . ftv) Set.empty

instance Substitutable TEnv where
  apply s (TypeEnv env) = TypeEnv $ Map.map (apply s) env
  ftv (TypeEnv env) = ftv $ Map.elems env

-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------
inferProgram:: TEnv -> Program a -> Either PTypeError ([Constraint], (Scheme, Scheme))
inferProgram env = runInfer env . inferProg env

inferExpr :: TEnv -> Expr a -> Either PTypeError ([Constraint], (Scheme, Scheme))
inferExpr env = runInfer env . infer env

runInfer :: TEnv -> Infer (Subst, [Constraint], PType) -> Either PTypeError ([Constraint], (Scheme, Scheme))
runInfer env m = case evalState (runExceptT m) initInfer of
  Left err  -> Left err
  Right (_, c, t) -> Right $ simpleClose env c t
-- Right (c, (Forall [] [] t, Forall [] [] t))
--  Right $ simpleClose env c t
closeOver :: (Subst, [Constraint], PType) -> Scheme
closeOver (sub, _, ty) = normalize sc
  where sc = generalize mempty (apply sub ty)

filterConstraint :: Set.Set TVar -> Constraint -> Bool
filterConstraint ftvs ("eq", PArr (TVar t) (TVar s)) = t /= s
filterConstraint ftvs (_, ty)  = any (occursCheck ty) ftvs

lcg :: [Scheme] -> Infer PType
lcg schemes = do
  tv1 <- fresh
  tv2 <- fresh
  tv3 <- fresh
  return (tv1 `PArr` tv2 `PArr` tv3)

-- TODO implement
satisfiable :: TEnv -> [Constraint] -> Bool
satisfiable env ((v, ty):r) = satisfiable env r
satisfiable env [] = True

findResolvableCons :: TEnv -> [Constraint] -> Subst
findResolvableCons env [] = emptySubst
findResolvableCons env@(TypeEnv e) (("eq", PArr (TVar t) (TVar s)):r) =
  if t == s then  findResolvableCons env r else Subst $ Map.singleton t (TVar s)
findResolvableCons env@(TypeEnv e) (("eq", PArr (TVar t) t2):r) =
  Subst $ Map.singleton t t2
findResolvableCons env@(TypeEnv e) (("eq", PArr _ t2):r) = findResolvableCons env r
findResolvableCons env@(TypeEnv e) ((var, ty):r) = case getResType ty of
  Nothing -> findResolvableCons env r
  Just tvar -> case Map.lookup var e of
    Nothing -> error "Variable not in type env"
    Just schemes -> Subst $ Map.singleton tvar (getResCon (unpackScheme (head (filter (tyMatch ty . unpackScheme) schemes))))


reduceAlph :: Subst -> Set.Set TVar -> Set.Set TVar
reduceAlph (Subst s) alph = foldl (flip Set.delete) alph (Map.keys s)

isTVar :: PType -> Bool
isTVar (TVar _) = True
isTVar _ = False
reduction :: TEnv -> Set.Set TVar -> [Constraint] -> PType -> (Set.Set TVar, [Constraint], PType)
reduction env alph et p = if null s
  then (alph, et, p)
  else reduction env nalph n_et (apply (Subst s) p)
  where (Subst s) = findResolvableCons env et
        nalph = reduceAlph (Subst s) alph
        n_et = filter (filterConstraint nalph) (apply (Subst s) et)

getResType :: PType -> Maybe TVar
getResType (PArr (TVar _) _) = Nothing
getResType (PArr _ t2) = getResType t2
getResType (TVar t) = Just t
getResType _ = Nothing

getResCon :: PType -> PType
getResCon (PArr (TVar _) _) = error "rescon"
getResCon (PArr _ t2) = getResCon t2
getResCon (TVar t) =  error "rescon"
getResCon t = t

unpackScheme :: Scheme -> PType
unpackScheme (Forall _ _ ty) = ty

simpleClose :: TEnv -> [Constraint] -> PType -> ([Constraint], (Scheme, Scheme))
simpleClose env cons ty = (cons', (Forall (Set.toList alph) cons ty, Forall (Set.toList nalph) cons'' nty))
  where alph = Set.difference (Set.union (ftv cons) (ftv ty))  (ftv env)
        (nalph, ncons, nty) = reduction env alph cons ty
        cons'' = filter (filterConstraint nalph) ncons
        cons' = if null (ftv env)
                then
                   if satisfiable env ncons
                      then []
                      else error "non satisfiable constraint set"
                else ncons

extend :: TEnv -> (Var, Scheme) -> TEnv
extend (TypeEnv env) (x, s) = TypeEnv $ Map.insertWith (++) x [s] env

typeof :: TEnv -> Var -> Maybe [Scheme]
typeof (TypeEnv env) name = Map.lookup name env

tyMatch :: PType -> PType -> Bool
tyMatch (l `PArr` r) (l' `PArr` r') = if not (l == l') then False else tyMatch r r'
tyMatch (TVar t) t2 = True

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

instantiate ::  Scheme -> Infer ([Constraint], PType)
instantiate (Forall as cs t) = do
  as' <- mapM (const fresh) as
  let s = Subst $ Map.fromList $ zip as as'
  return (apply s cs,apply s t)
  
generalize :: TEnv -> PType -> Scheme
generalize env t  = Forall as [] t
    where as = Set.toList $ ftv t `Set.difference` ftv env

lookupEnv :: TEnv -> Var -> Infer (Subst, [Constraint], PType)
lookupEnv (TypeEnv env) x =
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable (show x)
    Just [s] -> do (cs, t) <- instantiate s
                   return (emptySubst, cs, t)
    Just s -> do t <- lcg s
                 return (emptySubst, [(x, t)], t)

applyOpArg :: TEnv -> Expr a -> Subst -> [Constraint] -> PType -> Infer (Subst, [Constraint], PType)
applyOpArg env expr s1 cs1 t1 = do
  (s2, cs2, t2) <- infer (apply s1 env) expr
  tv1 <- fresh
  s3       <- unify (apply s2 t1) (PArr t2 tv1)
  return (s3 `compose` s2 `compose` s1,
    apply (s3 `compose` s2) cs1 ++ apply s3 cs2,
    apply s3 tv1)

applyOpTy :: TEnv -> PType -> Subst -> [Constraint] -> PType -> Infer (Subst, [Constraint], PType)
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
fst3 :: (Subst, [Constraint], PType) -> Subst
fst3 (x, _, _) = x
snd3 :: (Subst, [Constraint], PType) -> [Constraint]
snd3 (_, x, _) = x
trd3 :: (Subst, [Constraint], PType) -> PType
trd3 (_, _, x) = x

makeEqConstraint :: PType -> PType -> (Var, PType)
makeEqConstraint t1 t2 = ("eq", PArr t1 t2)
inferProg :: TEnv -> Program a -> Infer (Subst, [Constraint], PType)
inferProg env (Program decls _ expr) = do
  -- init type variable for all function decls beforehand so we can build constraints for
  -- calls between these functions
  tv_rev <- freshVars (length decls) []
  let tvs = reverse tv_rev
  -- env building with (name, scheme) for infer methods
  let func_tvs = zip (map fst decls) (map (Forall [] []) tvs)
  let fenv = foldl extend env func_tvs
  -- infer the type and constraints of the declaration expressions
  cts <- mapM ( infer fenv . snd) decls
  -- inferring the type of the top level expression
  (s1, cs1, t1) <- infer fenv expr
  -- building the constraints that the built type variables of the functions equal
  -- the inferred function type
  let tcs =  zipWith makeEqConstraint tvs (map trd3 cts)
  -- combine all constraints
  -- ++ tcs
  return (s1, cs1 ++ concatMap snd3 cts ++ tcs  , t1)

infer :: TEnv -> Expr a -> Infer (Subst, [Constraint], PType)
infer env expr = case expr of

  ThetaI _ a i  -> return (emptySubst, [], Deterministic)
  Subtree _ a i  -> return (emptySubst, [], Deterministic)
  Uniform _  -> return (emptySubst, [], Integrate)
  Normal _  -> return (emptySubst, [], Integrate)
  Constant _ val  -> return (emptySubst, [], Deterministic)

  PlusF _ e1 e2 -> do
    (s1, cs1, t1) <- lookupEnv env "+"
    (s2, cs2, t2) <- applyOpArg env e1 s1 cs1 t1
    applyOpArg env e2 s2 cs2 t2

  PlusI _ e1 e2 -> do
    (s1, cs1, t1) <- lookupEnv env "+"
    (s2, cs2, t2) <- applyOpArg env e1 s1 cs1 t1
    applyOpArg env e2 s2 cs2 t2

  MultF _ e1 e2 -> do
      (s1, cs1, t1) <- lookupEnv env "+"
      (s2, cs2, t2) <- applyOpArg env e1 s1 cs1 t1
      applyOpArg env e2 s2 cs2 t2
      
  MultI _ e1 e2 -> do
      (s1, cs1, t1) <- lookupEnv env "+"
      (s2, cs2, t2) <- applyOpArg env e1 s1 cs1 t1
      applyOpArg env e2 s2 cs2 t2

  GreaterThan _ e1 e2 -> do
      (s1, cs1, t1) <- lookupEnv env ">="
      (s2, cs2, t2) <- applyOpArg env e1 s1 cs1 t1
      applyOpArg env e2 s2 cs2 t2


  Call _ name -> do
      (s1, cs, t1) <- lookupEnv env name
      return (s1, cs, t1)

  Null _ -> return (emptySubst, [], Deterministic)

  Cons _ e1 e2 -> do
    (s1, cs1, t1) <- lookupEnv env ">="
    (s2, cs2, t2) <- applyOpArg env e1 s1 cs1 t1
    applyOpArg env e2 s2 cs2 t2

  IfThenElse _ cond tr fl -> do
    (s1, cs1, t1) <- lookupEnv env ">="
    (s2, cs2, t2) <- applyOpArg env cond s1 cs1 t1
    (s3, cs3, t3) <- applyOpArg env tr s2 cs2 t2

    (s4, cs4, t4) <- lookupEnv env ">="
    (s5, cs5, t5) <- applyOpTy env t3 (s4 `compose` s3) (cs3 ++ cs4) t4
    applyOpArg env fl s5 cs5 t5

normalize :: Scheme -> Scheme
normalize (Forall _ c body) = Forall (map snd ord) (normcs c) (normtype body)
  where
    ord = zip (nub $ fvcs c ++ fv body ) (map TV letters)

    fv (TVar a)   = [a]
    fv (PArr a b) = fv a ++ fv b
    fv Deterministic = []
    fv Integrate = []
    fv Bottom = []

    fvcs ((_, ty):b) = fv ty ++ fvcs b
    fvcs [] = []

    normcs ((var, ty):b) = (var, normtype ty): normcs b
    normcs [] = []

    normtype (PArr a b) = PArr (normtype a) (normtype b)
    normtype Deterministic = Deterministic
    normtype Integrate = Integrate
    normtype Bottom = Bottom

    normtype (TVar a)   =
      case Prelude.lookup a ord of
        Just x -> TVar x
        Nothing -> error "type variable not in signature"

