{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module SPLL.Typing.Typing where

import SPLL.Lang
import SPLL.Typing.RType
import SPLL.Typing.PType

import Data.Maybe
import Control.Monad.Reader
import Control.Monad.Except

-- Because Env will be polluted by local symbols as we evaluate, we need to reset when calling functions.
-- Therefore, we define that all functions must exist in the global namespace.
-- That way, it is sufficient to carry only the global namespace as reset point.
-- local functions are in principle possible, but they need to carry their own environment with them,
-- e.g. by expanding Env to be of [(String, Env x a, Expr x a)], where [] indicates a shorthand for the global scope.
type Env x a = [(String, Expr x a)]
type Check a = ExceptT TypeError (Reader (Env () a))

data TypeError = Mismatch RType RType
               deriving (Show, Eq)

getR :: Expr TypeInfo a -> RType
getR expr = r
  where
    TypeInfo r _ = getTypeInfo expr

getP :: Expr TypeInfo a -> PType
getP expr = p
  where
    TypeInfo _ p = getTypeInfo expr
getPW :: Expr TypeInfoWit a -> PType
getPW expr = p
  where
    TypeInfoWit _ p _ = getTypeInfo expr
getRW :: Expr TypeInfoWit a -> RType
getRW expr = r
  where
    TypeInfoWit r _ _  = getTypeInfo expr

rIntersect :: RType -> RType -> Maybe RType
--here be all cases where types are "equal" but one is more strict
-- or where we can match unequal types anyway.
rIntersect l@(RConstraint _ _ retT) r@(RConstraint _ _ retT2) =
  if retT == retT2 && isJust sectType
  -- We need to worry about recursive Constraint types.
  then Just $ buildConstraints (getConstraints l ++ getConstraints r) $ fromJust sectType --Just $ RConstraint name constraint $ RConstraint name2 constraint2 retT2
  else Nothing
    where
      getFinal (RConstraint _ _ b) = getFinal b
      getFinal other = other
      getConstraints (RConstraint x y ys) = (x, y) : getConstraints ys
      getConstraints _ = []
      buildConstraints [] finalR = finalR
      buildConstraints ((a,b):cs) finalR = RConstraint a b (buildConstraints cs finalR)
      leftFinal = getFinal retT
      rightFinal = getFinal retT2
      sectType = rIntersect leftFinal rightFinal
rIntersect left (RConstraint name constraint retT) =
  if isNothing sectType
  then Nothing
  else Just $ RConstraint name constraint $ fromJust sectType
    where sectType = rIntersect left retT
rIntersect (RConstraint name constraint retT) right =
  if isNothing sectType
  then Nothing
  else Just $ RConstraint name constraint $ fromJust sectType
    where sectType = rIntersect right retT
--TODO: Validate the next two lines
rIntersect (RIdent name) t = Just $ RConstraint name t t
rIntersect t (RIdent name) = Just $ RConstraint name t t
rIntersect (ListOf x) NullList = Just $ ListOf x
rIntersect NullList (ListOf x) = Just $ ListOf x
rIntersect left right = if left == right then Just left else Nothing

matchRExpr :: Expr () a -> Expr () a -> Check a RType
matchRExpr e1 e2 = do
  e1R <- inferR e1
  e2R <- inferR e2
  matchRType e1R e2R

matchRType :: RType -> RType -> Check a RType
matchRType t1 t2 =
  if isNothing intersection
  then throwError $ Mismatch t1 t2
  else return $ fromJust intersection
    where intersection = rIntersect t1 t2

matchTwoReturnThird :: RType -> RType -> RType -> Check a RType
matchTwoReturnThird a b ret =
  if isNothing intersection
  then throwError $ Mismatch a b
  else return ret
    where intersection = rIntersect a b

--TODO: if Expr is Let_in or otherwise affects Env.
typeCheckExpr :: Env () a -> Expr () a -> Expr TypeInfo a
typeCheckExpr env = tMap (mkTypeInfo2 env)

mkTypeInfo2 :: Env () a -> Expr () a -> TypeInfo
mkTypeInfo2 env expr =
  case mkTypeInfo env expr of
    Left err -> error $ show err
    Right result -> result

mkTypeInfo :: Env () a -> Expr () a -> Either TypeError TypeInfo
mkTypeInfo env expr =
  do
    pType <- runReader (runExceptT (inferP expr)) env
    rType <- runReader (runExceptT (inferR expr)) env
    return $ TypeInfo rType pType

inferR :: Expr () a -> Check a RType
inferR (IfThenElse () cond left right) = do
  condR <- inferR cond
  ret <- matchRExpr left right
  matchTwoReturnThird condR TBool ret
  --if condR /= TBool
  --then throwError $ Mismatch condR TBool
  --else matchRExpr left right
inferR (GreaterThan () left right) = do
  e1R <- inferR left
  e2R <- inferR right
  matchTwoReturnThird e1R e2R TBool
  --if e1R /= e2R
  --then throwError $ Mismatch e1R e2R
  --else return TBool
inferR (ThetaI () _) = return TFloat
inferR (Uniform ()) = return TFloat
inferR (Normal ()) = return TFloat
inferR (Constant () val) = return $ getRType val
--inferR (Constant () (VFloat _)) = return TFloat
--inferR (Constant () (VBool _)) = return TBool
--inferR (Constant () (VList xs)) = return $ ListOf xs
inferR (Mult () e1 e2) = matchRExpr e1 e2
inferR (Plus () e1 e2) = matchRExpr e1 e2
inferR (Null ()) = return NullList
inferR (Cons () headX tailX) = do
  tHead <- inferR headX
  tTail <- inferR tailX
  case tTail of
    ListOf innerType -> liftM ListOf $ matchRType innerType tHead
    NullList -> return (ListOf tHead)
    _ -> matchRType tTail (ListOf tHead)
inferR (Call () name) = return $ RIdent name

--TODO: Find a way to statically align the result of inferP with the constraints of the likelihood function.
inferP :: Expr () a -> Check a PType
inferP (IfThenElse _ cond left right) = do
  condP <- inferP cond
  leftP <- inferP left
  rightP <- inferP right
  -- assumption: cond is always binomial - this should follow from typing rules.
  return $ downgrade condP $ downgrade leftP rightP
inferP (GreaterThan _ left right) = do
  leftP <- inferP left
  rightP <- inferP right
  return $ downgrade leftP rightP
inferP (ThetaI _ _) = return Deterministic
inferP (Constant _ _) = return Deterministic
inferP (Uniform _) = return Integrate
inferP (Normal _) = return Integrate
inferP (Mult _ left right) = do
  leftP <- inferP left
  rightP <- inferP right
  if upgrade leftP rightP == Deterministic
  then return $ downgrade leftP rightP
  -- we do not know how to integrate over a product
  else return Chaos
inferP (Plus _ left right) = do
  leftP <- inferP left
  rightP <- inferP right
  if upgrade leftP rightP == Deterministic
  then return $ downgrade leftP rightP
  -- we do not know how to integrate over a sum
  else return Chaos
inferP (Null _) = return Deterministic
inferP (Cons _ headX tailX) = do
  -- TODO: Assumes independence. Invalid if there exists x elem Env that is used in head and tail.
  headP <- inferP headX
  tailP <- inferP tailX
  return $ downgrade headP tailP
inferP (Call _ name) = return $ PIdent name [(Deterministic, Deterministic), (Integrate, Integrate), (Chaos, Chaos)]--TODO: here there be dragons
--inferP (LetIn _ name assignment inExpr) = inferP inExpr
--TODO: Arg needs to make sure the variable has proper type, same as let_in
--inferP (Arg _ name inExpr) = inferP inExpr
--inferP (CallArg _ name withExpr) = return $ PIdent name [(Deterministic, Deterministic), (Integrate, Integrate), (Chaos, Chaos)]


progToEnv :: Program x a -> Env x a
progToEnv (Program funcs main_expr) = ("main", main_expr): funcs