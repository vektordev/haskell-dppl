{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module SPLL.Typing.Typing (
  Env,
  TypeError,
  TypeInfo(..),
  ChainName,
  HornClause,
  Tag(..),
  CType(..),
  makeTypeInfo,
  setRType,
  setPType,
  setCType,
  setWitnessedVars,
  setChainName,
  setTags,
  progToEnv,
  autoVal,
  autoEnv,
  autoExpr
)where

import SPLL.Lang
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.InferenceRule
import GHC.Records

import Data.Maybe
import Data.Set (empty)
import Control.Monad.Reader
import Control.Monad.Except

import Numeric.AD (grad', auto)
import Numeric.AD.Internal.Reverse ( Reverse, Tape)
import Data.Reflection (Reifies)
data Tag a = EnumRange (Value a, Value a)
           | EnumList [Value a]
           | Alg InferenceRule
           deriving (Show, Eq, Ord)

type ChainName = String

-- (Set of Preconditions with CType, set of Inferable variables with attached CType, Expression this HornClause originates from with its inversion number
type HornClause a = ([(ChainName, CType a)], [(ChainName, CType a)], (ExprStub, Int))

data CType a = CDeterministic
             | CInferDeterministic
             | CConstrainedTo a a
             | CBottom
             | CNotSetYet
             deriving (Show, Eq)
           
instance Eq a => Ord (CType a) where
  compare x y = compare (rank x) (rank y)
    where
      rank CDeterministic = 10
      rank CInferDeterministic = 9
      rank (CConstrainedTo _ _) = 5
      rank CBottom = 1
      rank CNotSetYet = -1

--Do not use this constructor, use makeTypeInfo instead
data TypeInfo a = TypeInfo
  { rType :: RType
  , pType :: PType
  , cType :: CType a
  , derivingHornClause :: Maybe (HornClause a)
  , witnessedVars :: WitnessedVars
  , chainName :: ChainName
  , tags :: [Tag a]} deriving (Show, Eq, Ord)
-- only use ord instance for algorithmic convenience, not for up/downgrades / lattice work.

makeTypeInfo = TypeInfo
    { rType = SPLL.Typing.RType.NotSetYet
    , pType = SPLL.Typing.PType.NotSetYet
    , cType = CNotSetYet
    , derivingHornClause = Nothing
    , witnessedVars = empty
    , chainName = ""
    , tags = []}

setRType :: TypeInfo a -> RType -> TypeInfo a
setRType t rt = t {rType = rt}

setPType :: TypeInfo a -> PType -> TypeInfo a
setPType t pt = t {pType = pt}

setCType :: TypeInfo a -> CType a -> TypeInfo a
setCType t ct = t {cType = ct}

setDerivingHornClause :: TypeInfo a -> HornClause a -> TypeInfo a
setDerivingHornClause t dhc = t {derivingHornClause = Just dhc}

setWitnessedVars :: TypeInfo a-> WitnessedVars -> TypeInfo a
setWitnessedVars t wit = t {witnessedVars = wit}

setChainName:: TypeInfo a -> ChainName -> TypeInfo a
setChainName t name = t {chainName = name}

setTags:: TypeInfo a -> [Tag a] -> TypeInfo a
setTags t tgs = t {tags = tgs}

-- Because Env will be polluted by local symbols as we evaluate, we need to reset when calling functions.
-- Therefore, we define that all functions must exist in the global namespace.
-- That way, it is sufficient to carry only the global namespace as reset point.
-- local functions are in principle possible, but they need to carry their own environment with them,
-- e.g. by expanding Env to be of [(String, Env x a, Expr x a)], where [] indicates a shorthand for the global scope.
type Env x a = [(String, Expr x a)]
type Check a = ExceptT TypeError (Reader (Env () a))

data TypeError = Mismatch RType RType
               deriving (Show, Eq)

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

progToEnv :: Program (TypeInfo a) a -> Env (TypeInfo a) a
progToEnv (Program funcs main_expr) = ("main", main_expr): funcs

autoExpr :: (Eq a, Num a, Reifies s Tape) => Expr (TypeInfo a) a -> Expr (TypeInfo (Reverse s a)) (Reverse s a)
autoExpr e = tMap (autoTypeInfo . getTypeInfo) $ exprMap auto e

autoTypeInfo :: (Eq a, Num a, Reifies s Tape) =>TypeInfo a ->TypeInfo (Reverse s a)
autoTypeInfo t = t {tags = Prelude.map autoTag (tags t), cType = autoCType (cType t), derivingHornClause = do
  hc <- derivingHornClause t
  return (autoHornClause hc)}

autoHornClause :: (Eq a, Num a, Reifies s Tape) => HornClause a -> HornClause (Reverse s a)
autoHornClause (cn, hc, inv) =  (map (\(cn1, ct) -> (cn1, autoCType ct)) cn, map (\(cn1, ct) -> (cn1, autoCType ct)) hc, inv)

autoCType :: (Num a, Reifies s Tape) => CType a -> CType (Reverse s a)
autoCType (CConstrainedTo a b) = CConstrainedTo (auto a) (auto b)
autoCType CDeterministic = CDeterministic
autoCType CInferDeterministic = CInferDeterministic
autoCType CBottom = CBottom
autoCType CNotSetYet = CNotSetYet


autoTag :: (Num a, Reifies s Tape) => Tag a -> Tag (Reverse s a)
autoTag (EnumRange (a, b))= EnumRange (autoVal a, autoVal b)
autoTag (EnumList l) = EnumList (Prelude.map autoVal l)
autoTag (Alg a) = Alg a
autoTag _ = error "Failed to convert to auto tag"

autoEnv :: (Eq a, Num a, Reifies s Tape) => Env (TypeInfo a) a -> Env (TypeInfo (Reverse s a)) (Reverse s a)
autoEnv = Prelude.map (\ (name, expr) -> (name, autoExpr expr))

autoVal :: (Num a, Reifies s Tape) => Value a -> Value (Reverse s a)
autoVal (VBool x) = VBool x
autoVal (VFloat y) = VFloat (auto y)
autoVal (VList xs) = VList (Prelude.map autoVal xs)
autoVal (VTuple x1 x2) = VTuple (autoVal x1) (autoVal x2)
autoVal (VInt x) = VInt x
autoVal (VSymbol x) = VSymbol x
autoVal _ = error "Failed to convert to auto value"