{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module SPLL.Typing.Typing (
  TypeError,
  TypeInfo(..),
  ChainName,
  Tag(..),
  CType(..),
  makeTypeInfo,
  setRType,
  setPType,
  setCType,
  setWitnessedVars,
  setChainName,
  setTags,
)where

import SPLL.Lang.Types
import SPLL.Lang.Lang
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

setRType :: TypeInfo -> RType -> TypeInfo
setRType t rt = t {rType = rt}

setPType :: TypeInfo -> PType -> TypeInfo
setPType t pt = t {pType = pt}

setCType :: TypeInfo -> CType -> TypeInfo
setCType t ct = t {cType = ct}

setDerivingHornClause :: TypeInfo -> HornClause -> TypeInfo
setDerivingHornClause t dhc = t {derivingHornClause = Just dhc}

setWitnessedVars :: TypeInfo -> WitnessedVars -> TypeInfo
setWitnessedVars t wit = t {witnessedVars = wit}

setChainName:: TypeInfo -> ChainName -> TypeInfo
setChainName t name = t {chainName = name}

setTags:: TypeInfo -> [Tag] -> TypeInfo
setTags t tgs = t {tags = tgs}

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

{--
autoProg p = Program (map (\(n, f) -> (n, autoExpr f)) (functions p)) (map autoNeuralDecl (neurals p))

autoExpr :: (Reifies s Tape) => Expr -> Expr
autoExpr e = exprMap auto e

autoNeuralDecl :: NeuralDecl -> NeuralDecl 
autoNeuralDecl (n, rt, t) = (n, rt, autoTag t)

--TODO: Maybe we should genericize this to be (a -> b) -> TI a -> TI b
autoTypeInfo :: TypeInfo -> TypeInfo
autoTypeInfo t = t {tags = Prelude.map autoTag (tags t), cType = autoCType (cType t), derivingHornClause = do
  hc <- derivingHornClause t
  return (autoHornClause hc)}

autoHornClause ::HornClause -> HornClause
autoHornClause (cn, hc, inv) =  (map (\(cn1, ct) -> (cn1, autoCType ct)) cn, map (\(cn1, ct) -> (cn1, autoCType ct)) hc, inv)

autoCType :: CType -> CType
autoCType (CConstrainedTo a b) = CConstrainedTo (auto a) (auto b)
autoCType CDeterministic = CDeterministic
autoCType CInferDeterministic = CInferDeterministic
autoCType CBottom = CBottom
autoCType CNotSetYet = CNotSetYet


autoTag :: Tag -> Tag
autoTag (EnumRange (a, b))= EnumRange (autoVal a, autoVal b)
autoTag (EnumList l) = EnumList (Prelude.map autoVal l)
autoTag (Alg a) = Alg a
autoTag _ = error "Failed to convert to auto tag"


autoVal :: Value -> Value
autoVal (VBool x) = VBool x
autoVal (VFloat y) = VFloat (auto y)
autoVal (VList xs) = VList (Prelude.map autoVal xs)
autoVal (VTuple x1 x2) = VTuple (autoVal x1) (autoVal x2)
autoVal (VInt x) = VInt x
autoVal (VSymbol x) = VSymbol x
autoVal _ = error "Failed to convert to auto value"
-}