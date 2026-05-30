{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE FlexibleContexts #-}

module SPLL.Typing.Typing (
  TypeError,
  TypeInfo(..),
  ChainName,
  Tag(..),
  makeTypeInfo,
  setRType,
  setPType,
  setChainName,
  setTags,
)where

import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.Typing.PType
import GHC.Records

import Data.Maybe
import Control.Monad.Reader
import Control.Monad.Except

import Numeric.AD (grad', auto)
import Numeric.AD.Internal.Reverse ( Reverse, Tape)
import Data.Reflection (Reifies)

setRType :: TypeInfo -> RType -> TypeInfo
setRType t rt = t {rType = rt}

setPType :: TypeInfo -> PType -> TypeInfo
setPType t pt = t {pType = pt}

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

