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

