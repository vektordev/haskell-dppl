module Infer where

import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import RInfer
import PInfer2
import SPLL.Examples

createTypeInfo :: (Show a) => Expr () a -> TypeInfo
createTypeInfo _ = TypeInfo SPLL.Typing.RType.NotSetYet SPLL.Typing.PType.NotSetYet

addEmptyTypeInfoExpr :: (Show a) => Expr () a -> Expr TypeInfo a
addEmptyTypeInfoExpr = tMap createTypeInfo

addEmptyTypeInfo :: (Show a) => Program () a -> Program TypeInfo a
addEmptyTypeInfo = tMapProg createTypeInfo

addTypeInfo :: (Show a) => Program () a -> Program TypeInfo a
addTypeInfo = addPTypeInfo . addRTypeInfo . addEmptyTypeInfo 

addRTypeInfoOnly :: (Show a) => Program () a -> Program TypeInfo a
addRTypeInfoOnly =  addRTypeInfo . addEmptyTypeInfo
