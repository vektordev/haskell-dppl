module SPLL.Typing.Infer where

import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Typing.RInfer
import SPLL.Typing.PInfer2
import SPLL.Typing.Witnessing

data CompileError = RErr RTypeError | PErr PTypeError deriving (Show)

wrapRErr :: Either RTypeError a -> Either CompileError a
wrapRErr (Left err) = Left (RErr err)
wrapRErr (Right x) = Right x

wrapPErr :: Either PTypeError a -> Either CompileError a
wrapPErr (Left err) = Left (PErr err)
wrapPErr (Right x) = Right x

infer :: (Show a) => Program a -> Either CompileError (Program a)
infer p = do
  x <- wrapRErr $ tryAddRTypeInfo (addEmptyTypeInfo p)
  y <- wrapPErr $ tryAddPTypeInfo x
  return $ addWitnessesProg y

inferNoWit :: (Show a) => Program a -> Either CompileError (Program a)
inferNoWit p = do
  x <- wrapRErr $ tryAddRTypeInfo (addEmptyTypeInfo p)
  wrapPErr $ tryAddPTypeInfo x


createTypeInfo :: (Show a) => Expr a -> TypeInfo a
createTypeInfo _ = makeTypeInfo

addEmptyTypeInfoExpr :: (Show a) => Expr a -> Expr a
addEmptyTypeInfoExpr = tMap createTypeInfo

addEmptyTypeInfo :: (Show a) => Program a -> Program a
addEmptyTypeInfo = tMapProg createTypeInfo

addTypeInfo :: (Show a) => Program a -> Program a
addTypeInfo = addPTypeInfo . addRTypeInfo . addEmptyTypeInfo 

addRTypeInfoOnly :: (Show a) => Program a -> Program a
addRTypeInfoOnly =  addRTypeInfo . addEmptyTypeInfo
