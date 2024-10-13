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

infer :: Program -> Either CompileError Program
infer p = do
  x <- wrapRErr $ tryAddRTypeInfo (addEmptyTypeInfo p)
  y <- wrapPErr $ tryAddPTypeInfo x
  return $ addWitnessesProg y

inferNoWit :: Program -> Either CompileError Program
inferNoWit p = do
  x <- wrapRErr $ tryAddRTypeInfo (addEmptyTypeInfo p)
  wrapPErr $ tryAddPTypeInfo x


createTypeInfo :: Expr -> TypeInfo
createTypeInfo _ = makeTypeInfo

addEmptyTypeInfoExpr :: Expr -> Expr
addEmptyTypeInfoExpr = tMap createTypeInfo

addEmptyTypeInfo :: Program -> Program
addEmptyTypeInfo = tMapProg createTypeInfo

addTypeInfo :: Program -> Program
addTypeInfo = addPTypeInfo . addRTypeInfo . addEmptyTypeInfo 

addRTypeInfoOnly :: Program -> Program
addRTypeInfoOnly =  addRTypeInfo . addEmptyTypeInfo
