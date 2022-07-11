module SPLL.CodeGenJulia (
  generateCode
, generateFunctions
) where
  
import SPLL.IntermediateRepresentation
import Lang (Value)
import Data.List (intercalate)

indentOnce :: [String] -> [String]
indentOnce = map ("  " ++)

juliaOps :: Operand -> String
juliaOps OpPlus = "+"
juliaOps OpMult = "*"
juliaOps OpGreaterThan = ">="
juliaOps OpDiv = "/"
juliaOps OpSub = "-"

juliaVal :: Value a -> String
juliaVal = undefined

unlinesTrimLeft :: [String] -> String
unlinesTrimLeft = intercalate "\n"

generateFunctions :: (Show a) => [(String, IRExpr a)] -> [String]
generateFunctions = concatMap generateFunction

generateFunction :: (Show a) => (String, IRExpr a) -> [String]
generateFunction (name, expr) = let
  (args, reducedExpr) = unwrapLambdas expr
  l1 = "function " ++ name ++ "(" ++ intercalate ", " ("thetas" : args) ++ ")"
  block = generateCode reducedExpr
  lEnd = "end"
  in [l1] ++ indentOnce block ++ [lEnd] 
  
unwrapLambdas :: IRExpr a -> ([String], IRExpr a)
unwrapLambdas (IRLambda name rest) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

generateCode :: (Show a) => IRExpr a -> [String]
generateCode (IRIf cond left right ) = let
  [cCond] = generateCode cond
  cLeft = generateCode left
  cRight = generateCode right
  l1 = "if " ++ cCond
  l2 = "elseif"
  l3 = "end"
  in [l1] ++ indentOnce cLeft ++ [l2] ++ indentOnce cRight ++ [l3]
generateCode (IROp op left right) = lines ("(" ++ unlinesTrimLeft (generateCode left) ++ " " ++ juliaOps op ++ " " ++ unlinesTrimLeft (generateCode right) ++ ")")
generateCode (IRTheta i) = ["thetas[" ++ show i ++ "]"]
generateCode (IRConst val) = [juliaVal val]
generateCode (IRCons hd tl) = undefined
generateCode (IRSample IRNormal) = ["randn()"]
generateCode (IRSample IRUniform) = ["rand()"]
generateCode (IRLetIn name bind into) = let 
  l1 = "("
  bindCode = generateCode bind
  assignment = if length bindCode == 1 then [name ++ " = " ++ head (generateCode bind)] else undefined
  rest = generateCode into
  block = indentOnce (assignment ++ rest)
  lend = ")"
  in [l1] ++ block ++ [lend]
generateCode (IRVar var) = [var]
generateCode (IRDensity dist subexpr) = let
  subexprCode = generateCode subexpr
  l1 = "density_" ++ show dist ++ "(" ++ head subexprCode
  center = tail $ init subexprCode
  l3 = last subexprCode ++ ")"
  in if length subexprCode > 1
    then [l1] ++ center ++ [l3]
    else ["density_" ++ show dist ++ "(" ++ head subexprCode ++ ")"]
generateCode x = error ("No Julia CodeGen for IR: " ++ show x)