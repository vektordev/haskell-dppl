module SPLL.CodeGenJulia (
  generateFunctions
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import Data.List (intercalate)
import SPLL.Lang.Types
import Data.Foldable

--TODO: On the topic of memoization: Ideally we would want to optimize away redundant calls within a loop.
-- e.g. in MNist-Addition

-- Expected format format of ThetaTrees:
--    ThetaTree = ([Double], [ThetaTree])

filet :: [a] -> [a]
filet = init . tail

wrap :: String -> [String] -> String -> [String]
wrap hd [singleline] tl = [hd ++ singleline ++ tl]
wrap hd block tl = (hd ++ head block) : indentOnce (filet block ++ [last block ++ tl])
wrap _ [] _ = undefined

indentOnce :: [String] -> [String]
indentOnce = map ("  " ++)

juliaOps :: Operand -> String
juliaOps OpPlus = "+"
juliaOps OpMult = "*"
juliaOps OpGreaterThan = ">"
juliaOps OpLessThan = "<"
juliaOps OpDiv = "/"
juliaOps OpSub = "-"
juliaOps OpOr = "||"
juliaOps OpAnd = "&&"
juliaOps OpEq = "=="
juliaOps x = error ("Unknown Julia operator: " ++ show x)

juliaUnaryOps :: UnaryOperand -> String
juliaUnaryOps OpNeg = "-"
juliaUnaryOps OpExp = "exp"
juliaUnaryOps OpAbs = "abs"
juliaUnaryOps OpNot = "!"
juliaUnaryOps OpLog = "log"
juliaUnaryOps OpSign = "sign"
juliaUnaryOps OpIsAny = "isAny"
juliaUnaryOps x = error ("Unknown Julia operator: " ++ show x)

juliaVal :: IRValue -> String
juliaVal (VList xs) = "[" ++ intercalate "," (map juliaVal (toList xs)) ++ "]"
juliaVal (VInt i) = show i
juliaVal (VFloat f) = show f
juliaVal (VBool f) = if f then "true" else "false"
juliaVal (VEither (Left a)) = "(false, " ++ juliaVal a ++ ", nothing)"
juliaVal (VEither (Right a)) = "(true, nothing, " ++ juliaVal a ++ ")"
juliaVal VAny = "\"ANY\""
juliaVal x = error ("unknown juliaVal for " ++ show x)

unlinesTrimLeft :: [String] -> String
unlinesTrimLeft = intercalate "\n"

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs

generateFunctions :: [(String, IRExpr)] -> [String]
generateFunctions = concatMap generateFunction

generateFunction :: (String, IRExpr) -> [String]
generateFunction (name, expr) = let
  (args, reducedExpr) = unwrapLambdas expr
  l1 = "function " ++ name ++ "(" ++ intercalate ", " args ++ ")"
  block = generateStatementBlock reducedExpr
  lEnd = "end"
  in [l1] ++ indentOnce block ++ [lEnd]

unwrapLambdas :: IRExpr -> ([String], IRExpr)
unwrapLambdas (IRLambda name rest) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

generateStatementBlock :: IRExpr -> [String]
generateStatementBlock (IRLetIn name lmd@(IRLambda _ _) body) = generateFunction (name, lmd) ++ generateStatementBlock body
generateStatementBlock (IRLetIn name val body) = (name ++ " = " ++ generateExpression val):generateStatementBlock body
generateStatementBlock (IRIf cond left right) = let
  cCond = generateExpression cond
  cLeft = generateStatementBlock left
  cRight = generateStatementBlock right
  l1 = "if " ++ cCond
  l2 = "else"
  l3 = "end"
  in [l1] ++ indentOnce cLeft ++ [l2] ++ indentOnce cRight ++ [l3]
generateStatementBlock expr = ["return " ++ generateExpression expr]

generateExpression :: IRExpr -> String
generateExpression (IRIf cond left right ) = "(" ++ generateExpression cond ++ " ? " ++ generateExpression left ++ " : " ++ generateExpression right ++ ")"
generateExpression (IROp op left right) = "((" ++ generateExpression left ++ ") " ++ juliaOps op ++ " (" ++ generateExpression right ++ "))"
generateExpression (IRUnaryOp op expr) = juliaUnaryOps op ++ "(" ++ generateExpression expr ++ ")"
generateExpression (IRTheta expr i) = "(" ++ generateExpression expr ++ ")[1][" ++ show (i + 1) ++ "]"
generateExpression (IRSubtree expr i) = "(" ++ generateExpression expr ++ ")[2][" ++ show (i + 1) ++ "]"
generateExpression (IRConst v) = juliaVal v
generateExpression (IRCons hd tl) = "hcat(" ++ generateExpression hd ++ ", " ++ generateExpression tl ++ ")"
generateExpression (IRElementOf el lst) = "(" ++ generateExpression el ++ " in " ++ generateExpression lst ++ ")"
generateExpression (IRTCons fs sn) = "(" ++ generateExpression fs ++ ", " ++ generateExpression sn ++ ")"
generateExpression (IRHead x) = "(" ++ generateExpression x ++ ")[1]"
generateExpression (IRTail x) = "(" ++ generateExpression x ++ ")[2:end]"
generateExpression (IRTFst x) = "(" ++ generateExpression x ++ ")[1]"
generateExpression (IRTSnd x) = "(" ++ generateExpression x ++ ")[2]"
generateExpression (IRLeft x) = "(false, " ++ generateExpression x ++ ", nothing)"
generateExpression (IRRight x) = "(true, nothing, " ++ generateExpression x ++ ")"
generateExpression (IRFromLeft x) = "(" ++ generateExpression x ++ ")[2]"
generateExpression (IRFromRight x) = "(" ++ generateExpression x ++ ")[3]"
generateExpression (IRIsLeft x) = "!(" ++ generateExpression x ++ ")[1]"
generateExpression (IRIsRight x) = "(" ++ generateExpression x ++ ")[1]"
generateExpression (IRDensity dist x) = "density_" ++ show dist ++ "(" ++ generateExpression x ++ ")"
generateExpression (IRCumulative dist x) = "cumulative_" ++ show dist ++ "(" ++ generateExpression x ++ ")"
generateExpression (IRSample IRNormal) = "randn()"
generateExpression (IRSample IRUniform) = "rand()"
generateExpression (IRVar name) = name
generateExpression (IRLambda name x) = "(" ++ name  ++ " -> " ++ generateExpression x ++ ")"
-- Julia cannot really do partial application. This is a workaround
generateExpression (IRApply f val) = "((args...) -> " ++ generateExpression f ++ "(" ++ generateExpression val ++ ", args...))"
generateExpression expr@(IRInvoke _) = generateInvokeExpression expr
generateExpression (IREnumSum name enumRange expr) = "sum(map((" ++ name ++ " -> " ++ generateExpression expr ++ "), " ++ juliaVal enumRange ++ "))"
generateExpression (IREvalNN name arg) = name ++ "(" ++ generateExpression arg ++ ")"
generateExpression (IRIndex lst idx) = "(" ++ generateExpression lst ++ ")[" ++ generateExpression idx ++ " + 1]"
generateExpression (IRLetIn name val body) = "(let " ++ name ++ " = " ++ generateExpression val ++ "; " ++ generateExpression body ++ ")"
generateExpression x = error ("Unknown expression in Julia codegen: " ++ show x)

generateInvokeExpression :: IRExpr -> String
-- IRInvoke is always the outermost expression of the block compiled here. Compile the function and the parameters first, then end it all with an ")"
generateInvokeExpression (IRInvoke expr) = generateInvokeExpression expr ++ ")"
-- Not that the parameters are in reverse order. The innermost parameter is applied first
-- We have more parameters
generateInvokeExpression (IRApply f@(IRApply _ _) val) = generateInvokeExpression f ++ ", " ++ generateExpression val
-- This is the last parameter
generateInvokeExpression (IRApply f val) = generateInvokeExpression f ++ generateExpression val
-- No more parameters, compile the fucntion
generateInvokeExpression expr = "(" ++ generateExpression expr ++ ")("
