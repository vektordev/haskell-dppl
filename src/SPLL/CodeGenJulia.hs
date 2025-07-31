module SPLL.CodeGenJulia (
  generateFunctions,
  juliaVal
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import Data.List (intercalate)
import SPLL.Lang.Types
import Data.Foldable
import Data.Maybe (fromMaybe)
import Data.Functor ((<&>))

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
juliaVal (VList EmptyList) = "EmptyInferenceList()"
juliaVal (VList AnyList) = "AnyInferenceList()"
juliaVal (VList (ListCont x xs)) = "ConsInferenceList(" ++ juliaVal x ++ ", " ++ juliaVal (VList xs) ++ ")"
juliaVal (VInt i) = show i
juliaVal (VFloat f) = show f
juliaVal (VBool f) = if f then "true" else "false"
juliaVal (VTuple a b) = "T(" ++ juliaVal a ++ ", " ++ juliaVal b ++ ")"
juliaVal (VEither (Left a)) = "(false, " ++ juliaVal a ++ ", nothing)"
juliaVal (VEither (Right a)) = "(true, nothing, " ++ juliaVal a ++ ")"
juliaVal (VThetaTree tt) = juliaValTree tt
  where juliaValTree (ThetaTree val trees) = "([" ++ intercalate ", " (map show val) ++ "], [" ++ intercalate ", " (map juliaValTree trees) ++ "])"
juliaVal VAny = "\"ANY\""
juliaVal x = error ("unknown juliaVal for " ++ show x)

unlinesTrimLeft :: [String] -> String
unlinesTrimLeft = intercalate "\n"

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs

generateADTClasses :: [ADTDecl] -> [String]
generateADTClasses decls = concatMap generateADTClass (concatMap snd decls)

generateADTClass :: ADTConstructorDecl -> [String]
generateADTClass (name, fields) =
  -- Struct declaration
  ["struct " ++ name]++
  indentOnce (
    indentOnce fieldNames
  ) ++
  ["end"] ++
  -- Is function
  ["is" ++ name ++ "(x) = x isa " ++ name] ++
  -- Field acceessors
  concatMap (\f ->
    ("function " ++ f ++ "(x :: " ++ name ++ ")") :
    indentOnce ["return x." ++ f] ++
    ["end"]
  ) fieldNames
  where fieldNames = map fst fields

generateFunctions :: IREnv -> [String]
generateFunctions (IREnv funcs adts) = 
  generateADTClasses adts ++
  concatMap generateFunctionGroup funcs

generateFunctionGroup :: IRFunGroup -> [String]
generateFunctionGroup IRFunGroup {groupName=n, genFun=g, probFun=p, integFun=i, groupDoc=doc} = 
  [ "# === Function Group " ++ n ++ " ===\n# " ++ doc] ++ 
  genF n "_gen" g ++
  fromMaybe [] (p <&> genF n "_prob") ++
  fromMaybe [] (i <&> genF n "_integ")
  where genF name suffix (e, d) = generateFunction (name ++ suffix) d e

generateFunction :: String -> String -> IRExpr -> [String]
generateFunction name doc expr = let
  (args, reducedExpr) = unwrapLambdas expr
  docLine = "# " ++ doc
  l1 = "function " ++ name ++ "(" ++ intercalate ", " args ++ ")"
  block = generateStatementBlock reducedExpr
  lEnd = "end"
  in [docLine, l1] ++ indentOnce block ++ [lEnd]

unwrapLambdas :: IRExpr -> ([String], IRExpr)
unwrapLambdas (IRLambda name rest) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

generateStatementBlock :: IRExpr -> [String]
generateStatementBlock (IRLetIn name lmd@(IRLambda _ _) body) = generateFunction name ("Inner function: " ++ name) lmd ++ generateStatementBlock body
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
generateExpression (IROp OpApprox left right) = "isclose(" ++ generateExpression left ++ ", " ++ generateExpression right ++ ")"
generateExpression (IROp op left right) = "((" ++ generateExpression left ++ ") " ++ juliaOps op ++ " (" ++ generateExpression right ++ "))"
generateExpression (IRUnaryOp op expr) = juliaUnaryOps op ++ "(" ++ generateExpression expr ++ ")"
generateExpression (IRTheta expr i) = "(" ++ generateExpression expr ++ ")[1][" ++ show (i + 1) ++ "]"
generateExpression (IRSubtree expr i) = "(" ++ generateExpression expr ++ ")[2][" ++ show (i + 1) ++ "]"
generateExpression (IRConst v) = juliaVal v
generateExpression (IRCons hd tl) = "prepend(" ++ generateExpression hd ++ ", " ++ generateExpression tl ++ ")"
generateExpression (IRElementOf el lst) = "(" ++ generateExpression el ++ " in " ++ generateExpression lst ++ ")"
generateExpression (IRTCons fs sn) = "T(" ++ generateExpression fs ++ ", " ++ generateExpression sn ++ ")"
generateExpression (IRHead x) = "head(" ++ generateExpression x ++ ")"
generateExpression (IRTail x) = "tail(" ++ generateExpression x ++ ")"
generateExpression (IRMap f x) = "mapList(" ++ generateExpression f ++ ", " ++ generateExpression x ++ ")"
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
generateExpression (IRLetIn name val body) = "(let " ++ name ++ " = " ++ generateExpression val ++ "; " ++ generateExpression body ++ "end)"
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
