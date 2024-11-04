module SPLL.CodeGenJulia (
  generateCode
, generateFunctions
) where
  
import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import Data.List (intercalate)
import SPLL.Lang.Types

--TODO: On the topic of memoization: Ideally we would want to optimize away redundant calls within a loop.
-- e.g. in MNist-Addition

-- Expected format format of ThetaTrees:
--    ThetaTree = ([Double], [ThetaTree])

filet :: [a] -> [a]
filet = init . tail

wrap :: String -> [String] -> String -> [String]
wrap hd [singleline] tl = [hd ++ singleline ++ tl]
wrap hd (block) tl = [hd ++ head block] ++ indentOnce (filet block ++ [last block ++ tl])
wrap _ [] _ = undefined

wrapMultiBlock :: [String] -> [[String]] -> [String]
wrapMultiBlock [prefix, suffix] [block] = wrap prefix block suffix
wrapMultiBlock (prefix:infixes) (block:blocks) = if length block == 1 then y else x
  where
    rest = wrapMultiBlock infixes blocks
    x = [prefix ++ head block] ++ indentOnce (filet block ++ [last block ++ head rest]) ++ tail rest
    y = [prefix ++ head block ++ head rest] ++ tail rest
wrapMultiBlock x y = error "uneven list lengths in wrapMultiBlock"

indentOnce :: [String] -> [String]
indentOnce = map ("  " ++)

spicyHead :: [a] -> a
spicyHead [x] = x
spicyHead [] = error "empty list in head"
spicyHead x = error "overfull list in head"

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

juliaVal :: IRValue -> String
juliaVal (VList xs) = "[" ++ (intercalate "," $ map juliaVal xs) ++ "]"
juliaVal (VInt i) = show i
juliaVal (VFloat f) = show f
juliaVal (VBool f) = if f then "true" else "false"
juliaVal x = error ("unknown juliaVal for " ++ show x)

unlinesTrimLeft :: [String] -> String
unlinesTrimLeft = intercalate "\n"

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = (f x : xs)

generateFunctions :: [(String, IRExpr)] -> [String]
generateFunctions = concatMap generateFunction

generateFunction :: (String, IRExpr) -> [String]
generateFunction (name, expr) = let
  (args, reducedExpr) = unwrapLambdas expr
  l1 = "function " ++ name ++ "(" ++ intercalate ", " ("thetas" : args) ++ ")"
  block = wrap "return " (generateCode reducedExpr) ""
  lEnd = "end"
  in [l1] ++ indentOnce block ++ [lEnd] 
  
unwrapLambdas :: IRExpr -> ([String], IRExpr)
unwrapLambdas (IRLambda name rest) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

generateCode :: IRExpr -> [String]
generateCode (IRIf cond left right ) = let
  [cCond] = generateCode cond
  cLeft = generateCode left
  cRight = generateCode right
  l1 = "if " ++ cCond
  l2 = "else"
  l3 = "end"
  in [l1] ++ indentOnce cLeft ++ [l2] ++ indentOnce cRight ++ [l3]
generateCode (IROp op left right) = lines ("(" ++ unlinesTrimLeft (generateCode left) ++ " " ++ juliaOps op ++ " " ++ unlinesTrimLeft (generateCode right) ++ ")")
generateCode (IRUnaryOp OpExp expr) = wrap "exp(" (generateCode expr) ")"
generateCode (IRUnaryOp OpLog expr) = wrap "log(" (generateCode expr) ")"
generateCode (IRUnaryOp OpNeg expr) = wrap "-(" (generateCode expr) ")"
generateCode (IRUnaryOp OpNot expr) = wrap "!(" (generateCode expr) ")"
generateCode (IRUnaryOp OpAbs expr) = wrap "abs(" (generateCode expr) ")"
generateCode (IRTheta expr i) = wrap "(" (generateCode expr) (")[1][" ++ show (i + 1) ++ "]")
generateCode (IRSubtree expr i) = wrap "(" (generateCode expr) (")[2][" ++ show (i + 1) ++ "]")
generateCode (IRConst val) = [juliaVal val]
generateCode (IRCons hd tl) = wrapMultiBlock ["hcat(", ", ", ")"] [generateCode hd, generateCode tl]
generateCode (IRTCons t1 t2) = wrapMultiBlock ["(", ", ", ")"] [generateCode t1, generateCode t2]
generateCode (IRHead lst) = wrap "(" (generateCode lst) ")[1]"
generateCode (IRTail lst) = wrap "(" (generateCode lst) ")[2:end]"
generateCode (IRElementOf ele lst) = wrapMultiBlock ["(", " in ", ")"] [generateCode ele, generateCode lst]
generateCode (IRTFst t) = wrap "(" (generateCode t) ")[1]"
generateCode (IRTSnd t) = wrap "(" (generateCode t) ")[2]"
generateCode (IRSample IRNormal) = ["randn()"]
generateCode (IRSample IRUniform) = ["rand()"]
generateCode (IRLetIn name bind into) = let --TODO letins within method calls
  l1 = "("
  bindCode = generateCode bind
  --assignment = if length bindCode == 1 then [name ++ " = " ++ spicyHead (generateCode bind)] else undefined
  assignment = onHead (\line -> name ++ " = " ++ line) bindCode
  rest = generateCode into
  block = indentOnce (assignment ++ rest)
  lend = ")"
  in [l1] ++ block ++ [lend]
generateCode (IRVar var) = [var]
generateCode (IRDensity dist subexpr) = let
  subexprCode = generateCode subexpr
  l1 = "density_" ++ show dist ++ "(" ++ spicyHead subexprCode
  center = tail $ init subexprCode
  l3 = last subexprCode ++ ")"
  in if length subexprCode > 1
    then [l1] ++ center ++ [l3]
    else ["density_" ++ show dist ++ "(" ++ spicyHead subexprCode ++ ")"]
generateCode (IRCumulative dist subexpr) = let
  subexprCode = generateCode subexpr
  l1 = "cumulative_" ++ show dist ++ "(" ++ spicyHead subexprCode
  center = tail $ init subexprCode
  l3 = last subexprCode ++ ")"
  in if length subexprCode > 1
    then [l1] ++ center ++ [l3]
    else ["cumulative_" ++ show dist ++ "(" ++ spicyHead subexprCode ++ ")"]
--sum $ map (\name -> subexpr name) enumRange
generateCode (IREnumSum name enumRange subexpr) = let
  function = wrap ("sum(map((" ++ name ++ " -> ") (generateCode subexpr) ("), " ++ juliaVal enumRange ++ "))")
  --l2 = "sum(map(" ++ function ++ ", " ++ juliaVal enumRange ++ "))"
  in function
generateCode (IRIndex arrExpr indexExpr) = let
  arrCode = spicyHead $ generateCode arrExpr
  indexCode = spicyHead $ generateCode indexExpr
  in [arrCode ++ "[1 + " ++ indexCode ++ "]"]
generateCode (IREvalNN funcName argExpr) = [funcName ++ "(" ++ spicyHead (generateCode argExpr) ++ ")"]
generateCode (IRCall funcName argExprs) = [funcName ++ "(" ++ (intercalate "," (map (spicyHead . generateCode) argExprs)) ++ ")"]
generateCode (IRApply lambda argExpr) = [spicyHead (generateCode lambda) ++ "(" ++ spicyHead (generateCode argExpr) ++ ")"]
generateCode (IRLambda varName expr) = ["(" ++ varName ++ " -> " ++ spicyHead (generateCode expr) ++ ")"]
generateCode (IRReturning expr) = generateCode expr
generateCode x = error ("No Julia CodeGen for IR: " ++ show x)
