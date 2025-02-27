module SPLL.CodeGenPyTorch (
  generateFunctions
) where
  
import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import Data.List (intercalate, isSuffixOf, nub, find)
import Data.Char (toUpper, toLower)
import Data.Maybe (fromJust, fromMaybe)
import Debug.Trace (trace)

--TODO: On the topic of memoization: Ideally we would want to optimize away redundant calls within a loop.
-- e.g. in MNist-Addition

--TODO: Recursive calls should be phrased as self.forward rather than (modulename).forward.

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
indentOnce = map ("    " ++)

spicyHead :: [a] -> a
spicyHead [x] = x
spicyHead [] = error "empty list in head"
spicyHead x = error "overfull list in head"

pyOps :: Operand -> String
pyOps OpPlus = "+"
pyOps OpMult = "*"
pyOps OpGreaterThan = ">"
pyOps OpLessThan = "<"
pyOps OpDiv = "/"
pyOps OpSub = "-"
pyOps OpOr = "or"
pyOps OpAnd = "and"
pyOps OpEq = "=="

pyUnaryOps :: UnaryOperand -> String
pyUnaryOps OpNeg = "-"
pyUnaryOps OpExp = "math.exp"
pyUnaryOps OpAbs = "abs"
pyUnaryOps OpNot = "not"
pyUnaryOps OpLog = "math.log"
--pyUnaryOps OpSign = "sign"
--pyUnaryOps OpIsAny = "isAny"

pyVal :: IRValue -> String
pyVal (VList xs) = "[" ++ (intercalate "," $ map pyVal xs) ++ "]"
--pyVal (VList EmptyList) = "EmptyInferenceList()"
--pyVal (VList AnyList) = "AnyInferenceList()"
--pyVal (VList (ListCont x xs)) = "ConsInferenceList(" ++ pyVal x ++ ", " ++ pyVal (VList xs) ++ ")"
pyVal (VInt i) = show i
pyVal (VFloat f) = show f
pyVal (VBool f) = if f then "True" else "False"
pyVal x = error ("unknown pyVal for " ++ show x)

unlinesTrimLeft :: [String] -> String
unlinesTrimLeft = intercalate "\n"

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs

onLast :: (a -> a) -> [a] -> [a]
onLast f [x] = [f x]
onLast f (x:xs) = x : onLast f xs

generateFunctions :: [(String, IRExpr)] -> [String]
--generateFunctions defs | trace (show defs) False = undefined
--contrary to the julia backend, we want to aggregate gen and prob into one classes. Ugly implementation, but it'll do for now.
generateFunctions defs =
  let
    getName str
      | "_prob" `isSuffixOf` str = iterate init str !! 5
      | "_integ" `isSuffixOf` str = iterate init str !! 6
      | otherwise = iterate init str !! 4
    names = nub $ map (getName . fst) defs
    lut = [(name ++ "_gen", onHead toLower name ++ ".generate") | name <- names]
       ++ [(name ++ "_prob", onHead toLower name ++ ".forward") | name <- names]
       ++ [(name ++ "_integ", onHead toLower name ++ ".integrate") | name <- names] ++ stdLib
    findDef name suffix = find (\def -> fst def == (name ++ suffix)) defs
    getDef name suffix = case findDef name suffix of
      Nothing -> Nothing
      Just a -> Just $ irMap (replaceCalls lut) $ snd a
    groups = [(name, getDef name "_gen", getDef name "_prob", getDef name "_integ")| name <- names]
  in
    concatMap generateClass groups ++ ["", "# Example Initialization"] ++ [onHead toLower name ++ " = " ++ onHead toUpper name ++ "()" | name <- names]

stdLib :: [(String, String)]
stdLib = [("in", "contains")]

replaceCalls :: [(String, String)] -> IRExpr -> IRExpr
replaceCalls lut (IRVar name) = IRVar (fromMaybe name $ lookup name lut)
replaceCalls _ other = other

generateClass :: (String, Maybe IRExpr, Maybe IRExpr, Maybe IRExpr) -> [String]
generateClass (name, gen, prob, integ) = let
  funcStringFromMaybe name func = case func of
    Just a -> generateFunction (name, a)
    Nothing -> []
  i = funcStringFromMaybe "integrate" integ
  p = funcStringFromMaybe "forward" prob
  g = funcStringFromMaybe "generate" gen
  initLine = "class " ++ onHead toUpper name ++ "(Module):"
  funcs = i ++ [""] ++ p ++ [""] ++ g
  in [initLine] ++ indentOnce funcs

generateFunction :: (String, IRExpr) -> [String]
generateFunction (name, expr) = let
  (args, reducedExpr) = unwrapLambdas expr
  l1 = "def " ++ name ++ "(" ++ intercalate ", " ("self" : args) ++ "):"
  block = generateStatementBlock reducedExpr
  --TODO Use returnize to find all exprs to attach returns to.
  in [l1] ++ indentOnce block

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
  l1 = "if " ++ cCond ++ ":"
  l2 = "else:"
  in [l1] ++ indentOnce cLeft ++ [l2] ++ indentOnce cRight
generateStatementBlock expr = ["return " ++ generateExpression expr]

generateExpression :: IRExpr -> String
generateExpression (IRIf cond left right) = "(" ++ generateExpression left ++ " if " ++ generateExpression cond ++ " else " ++ generateExpression right ++ ")"
generateExpression (IROp op left right) = "((" ++ generateExpression left ++ ") " ++ pyOps op ++ " (" ++ generateExpression right ++"))" 
generateExpression (IRUnaryOp op expr) = pyUnaryOps op ++ "(" ++ generateExpression expr ++ ")"
generateExpression (IRTheta x i) = "(" ++ generateExpression x ++ ")[0][" ++ show i ++ "]" 
generateExpression (IRSubtree x i) = "(" ++ generateExpression x ++ ")[1][" ++ show i ++ "]" 
generateExpression (IRConst v) = pyVal v
generateExpression (IRCons hd tl) = "ConsInferenceList(" ++ generateExpression hd ++ ", " ++ generateExpression tl ++ ")"
generateExpression (IRElementOf el lst) = "(" ++ generateExpression el ++ " in " ++ generateExpression lst ++ ")"
generateExpression (IRTCons fs sn) = "(" ++ generateExpression fs ++ ", " ++ generateExpression sn ++ ")"
generateExpression (IRHead x) = "(" ++ generateExpression x ++ ")[0]" 
generateExpression (IRTail x) = "(" ++ generateExpression x ++ ")[1:]" 
generateExpression (IRTFst x) = "(" ++ generateExpression x ++ ")[0]" 
generateExpression (IRTSnd x) = "(" ++ generateExpression x ++ ")[1]" 
generateExpression (IRDensity dist x) = "density_" ++ show dist ++ "(" ++ generateExpression x ++ ")"
generateExpression (IRCumulative dist x) = "cumulative_" ++ show dist ++ "(" ++ generateExpression x ++ ")"
generateExpression (IRSample IRNormal) = "randn()"
generateExpression (IRSample IRUniform) = "rand()"
generateExpression (IRVar name) = name
generateExpression (IRLambda name x) = "(lambda " ++ name  ++ ": " ++ generateExpression x ++ ")"
generateExpression (IRApply f val) = "functools.partial(" ++ generateExpression f ++ ", " ++ generateExpression val ++ ")"
generateExpression expr@(IRInvoke _) = generateInvokeExpression expr
generateExpression (IREnumSum name enumRange expr) = "sum(map((lambda " ++ name ++ ": " ++ generateExpression expr ++ "), " ++ pyVal enumRange ++ "))"
generateExpression (IREvalNN name arg) = name ++ "(" ++ generateExpression arg ++ ")"
generateExpression (IRIndex lst idx) = "(" ++ generateExpression lst ++ ")[" ++ generateExpression idx ++ "]" 
-- I personally hate this code. I constructs a tuple with an assignment expression in the first element and discards the first element
generateExpression (IRLetIn name val body) = "((" ++ name ++ ":=" ++ generateExpression val ++ "), " ++ generateExpression body ++ ")[1]"
generateExpression x = error ("Unknown expression in PyTorch codegen: " ++ show x)

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