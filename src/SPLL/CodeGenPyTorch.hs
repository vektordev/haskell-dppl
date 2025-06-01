module SPLL.CodeGenPyTorch (
  generateFunctions,
  pyVal
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import Data.List (intercalate, isSuffixOf, nub, find)
import Data.Char (toUpper, toLower)
import Data.Maybe (fromJust, fromMaybe)
import Debug.Trace (trace, traceShowId)
import Data.Foldable

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
pyUnaryOps OpSign = "sign"
pyUnaryOps OpIsAny = "isAny"

pyVal :: IRValue -> String
pyVal (VList EmptyList) = "EmptyInferenceList()"
pyVal (VList AnyList) = "AnyInferenceList()"
pyVal (VList (ListCont x xs)) = "ConsInferenceList(" ++ pyVal x ++ ", " ++ pyVal (VList xs) ++ ")"
pyVal (VInt i) = show i
pyVal (VFloat f) = show f
pyVal (VBool f) = if f then "True" else "False"
pyVal (VTuple a b) = "T(" ++ pyVal a ++ ", " ++ pyVal b ++ ")"
pyVal (VEither (Left a)) = "(False, " ++ pyVal a ++ ", None)"
pyVal (VEither (Right a)) = "(True, None, " ++ pyVal a ++ ")"
pyVal (VThetaTree tt) = pyValTree tt
  where pyValTree (ThetaTree val trees) = "([" ++ intercalate ", " (map show val) ++ "], [" ++ intercalate ", " (map pyValTree trees) ++ "])"
pyVal (VAny) = "'ANY'"
pyVal x = error ("unknown pyVal for " ++ show x)

unlinesTrimLeft :: [String] -> String
unlinesTrimLeft = intercalate "\n"

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs

onLast :: (a -> a) -> [a] -> [a]
onLast f [x] = [f x]
onLast f (x:xs) = x : onLast f xs

generateFunctions :: Bool -> IREnv -> [String]
--generateFunctions defs | trace (show defs) False = undefined
--contrary to the julia backend, we want to aggregate gen and prob into one classes. Ugly implementation, but it'll do for now.
generateFunctions genBoil env@(IREnv funcs adts) =
{-  let
    getName str
      | "_prob" `isSuffixOf` str = iterate init str !! 5
      | "_integ" `isSuffixOf` str = iterate init str !! 6
      | otherwise = iterate init str !! 4
    names = nub $ map (getName . fst3) defs
    lut = [(name ++ "_gen", onHead toLower name ++ ".generate") | name <- names]
       ++ [(name ++ "_prob", onHead toLower name ++ ".forward") | name <- names]
       ++ [(name ++ "_integ", onHead toLower name ++ ".integrate") | name <- names] ++ stdLib
    findDef name suffix = find (\def -> fst3 def == (name ++ suffix)) defs
    getDef name suffix = case findDef name suffix of
      Nothing -> Nothing
      Just (name, doc, expr) -> Just $ (irMap (replaceCalls lut) expr, doc)
    groups = [(name, getDef name "_gen", getDef name "_prob", getDef name "_integ")| name <- names]
    fst3 (a, b, c) = a -}
    if genBoil then
      ["from pythonLib import *",
      "import functools",
      "import math",
      "from torch.nn import Module", ""] ++
      generateADTClasses adts ++ 
      concatMap (generateClass (envToLUT env)) funcs ++
      ["", "# Example Initialization"] ++
      generateInitializations env
    else
      concatMap (generateClass (envToLUT env)) funcs


stdLib :: [(String, String)]
stdLib = [("in", "contains")]

envToLUT :: IREnv -> [(String, String)]
envToLUT (IREnv funcs _) = concatMap (\IRFunGroup {groupName=n} -> [(n ++ "_gen", n ++ ".generate"), (n ++ "_prob", n ++ ".forward"), (n ++ "_integ", n ++ ".integrate")]) funcs

replaceCalls :: [(String, String)] -> IRExpr -> IRExpr
replaceCalls lut (IRVar name) = IRVar (fromMaybe name $ lookup name lut)
replaceCalls _ other = other

generateInitializations :: IREnv -> [String]
generateInitializations (IREnv funcs _) = map (\IRFunGroup {groupName=n} -> n ++ " = " ++ onHead toUpper n ++ "()") funcs

generateADTClasses :: [ADTDecl] -> [String]
generateADTClasses decls = concatMap generateADTClass (concatMap snd decls)

generateADTClass :: ADTConstructorDecl -> [String]
generateADTClass (name, fields) =
  -- Class declaration
  ["class " ++ name ++ ":"]++
  indentOnce (
    -- Constructor
    ("def __init__(self, " ++ intercalate ", " fieldNames ++ "):") :
    indentOnce (
      map (\f -> "self." ++f ++ " = " ++ f) fieldNames)
  ) ++
  -- Is function
  ["def is" ++ name ++ "(x):"] ++
  indentOnce ["return isinstance(x, " ++ name ++ ")"] ++
  -- Field acceessors
  concatMap (\f ->
    ("def " ++ f ++ "(x):") :
    indentOnce ["return x." ++ f]
  ) fieldNames
  where fieldNames = map fst fields

generateClass :: [(String, String)] -> IRFunGroup -> [String]
generateClass lut (IRFunGroup name gen prob integ doc) = let
  funcStringFromMaybe name func = case func of
    Just a -> generateFunction (name, replaceCallsDecl a)
    Nothing -> []
  i = funcStringFromMaybe "integrate" integ
  p = funcStringFromMaybe "forward" prob
  g = generateFunction ("generate", replaceCallsDecl gen)
  commentLine = "# " ++ doc
  initLine = "class " ++ onHead toUpper name ++ "(Module):"
  funcs = i ++ [""] ++ p ++ [""] ++ g
  replaceCallsDecl (e, d) = (irMap (replaceCalls lut) e, d)
  in commentLine:initLine:indentOnce funcs

generateFunction :: (String, IRFunDecl) -> [String]
generateFunction (name, (expr, doc)) = let
  (args, reducedExpr) = unwrapLambdas expr
  l1 = "def " ++ name ++ "(" ++ intercalate ", " ("self" : args) ++ "):"
  block = generateStatementBlock reducedExpr
  docLine = "# " ++ doc
  in [docLine, l1] ++ indentOnce block

unwrapLambdas :: IRExpr -> ([String], IRExpr)
unwrapLambdas (IRLambda name rest) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

generateStatementBlock :: IRExpr -> [String]
generateStatementBlock (IRLetIn name lmd@(IRLambda _ _) body) = generateFunction (name, (lmd, "Inner function: " ++ name)) ++ generateStatementBlock body
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
generateExpression (IRTCons fs sn) = "T(" ++ generateExpression fs ++ ", " ++ generateExpression sn ++ ")"
generateExpression (IRHead x) = "(" ++ generateExpression x ++ ")[0]"
generateExpression (IRTail x) = "(" ++ generateExpression x ++ ")[1:]"
generateExpression (IRTFst x) = "(" ++ generateExpression x ++ ")[0]"
generateExpression (IRTSnd x) = "(" ++ generateExpression x ++ ")[1]"
generateExpression (IRLeft x) = "(False, " ++ generateExpression x ++ ", None)"
generateExpression (IRRight x) = "(False, None, " ++ generateExpression x ++ ")"
generateExpression (IRFromLeft x) = "(" ++ generateExpression x ++ ")[1]"
generateExpression (IRFromRight x) = "(" ++ generateExpression x ++ ")[2]"
generateExpression (IRIsLeft x) = "(not(" ++ generateExpression x ++ ")[0])"
generateExpression (IRIsRight x) = "(" ++ generateExpression x ++ ")[0]"
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