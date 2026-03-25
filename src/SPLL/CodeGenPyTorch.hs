{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

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
import SPLL.Lang.Lang (constructVList, multiValueToValueList)
import Control.Monad.State (StateT (runStateT), MonadState (get, put), MonadTrans (lift))
import Utils (Supply, demandUniqueNumber, evalSupply)

--TODO: On the topic of memoization: Ideally we would want to optimize away redundant calls within a loop.
-- e.g. in MNist-Addition

--TODO: Recursive calls should be phrased as self.forward rather than (modulename).forward.

-- Expected format format of ThetaTrees:
--    ThetaTree = ([Double], [ThetaTree])

type GlobalStorage = StateT ([(MultiValue, String)], [String])
type VariableSupply = Supply
type GlobalVariableSupply a = GlobalStorage VariableSupply a

addOrGetFromGlobalStorage :: MultiValue -> GlobalVariableSupply String
addOrGetFromGlobalStorage mv = do
  (globalStorage, callables) <- get
  case lookup mv globalStorage of
    Nothing -> do
      varID <- lift demandUniqueNumber
      let varName = "_globalMulti" ++ show varID
      put ((mv, varName):globalStorage, callables)
      return varName
    Just var -> return var

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
pyOps x = error $ "Operator has no infix representation: " ++ show x

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
pyVal (VEither (Left a)) = "Left(" ++ pyVal a ++ ")"
pyVal (VEither (Right a)) = "Right(" ++ pyVal a ++ ")"
pyVal (VThetaTree tt) = pyValTree tt
  where pyValTree (ThetaTree val trees) = "([" ++ intercalate ", " (map show val) ++ "], [" ++ intercalate ", " (map pyValTree trees) ++ "])"
pyVal (VADT cName params) = cName ++ "(" ++ intercalate ", " (map pyVal params) ++ ")"
pyVal (VAny) = "'ANY'"
pyVal x = error ("unknown pyVal for " ++ show x)

pyMultiVal :: MultiValue -> String
pyMultiVal (MultiDiscretes vals) = "(\"D\", [" ++ intercalate ", " (map (pyVal . valueToIR) vals) ++ "])"
pyMultiVal (MultiTuple l r) = "(\"T\", (" ++ pyMultiVal l ++ ", " ++ pyMultiVal r ++ ")"
pyMultiVal (MultiEither l r) = "(\"E\", (" ++ pyMultiVal l ++ ", " ++ pyMultiVal r ++ ")"
pyMultiVal (MultiADT constrs) = "(\"A\", [" ++ intercalate ", " (map (\(cName, fields) -> 
  "(" ++ cName ++ ", [" ++ intercalate ", " (map pyMultiVal fields) ++ "])"
  ) constrs) ++ "])"

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
    let lut = envToLUT env ++ stdLib
        callableNames = [ fromMaybe (n ++ "_gen") (lookup (n ++ "_gen") lut)
                        | IRFunGroup{groupName=n, genFun=Just (e, _)} <- funcs
                        , null (fst (unwrapLambdas e)) ]
    in if genBoil then
      ["from pythonLib import *",
      "import functools",
      "import math",
      "from torch.nn import Module", ""] ++
      generateADTClasses adts ++
      concatMap (generateClass lut callableNames) funcs ++
      ["", "# Example Initialization"] ++
      generateInitializations env
    else
      concatMap (generateClass lut callableNames) funcs


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
generateADTClasses decls = concatMap generateADTClass (concatMap constructors decls)

generateADTClass :: ADTConstructorDecl -> [String]
generateADTClass (name, fields) =
  -- Class declaration
  ["class " ++ name ++ ":"]++
  indentOnce (
    -- Constructor
    ("def __init__(self, " ++ intercalate ", " fieldNames ++ "):") :
    case fieldNames of
      [] -> indentOnce ["pass"]
      fieldNames -> indentOnce (
        map (\f -> "self." ++f ++ " = " ++ f) fieldNames ++
        ["self._fields = [" ++ intercalate ", " fieldNames ++ "]"])
  ) ++ [""] ++
  indentOnce (
    "def __eq__(self, other):":
      indentOnce (
        ("if not isinstance(other, " ++ name ++ "): return False"):
        map (\f -> "if not eq(self." ++ f ++ ", other." ++ f ++ "): return False") fieldNames ++
        ["return True"]
      )
  ) ++ [""] ++
  -- Is function
  ["def is" ++ name ++ "(x):"] ++
  indentOnce ["return isinstance(x, " ++ name ++ ")"] ++
  -- Field acceessors
  concatMap (\f ->
    ("def " ++ f ++ "(x):") :
    indentOnce ["return x." ++ f]
  ) fieldNames
  where fieldNames = map fst fields

generateClass :: [(String, String)] -> [String] -> IRFunGroup -> [String]
generateClass lut callableNames (IRFunGroup name gen prob integ doc) = let
  funcStringFromMaybe name func = case func of
    Just a -> generateFunction True (name, replaceCallsDecl a)
    Nothing -> return []
  ((i, p, g), (globalVars, _)) = evalSupply $ runStateT (do
    i' <- funcStringFromMaybe "integrate" integ
    p' <- funcStringFromMaybe "forward" prob
    g' <- funcStringFromMaybe "generate" gen
    return (i', p', g')) ([], callableNames)
  commentLine = "# " ++ doc
  initLine = "class " ++ onHead toUpper name ++ "(Module):"
  globalVarDecls = map (\(mv, name)-> name ++ " = " ++ pyMultiVal mv) globalVars
  funcs = i ++ [""] ++ p ++ [""] ++ g
  replaceCallsDecl (e, d) = (irMap (replaceCalls lut) e, d)
  in commentLine:initLine:indentOnce globalVarDecls ++ indentOnce funcs

generateFunction :: Bool -> (String, IRFunDecl) -> GlobalVariableSupply [String]
generateFunction classFunction (name, (expr, doc)) = do
  let (args, reducedExpr) = unwrapLambdas expr
  let args' = if classFunction then "self":args else args
  let l1 = "def " ++ name ++ "(" ++ intercalate ", " args' ++ "):"
  block <- generateStatementBlock reducedExpr
  let docLine = "# " ++ doc
  return $ [docLine, l1] ++ indentOnce block

unwrapLambdas :: IRExpr -> ([String], IRExpr)
unwrapLambdas (IRLambda name rest) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

generateStatementBlock :: IRExpr -> GlobalVariableSupply [String]
generateStatementBlock (IRLetIn name x body) = do
  s1 <- generateLetInStatement name x
  s2 <- generateStatementBlock body
  return (s1 ++ s2)
generateStatementBlock (IRIf cond left right) = do
  cCond  <- generateExpression cond
  cLeft  <- generateStatementBlock left
  cRight <- generateStatementBlock right
  let l1 = "if " ++ cCond ++ ":"
      l2 = "else:"
  return ([l1] ++ indentOnce cLeft ++ [l2] ++ indentOnce cRight)
generateStatementBlock expr = do
  e <- generateExpression expr
  return ["return " ++ e]


generateLetInStatement :: String -> IRExpr -> GlobalVariableSupply [String]
generateLetInStatement name lmd@(IRLambda _ _) =
  generateFunction False (name, (lmd, "Inner function: " ++ name))
generateLetInStatement name (IRIf cond left right) = do
  c         <- generateExpression cond
  leftStmts <- generateLetInStatement name left
  rightStmts<- generateLetInStatement name right
  return (["if " ++ c ++ ":"] ++ indentOnce leftStmts ++ ["else:"] ++ indentOnce rightStmts)
generateLetInStatement name x = do
  v <- generateExpression x
  return [name ++ " = " ++ v]

generateExpression :: IRExpr -> GlobalVariableSupply String
generateExpression (IRIf cond left right) = do
  l <- generateExpression left
  c <- generateExpression cond
  r <- generateExpression right
  return ("(" ++ l ++ " if " ++ c ++ " else " ++ r ++ ")")
generateExpression (IROp OpApprox left right) = do
  l <- generateExpression left
  r <- generateExpression right
  return ("isclose(" ++ l ++ ", " ++ r ++ ")")
generateExpression (IROp op left right) = do
  l <- generateExpression left
  r <- generateExpression right
  return ("((" ++ l ++ ") " ++ pyOps op ++ " (" ++ r ++ "))")
generateExpression (IRUnaryOp op expr) = do
  e <- generateExpression expr
  return (pyUnaryOps op ++ "(" ++ e ++ ")")
generateExpression (IRTheta x i) = do
  sx <- generateExpression x
  return ("(" ++ sx ++ ")[0][" ++ show i ++ "]")
generateExpression (IRSubtree x i) = do
  sx <- generateExpression x
  return ("(" ++ sx ++ ")[1][" ++ show i ++ "]")
generateExpression (IRConst v) =
  return (pyVal v)
generateExpression (IRCons hd tl) = do
  h <- generateExpression hd
  t <- generateExpression tl
  return ("ConsInferenceList(" ++ h ++ ", " ++ t ++ ")")
generateExpression (IRElementOf el lst) = do
  e <- generateExpression el
  l <- generateExpression lst
  return ("(" ++ e ++ " in " ++ l ++ ")")
generateExpression (IRTCons fs sn) = do
  f <- generateExpression fs
  s <- generateExpression sn
  return ("T(" ++ f ++ ", " ++ s ++ ")")
generateExpression (IRHead x) = do
  sx <- generateExpression x
  return ("(" ++ sx ++ ")[0]")
generateExpression (IRTail x) = do
  sx <- generateExpression x
  return ("(" ++ sx ++ ")[1:]")
generateExpression (IRMap f x) = do
  ff <- generateExpression f
  xx <- generateExpression x
  return ("mapList(" ++ ff ++ ", " ++ xx ++ ")")
generateExpression (IRTFst x) = do
  sx <- generateExpression x
  return ("(" ++ sx ++ ")[0]")
generateExpression (IRTSnd x) = do
  sx <- generateExpression x
  return ("(" ++ sx ++ ")[1]")
generateExpression (IRLeft x) = do
  sx <- generateExpression x
  return ("Left(" ++ sx ++ ")")
generateExpression (IRRight x) = do
  sx <- generateExpression x
  return ("Right(" ++ sx ++ ")")
generateExpression (IRFromLeft x) = do
  sx <- generateExpression x
  return ("fromLeft(" ++ sx ++ ")")
generateExpression (IRFromRight x) = do
  sx <- generateExpression x
  return ("fromRight(" ++ sx ++ ")")
generateExpression (IRIsLeft x) = do
  sx <- generateExpression x
  return ("isinstance(" ++ sx ++ ", Left)")
generateExpression (IRIsRight x) = do
  sx <- generateExpression x
  return ("isinstance(" ++ sx ++ ", Right)")
generateExpression (IRDensity dist x) = do
  sx <- generateExpression x
  return ("density_" ++ show dist ++ "(" ++ sx ++ ")")
generateExpression (IRCumulative dist x) = do
  sx <- generateExpression x
  return ("cumulative_" ++ show dist ++ "(" ++ sx ++ ")")
generateExpression (IRSample IRNormal) =
  return "randn()"
generateExpression (IRSample IRUniform) =
  return "rand()"
generateExpression (IRVar name) = do
  (_, callables) <- get
  return $ if name `elem` callables then "(" ++ name ++ ")()" else name
generateExpression expr@(IRLambda _ _) =
  generateLambdaExpression expr
generateExpression expr@(IRApply _ _) = do
  let (fn, args) = collectApplyChain expr
  fn' <- generateExpression fn
  args' <- mapM generateExpression args
  return ("(" ++ fn' ++ ")(" ++ intercalate ", " args' ++ ")")
generateExpression (IREnumSum name enumRange expr) = do
  e <- generateExpression expr
  varName <- addOrGetFromGlobalStorage enumRange
  return ("sum(map((lambda " ++ name ++ ": " ++ e ++ "), multiValueToValueList(self." ++ varName ++ ")))")
generateExpression (IRIsPossible multiVal expr) = do
  e <- generateExpression expr
  varName <- addOrGetFromGlobalStorage multiVal
  return ("isPossible(self." ++ varName ++ ", " ++ e ++ ")")
generateExpression (IRIndex lst idx) = do
  l <- generateExpression lst
  i <- generateExpression idx
  return ("(" ++ l ++ ")[" ++ i ++ "]")
generateExpression (IRLetIn name val body) = do
  v <- generateExpression val
  b <- generateExpression body
  return ("((" ++ name ++ ":=" ++ v ++ "), " ++ b ++ ")[1]")
generateExpression (IRError e) =
  return ("throw(\"" ++ e ++ "\")")
generateExpression x =
  error ("Unknown expression in PyTorch codegen: " ++ show x)

collectApplyChain :: IRExpr -> (IRExpr, [IRExpr])
collectApplyChain (IRApply f arg) = let (fn, args) = collectApplyChain f in (fn, args ++ [arg])
collectApplyChain expr = (expr, [])

generateLambdaExpression :: IRExpr -> GlobalVariableSupply String
generateLambdaExpression expr = do
  let (names, rest) = getLambdaNames expr
  body <- generateExpression rest
  return ("(lambda " ++ intercalate ", " names ++ ": " ++ body ++ ")")

getLambdaNames :: IRExpr -> ([String], IRExpr)
getLambdaNames (IRLambda n body) = (n:names, rest)
  where (names, rest) = getLambdaNames body
getLambdaNames x = ([], x)