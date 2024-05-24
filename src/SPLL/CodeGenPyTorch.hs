module SPLL.CodeGenPyTorch (
  generateCode
, generateFunctions
) where
  
import SPLL.IntermediateRepresentation
import SPLL.Lang
import Data.List (intercalate, isSuffixOf, nub, find)
import Data.Char (toUpper, toLower)
import Data.Maybe (fromJust, fromMaybe)

--TODO: On the topic of memoization: Ideally we would want to optimize away redundant calls within a loop.
-- e.g. in MNist-Addition

--TODO: Recursive calls should be phrased as self.forward rather than (modulename).forward.

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
pyOps OpGreaterThan = ">="
pyOps OpDiv = "/"
pyOps OpSub = "-"
pyOps OpOr = "or"
pyOps OpAnd = "and"
pyOps OpEq = "=="

pyVal :: (Show a) => Value a -> String
pyVal (VList xs) = "[" ++ (intercalate "," $ map pyVal xs) ++ "]"
pyVal (VInt i) = show i
pyVal (VFloat f) = show f
pyVal (VBool f) = if f then "true" else "false"
pyVal x = error ("unknown pyVal for " ++ show x)

unlinesTrimLeft :: [String] -> String
unlinesTrimLeft = intercalate "\n"

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs

onLast :: (a -> a) -> [a] -> [a]
onLast f [x] = [f x]
onLast f (x:xs) = x : onLast f xs

generateFunctions :: (Show a) => [(String, IRExpr a)] -> [String]
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
       ++ [(name ++ "_integ", onHead toLower name ++ ".integral") | name <- names] ++ stdLib
    findDef name suffix = find (\def -> fst def == (name ++ suffix)) defs
    getDef name suffix = case findDef name suffix of
      Nothing -> Nothing
      Just a -> Just $ irMap (replaceCalls lut) $ snd a
    groups = [(name, getDef name "_gen", getDef name "_prob", getDef name "_integ")| name <- names]
  in
    concatMap generateClass groups

stdLib :: [(String, String)]
stdLib = [("in", "contains")]

replaceCalls :: [(String, String)] -> IRExpr a -> IRExpr a
replaceCalls lut (IRCall name args) = IRCall (fromMaybe name $ lookup name lut) args
replaceCalls lut other = other

generateClass :: (Show a ) => (String, Maybe (IRExpr a), Maybe (IRExpr a), Maybe (IRExpr a)) -> [String]
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

generateFunction :: (Show a) => (String, IRExpr a) -> [String]
generateFunction (name, expr) = let
  (args, reducedExpr) = unwrapLambdas expr
  l1 = "def " ++ name ++ "(" ++ intercalate ", " ("self" : args) ++ "):"
  block = generateCode reducedExpr "return "
  --TODO Use returnize to find all exprs to attach returns to.
  in [l1] ++ indentOnce block
  
unwrapLambdas :: IRExpr a -> ([String], IRExpr a)
unwrapLambdas (IRLambda name rest) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

generateCode :: (Show a) => IRExpr a -> String -> [String]
generateCode (IRIf cond left right) "" = wrapMultiBlock ["(", " if ", " else ", ")"] [generateCode left "", generateCode cond "", generateCode right ""]
generateCode (IRIf cond left right) bindto = let
  [cCond] = generateCode cond ""
  cLeft = generateCode left bindto
  cRight = generateCode right bindto
  l1 = "if " ++ cCond ++ ":"
  l2 = "else:"
  in [l1] ++ indentOnce cLeft ++ [l2] ++ indentOnce cRight
generateCode (IROp op left right) bindto = wrapMultiBlock [bindto ++ "(", " " ++ pyOps op ++ " ", ")"] [generateCode left "", generateCode right ""]
--generateCode (IROp op left right) bindto = lines ("(" ++ unlinesTrimLeft (generateCode left "") ++ " " ++ pyOps op ++ " " ++ unlinesTrimLeft (generateCode right "") ++ ")")
generateCode (IRUnaryOp OpNeg expr) bindto = wrap (bindto ++ "-(") (generateCode expr "") ")"
generateCode (IRUnaryOp OpNot expr) bindto = wrap (bindto ++ "not(") (generateCode expr "") ")"
generateCode (IRUnaryOp OpAbs expr) bindto = wrap (bindto ++ "abs(") (generateCode expr "") ")"
generateCode (IRTheta i) bindto = [bindto ++ "self.thetas[" ++ show i ++ "]"]
generateCode (IRConst val) bindto = [bindto ++ pyVal val]
generateCode (IRCons hd tl) bindto = wrapMultiBlock [bindto ++ "[", "] + ", ""] [generateCode hd "", generateCode tl ""]
generateCode (IRTCons t1 t2) bindto = wrapMultiBlock [bindto ++ "(", ", ", ")"] [generateCode t1 "", generateCode t2 ""]
generateCode (IRHead lst) bindto = wrap (bindto ++ "(") (generateCode lst "") ")[0]"
generateCode (IRTail lst) bindto = wrap (bindto ++ "(") (generateCode lst "") ")[1:]"
generateCode (IRTFst t) bindto = wrap (bindto ++ "(") (generateCode t "") ")[0]"
generateCode (IRTSnd t) bindto = wrap (bindto ++ "(") (generateCode t "") ")[1]"
generateCode (IRSample IRNormal) bindto = [bindto ++ "randn()"]
generateCode (IRSample IRUniform) bindto = [bindto ++ "rand()"]
generateCode (IRLetIn name bind into) bindto = let 
  l1 = "("
  bindCode = generateCode bind (name ++ " = ")
  --assignment = if length bindCode == 1 then [name ++ " = " ++ spicyHead (generateCode bind)] else undefined
  assignment = bindCode
  rest = generateCode into bindto
  block = indentOnce (assignment ++ rest)
  lend = ")"
  --in [l1] ++ block ++ [lend]
  in assignment ++ rest
generateCode (IRVar var) bindto = [bindto ++ var]
generateCode (IRDensity dist subexpr) bindto = let
  subexprCode = generateCode subexpr ""
  block = wrap (bindto ++ "density_" ++ show dist ++ "(") subexprCode ")"
  in block
generateCode (IRCumulative dist subexpr) bindto = let
  subexprCode = generateCode subexpr ""
  block = wrap (bindto ++ "cumulative_" ++ show dist ++ "(") subexprCode ")"
  in block
--sum $ map (\name -> subexpr name) enumRange
generateCode (IREnumSum name enumRange subexpr) bindto = let
  function = wrap ("sum(map((lambda " ++ name ++ ": ") (generateCode subexpr "") ("), " ++ pyVal enumRange ++ "))")
  --l2 = "sum(map(" ++ function ++ ", " ++ juliaVal enumRange ++ "))"
  in function
generateCode (IRIndex arrExpr indexExpr) bindto = let
  arrCode = spicyHead $ generateCode arrExpr ""
  indexCode = spicyHead $ generateCode indexExpr ""
  in [arrCode ++ "[" ++ indexCode ++ "]"]
generateCode (IREvalNN funcName argExpr) bindto = [funcName ++ "(" ++ spicyHead (generateCode argExpr "") ++ ")"]
generateCode (IRCall funcName argExprs) bindto = [funcName ++ "(" ++ (intercalate "," (map (\expr -> spicyHead $ generateCode expr "") argExprs)) ++ ")"]
generateCode (IRReturning expr) bindto = let
  arrCode = generateCode expr ""
  in onLast ("return " ++) arrCode
generateCode x y = error ("No PyTorch CodeGen for IR: " ++ show x)
