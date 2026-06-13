{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module SPLL.CodeGenPyTorch (
  generateFunctions,
  pyVal
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import Data.List (intercalate, isPrefixOf)
import Data.Char (toUpper)
import Data.Maybe (fromMaybe)
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

indentOnce :: [String] -> [String]
indentOnce = map ("    " ++)

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

pyDistName :: Distribution -> String
pyDistName IRNormal = "normal"
pyDistName IRUniform = "uniform"

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
pyVal VUnit = "None"
pyVal (VThetaTree tt) = pyValTree tt
  where pyValTree (ThetaTree val trees) = "([" ++ intercalate ", " (map show val) ++ "], [" ++ intercalate ", " (map pyValTree trees) ++ "])"
pyVal (VADT cName params) = cName ++ "(" ++ intercalate ", " (map pyVal params) ++ ")"
pyVal (VAny) = "'ANY'"
pyVal (VError e) = "throw(\"" ++ e ++ "\")"
pyVal x = error ("unknown pyVal for " ++ show x)

pyMultiVal :: MultiValue -> String
pyMultiVal MultiContinuous = "(\"C\", None)"
pyMultiVal (MultiDiscretes vals) = "(\"D\", [" ++ intercalate ", " (map (pyVal . valueToIR) vals) ++ "])"
pyMultiVal (MultiTuple l r) = "(\"T\", (" ++ pyMultiVal l ++ ", " ++ pyMultiVal r ++ ")"
pyMultiVal (MultiEither l r) = "(\"E\", (" ++ pyMultiVal l ++ ", " ++ pyMultiVal r ++ ")"
pyMultiVal (MultiADT constrs) = "(\"A\", [" ++ intercalate ", " (map (\(cName, fields) -> 
  "(" ++ cName ++ ", [" ++ intercalate ", " (map pyMultiVal fields) ++ "])"
  ) constrs) ++ "])"

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs

generateFunctions :: Bool -> IREnv -> [String]
--contrary to the julia backend, we want to aggregate gen and prob into one classes. Ugly implementation, but it'll do for now.
generateFunctions genBoil env@(IREnv funcs adts consts) =
    let lut = envToLUT env ++ stdLib
        callableNames = [ fromMaybe (n ++ "_gen") (lookup (n ++ "_gen") lut)
                        | IRFunGroup{groupName=n, genFun=Just (e, _)} <- funcs
                        , null (fst (unwrapLambdas e)) ]
                        -- nullary ADT constructors must be emitted as instantiations,
                        -- otherwise the bare class never compares equal to enumerated instances
                        ++ [ cName | decl <- adts, (cName, fields) <- constructors decl, null fields ]
    in if genBoil then
      ["from pythonLib import *",
      "import functools",
      "import math",
      "from torch.nn import Module", ""] ++
      generateADTClasses adts ++
      map (\(name, val) -> name ++ " = " ++ pyVal val) consts ++
      (if null consts then [] else [""]) ++
      concatMap (generateClass lut callableNames) funcs ++
      ["", "# Example Initialization"] ++
      generateInitializations env
    else
      map (\(name, val) -> name ++ " = " ++ pyVal val) consts ++
      concatMap (generateClass lut callableNames) funcs


stdLib :: [(String, String)]
stdLib = [("in", "contains")]

envToLUT :: IREnv -> [(String, String)]
envToLUT (IREnv funcs _ _) = concatMap (\IRFunGroup {groupName=n} -> [(n ++ "_gen", n ++ ".generate"), (n ++ "_prob", n ++ ".forward"), (n ++ "_integ", n ++ ".integrate"), (n ++ "_normal", n ++ ".normal_params")]) funcs

replaceCalls :: [(String, String)] -> IRExpr -> IRExpr
replaceCalls lut (IRVar name) = IRVar (fromMaybe name $ lookup name lut)
replaceCalls _ other = other

generateInitializations :: IREnv -> [String]
generateInitializations (IREnv funcs _ _) = map (\IRFunGroup {groupName=n} -> n ++ " = " ++ onHead toUpper n ++ "()") funcs

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
generateClass lut callableNames (IRFunGroup name gen prob integ encode normal doc) = let
  funcStringFromMaybe name func = case func of
    Just a -> generateFunction True (name, replaceCallsDecl a)
    Nothing -> return []
  ((i, p, g, e, n), (globalVars, _)) = evalSupply $ runStateT (do
    i' <- funcStringFromMaybe "integrate" integ
    p' <- funcStringFromMaybe "forward" prob
    g' <- funcStringFromMaybe "generate" gen
    e' <- funcStringFromMaybe "encode" encode
    n' <- funcStringFromMaybe "normal_params" normal
    return (i', p', g', e', n')) ([], callableNames)
  commentLine = "# " ++ doc
  initLine = "class " ++ onHead toUpper name ++ "(Module):"
  globalVarDecls = map (\(mv, name)-> name ++ " = " ++ pyMultiVal mv) globalVars
  funcs = i ++ [""] ++ p ++ [""] ++ g ++ [""] ++ e ++ [""] ++ n
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

-- | True when the block is exactly one if-elif-else construct with nothing after it.
-- After the else: body ends, no further top-level lines may appear.
isSingleIfBlock :: [String] -> Bool
isSingleIfBlock (l:ls) | "if " `isPrefixOf` l = afterIf ls
isSingleIfBlock _ = False

-- Scanning lines that may be elif/else or indented body after the opening if.
afterIf :: [String] -> Bool
afterIf [] = True
afterIf (l:ls)
  | "    " `isPrefixOf` l  = afterIf ls
  | "elif " `isPrefixOf` l = afterIf ls
  | l == "else:"           = afterElse ls
  | otherwise              = False   -- second if, bare assignment, etc.

-- Scanning lines inside an else: body; nothing may follow outside it.
afterElse :: [String] -> Bool
afterElse [] = True
afterElse (l:ls)
  | "    " `isPrefixOf` l = afterElse ls
  | otherwise             = False   -- anything after else body = multiple blocks

-- | Collapse `else: if` into `elif` only when the else-branch is a single if-block.
mergeElif :: [String] -> [String]
mergeElif stmts@(ifLine:rest) | "if " `isPrefixOf` ifLine && isSingleIfBlock stmts =
  ("elif " ++ drop 3 ifLine) : rest
mergeElif stmts = "else:" : indentOnce stmts

containsIf :: IRExpr -> Bool
containsIf (IRIf _ _ _)    = True
containsIf (IROp _ l r)    = containsIf l || containsIf r
containsIf (IRUnaryOp _ e) = containsIf e
containsIf (IRApply f x)   = containsIf f || containsIf x
containsIf (IRTCons f s)   = containsIf f || containsIf s
containsIf (IRTFst x)      = containsIf x
containsIf (IRTSnd x)      = containsIf x
containsIf (IRLetIn _ v b) = containsIf v || containsIf b
containsIf (IRHead x)      = containsIf x
containsIf (IRTail x)      = containsIf x
containsIf (IRLeft x)      = containsIf x
containsIf (IRRight x)     = containsIf x
containsIf (IRFromLeft x)  = containsIf x
containsIf (IRFromRight x) = containsIf x
containsIf (IRIsLeft x)    = containsIf x
containsIf (IRIsRight x)   = containsIf x
containsIf (IRDensity _ x) = containsIf x
containsIf (IRCumulative _ x) = containsIf x
containsIf (IRMap f x)     = containsIf f || containsIf x
containsIf (IRIndex l i)   = containsIf l || containsIf i
containsIf (IRCons h t)    = containsIf h || containsIf t
containsIf (IRTheta x _)   = containsIf x
containsIf (IRSubtree x _) = containsIf x
containsIf _               = False

-- | Like generateExpression, but lifts complex IRIf nodes into temp variables,
-- returning prefix statements and the resulting expression.
generateExpressionLifted :: IRExpr -> GlobalVariableSupply ([String], String)
generateExpressionLifted expr@(IRIf cond left right)
  | not (containsIf left || containsIf right) = do
      (condStmts, c) <- generateExpressionLifted cond
      l <- generateExpression left
      r <- generateExpression right
      return (condStmts, "(" ++ l ++ " if " ++ c ++ " else " ++ r ++ ")")
  | otherwise = do
      tmpId <- lift demandUniqueNumber
      let tmp = "_t" ++ show tmpId
      stmts <- generateLetInStatement tmp expr
      return (stmts, tmp)
generateExpressionLifted (IRLetIn name val body) = do
  valStmts <- generateLetInStatement name val
  (bodyStmts, bodyExpr) <- generateExpressionLifted body
  return (valStmts ++ bodyStmts, bodyExpr)
generateExpressionLifted (IROp OpApprox l r) = do
  (ls, le) <- generateExpressionLifted l
  (rs, re) <- generateExpressionLifted r
  return (ls ++ rs, "isclose(" ++ le ++ ", " ++ re ++ ")")
generateExpressionLifted (IROp op l r) = do
  (ls, le) <- generateExpressionLifted l
  (rs, re) <- generateExpressionLifted r
  return (ls ++ rs, "(" ++ le ++ " " ++ pyOps op ++ " " ++ re ++ ")")
generateExpressionLifted (IRUnaryOp op e) = do
  (ss, se) <- generateExpressionLifted e
  return (ss, pyUnaryOps op ++ "(" ++ se ++ ")")
generateExpressionLifted (IRTFst x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx ++ "[0]")
generateExpressionLifted (IRTSnd x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx ++ "[1]")
generateExpressionLifted (IRHead x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx ++ "[0]")
generateExpressionLifted (IRTail x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx ++ "[1:]")
generateExpressionLifted (IRLeft x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, "Left(" ++ sx ++ ")")
generateExpressionLifted (IRRight x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, "Right(" ++ sx ++ ")")
generateExpressionLifted (IRFromLeft x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, "fromLeft(" ++ sx ++ ")")
generateExpressionLifted (IRFromRight x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, "fromRight(" ++ sx ++ ")")
generateExpressionLifted (IRIsLeft x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, "isinstance(" ++ sx ++ ", Left)")
generateExpressionLifted (IRIsRight x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, "isinstance(" ++ sx ++ ", Right)")
generateExpressionLifted (IRDensity dist x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, "density_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
generateExpressionLifted (IRCumulative dist x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, "cumulative_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
generateExpressionLifted (IRMap f x) = do
  (fs, fe) <- generateExpressionLifted f
  (xs, xe) <- generateExpressionLifted x
  return (fs ++ xs, "mapList(" ++ fe ++ ", " ++ xe ++ ")")
generateExpressionLifted (IRCons hd tl) = do
  (hs, he) <- generateExpressionLifted hd
  (ts, te) <- generateExpressionLifted tl
  return (hs ++ ts, "ConsInferenceList(" ++ he ++ ", " ++ te ++ ")")
generateExpressionLifted (IRIndex lst idx) = do
  (ls, le) <- generateExpressionLifted lst
  (is, ie) <- generateExpressionLifted idx
  return (ls ++ is, "(" ++ le ++ ")[" ++ ie ++ "]")
generateExpressionLifted (IRTheta x i) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx ++ "[0][" ++ show i ++ "]")
generateExpressionLifted (IRSubtree x i) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx ++ "[1][" ++ show i ++ "]")
generateExpressionLifted (IRTCons f s) = do
  (fs, fe) <- generateExpressionLifted f
  (ss, se) <- generateExpressionLifted s
  return (fs ++ ss, "T(" ++ fe ++ ", " ++ se ++ ")")
generateExpressionLifted expr@(IRApply _ _) = do
  let (fn, args) = collectApplyChain expr
  (fss, fn') <- generateExpressionLifted fn
  argResults <- mapM generateExpressionLifted args
  let argStmts = concatMap fst argResults
      args'    = map snd argResults
  return (fss ++ argStmts, fn' ++ "(" ++ intercalate ", " args' ++ ")")
generateExpressionLifted expr = do
  e <- generateExpression expr
  return ([], e)

generateStatementBlock :: IRExpr -> GlobalVariableSupply [String]
generateStatementBlock (IRLetIn name x body) = do
  s1 <- generateLetInStatement name x
  s2 <- generateStatementBlock body
  return (s1 ++ s2)
generateStatementBlock (IRIf cond left right) = do
  (condStmts, cCond) <- generateExpressionLifted cond
  cLeft  <- generateStatementBlock left
  cRight <- generateStatementBlock right
  let l1 = "if " ++ cCond ++ ":"
  return $ condStmts ++ [l1] ++ indentOnce cLeft ++ mergeElif cRight
generateStatementBlock (IRTCons (IRTCons f s) bc) = do
  fStmts  <- generateLetInStatement "_r0" f
  sStmts  <- generateLetInStatement "_r1" s
  bcStmts <- generateLetInStatement "_r2" bc
  return (fStmts ++ sStmts ++ bcStmts ++ ["return T(T(_r0, _r1), _r2)"])
generateStatementBlock (IRTCons f s) = do
  fStmts <- generateLetInStatement "_r0" f
  sStmts <- generateLetInStatement "_r1" s
  return (fStmts ++ sStmts ++ ["return T(_r0, _r1)"])
generateStatementBlock expr = do
  (stmts, e) <- generateExpressionLifted expr
  return (stmts ++ ["return " ++ e])


generateLetInStatement :: String -> IRExpr -> GlobalVariableSupply [String]
generateLetInStatement name lmd@(IRLambda _ _) =
  generateFunction False (name, (lmd, "Inner function: " ++ name))
generateLetInStatement name (IRIf cond left right) = do
  (condStmts, c) <- generateExpressionLifted cond
  leftStmts  <- generateLetInStatement name left
  rightStmts <- generateLetInStatement name right
  return $ condStmts ++ ["if " ++ c ++ ":"] ++ indentOnce leftStmts ++ mergeElif rightStmts
generateLetInStatement name (IRTCons f s) = do
  fStmts <- generateLetInStatement (name ++ "_0") f
  sStmts <- generateLetInStatement (name ++ "_1") s
  return (fStmts ++ sStmts ++ [name ++ " = T(" ++ name ++ "_0, " ++ name ++ "_1)"])
generateLetInStatement name (IRLetIn innerName innerVal body) = do
  innerStmts <- generateLetInStatement innerName innerVal
  bodyStmts  <- generateLetInStatement name body
  return (innerStmts ++ bodyStmts)
generateLetInStatement name x = do
  (stmts, expr) <- generateExpressionLifted x
  return (stmts ++ [name ++ " = " ++ expr])

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
  return ("(" ++ l ++ " " ++ pyOps op ++ " " ++ r ++ ")")
generateExpression (IRUnaryOp op expr) = do
  e <- generateExpression expr
  return (pyUnaryOps op ++ "(" ++ e ++ ")")
generateExpression (IRTheta x i) = do
  sx <- generateExpression x
  return (sx ++ "[0][" ++ show i ++ "]")
generateExpression (IRSubtree x i) = do
  sx <- generateExpression x
  return (sx ++ "[1][" ++ show i ++ "]")
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
  return (sx ++ "[0]")
generateExpression (IRTail x) = do
  sx <- generateExpression x
  return (sx ++ "[1:]")
generateExpression (IRMap f x) = do
  ff <- generateExpression f
  xx <- generateExpression x
  return ("mapList(" ++ ff ++ ", " ++ xx ++ ")")
generateExpression (IRTFst x) = do
  sx <- generateExpression x
  return (sx ++ "[0]")
generateExpression (IRTSnd x) = do
  sx <- generateExpression x
  return (sx ++ "[1]")
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
  return ("density_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
generateExpression (IRCumulative dist x) = do
  sx <- generateExpression x
  return ("cumulative_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
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
  return (fn' ++ "(" ++ intercalate ", " args' ++ ")")
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