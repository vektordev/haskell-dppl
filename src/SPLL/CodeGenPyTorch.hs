{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module SPLL.CodeGenPyTorch (
  generateFunctions,
  pyVal,
  envToLUT,
  replaceCalls,
  pyMangle,
  pyDouble,
  pythonKeywords
) where

import SPLL.IntermediateRepresentation
import SPLL.IRSelectPass (desugarSelectEnv)
import SPLL.Lang.Types
import SPLL.Typing.RType (RType(..), shapeRank)
import SPLL.Typing.AlgebraicDataTypes (anyCtorTestMessage)
import Data.List (intercalate, intersperse, isPrefixOf, dropWhileEnd)
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
pyUnaryOps OpExp = "safe_exp"
pyUnaryOps OpAbs = "abs"
pyUnaryOps OpNot = "not"
pyUnaryOps OpLog = "safe_log"
pyUnaryOps OpSign = "sign"
pyUnaryOps OpIsAny = "isAny"

-- | A 'Double' as a Python float literal.
--
-- Haskell's 'show' renders the three non-finite doubles as @Infinity@,
-- @-Infinity@ and @NaN@ -- none of which is a Python name. Emitting them
-- produced code that raised @NameError@ at run time instead of failing the
-- compile, and log space reaches them constantly: its zero is @-1/0@
-- ('SPLL.Semiring.negInfIR'), so every impossible arm of a @--logSpace@
-- program carried an undefined name. @float('inf')@ needs no import, unlike
-- @math.inf@.
pyDouble :: Double -> String
pyDouble f
  | isNaN f      = "float('nan')"
  | isInfinite f = if f > 0 then "float('inf')" else "float('-inf')"
  | otherwise    = show f

pyVal :: IRValue -> String
pyVal (VList EmptyList) = "EmptyInferenceList()"
pyVal (VList AnyList) = "AnyInferenceList()"
pyVal (VList (ListCont x xs)) = "ConsInferenceList(" ++ pyVal x ++ ", " ++ pyVal (VList xs) ++ ")"
pyVal (VInt i) = show i
pyVal (VFloat f) = pyDouble f
pyVal (VBool f) = if f then "True" else "False"
pyVal (VTuple a b) = "T(" ++ pyVal a ++ ", " ++ pyVal b ++ ")"
pyVal (VEither (Left a)) = "Left(" ++ pyVal a ++ ")"
pyVal (VEither (Right a)) = "Right(" ++ pyVal a ++ ")"
pyVal VUnit = "None"
pyVal (VThetaTree tt) = pyValTree tt
  where pyValTree (ThetaTree val trees) = "([" ++ intercalate ", " (map pyDouble val) ++ "], [" ++ intercalate ", " (map pyValTree trees) ++ "])"
pyVal (VADT cName params) = pyCtorRef cName ++ "(" ++ intercalate ", " (map pyVal params) ++ ")"
pyVal (VAny) = "'ANY'"
pyVal (VError e) = "throw(\"" ++ e ++ "\")"
-- 'VAnyExcept' has no runtime representation in the Python runtime library
-- (unlike VAny/AnyList above, which both render as real sentinels), so there
-- is no string to emit here -- this is a backstop only. The intended refusal
-- point is 'SPLL.IntermediateRepresentation.anyExceptCodegenRefusal', called
-- from 'Main.codeGenToLang' before 'generateFunctions' is ever reached; a
-- direct caller of 'generateFunctions' that skips that check lands here
-- instead of the generic "unknown pyVal" panic below (task
-- vanyexcept-unrenderable-in-text-backends).
pyVal v@(VAnyExcept _) = error (unlines
  [ "pyVal: unconsumed VAnyExcept placeholder reached Python codegen: " ++ show v
  , "This should have been refused earlier by"
  , "SPLL.IntermediateRepresentation.anyExceptCodegenRefusal; a caller reached"
  , "generateFunctions without that guard."
  , "(task vanyexcept-unrenderable-in-text-backends)" ])
pyVal x = error ("unknown pyVal for " ++ show x)

pyMultiVal :: MultiValue -> String
pyMultiVal MultiContinuous = "(\"C\", None)"
pyMultiVal (MultiDiscretes vals) = "(\"D\", [" ++ intercalate ", " (map (pyVal . valueToIR) vals) ++ "])"
pyMultiVal (MultiTuple l r) = "(\"T\", (" ++ pyMultiVal l ++ ", " ++ pyMultiVal r ++ "))"
pyMultiVal (MultiEither l r) = "(\"E\", (" ++ pyMultiVal l ++ ", " ++ pyMultiVal r ++ "))"
pyMultiVal (MultiADT constrs) = "(\"A\", [" ++ intercalate ", " (map (\(cName, fields) -> 
  "(" ++ pyCtorRef cName ++ ", [" ++ intercalate ", " (map pyMultiVal fields) ++ "])"
  ) constrs) ++ "])"
-- MultiAuto and MultiTypeRef are resolved by AutoNeural before codegen: the
-- first by auto-derivation from the RType, the second by unrolling the
-- depth-bounded recursion. Reaching codegen means that pass was skipped.
pyMultiVal x = error ("unresolved MultiValue in codegen: " ++ show x)

-- | Python's reserved words. A name in this set cannot be an identifier at all,
-- so emitting one produces a file that does not parse -- @class None:@ is a
-- @SyntaxError@, not a shadowing hazard. Kept here, beside the code that prints
-- identifiers, rather than in a shared module: Julia's list is different and
-- the two must be free to diverge.
--
-- Soft keywords (@match@, @case@, @type@, @_@) are deliberately absent: they
-- are contextually valid as ordinary identifiers, so mangling them would rename
-- names that work. Names merely *exported by* @pythonLib@ (@eq@, @T@, @isAny@,
-- ...) are also absent -- shadowing one is a real hazard but a different one,
-- and it needs the library's whole surface rather than a fixed keyword list.
pythonKeywords :: [String]
pythonKeywords =
  [ "False", "None", "True", "and", "as", "assert", "async", "await", "break"
  , "class", "continue", "def", "del", "elif", "else", "except", "finally"
  , "for", "from", "global", "if", "import", "in", "is", "lambda", "nonlocal"
  , "not", "or", "pass", "raise", "return", "try", "while", "with", "yield"
  ]

-- | Make a name safe to emit as a Python identifier, by appending the
-- conventional trailing underscore.
--
-- The rule fires not only on a keyword but on a keyword followed by any run of
-- underscores, and that is what makes it injective. Mangling only exact
-- keywords would map the distinct source names @None@ and @None_@ onto the
-- same @None_@ -- emitting two @class None_:@ definitions, the second silently
-- shadowing the first, so values of one constructor would answer the other's
-- predicate. Escaping the whole family instead shifts @kw@, @kw_@, @kw__@, ...
-- each one underscore along; the family maps into itself injectively, every
-- other name maps to itself, and the two images are disjoint because anything
-- of the form @kw_@+ is by definition in the family.
--
-- Injectivity holds within this family, not across the whole ADT namespace: a
-- field named @isNone_@ in a program that also declares a constructor @None@
-- still collides with that constructor's derived predicate. Nothing here can
-- see that -- mangling is deliberately a pure function of one name, which is
-- what lets 'pyVal' mangle a query point that never passed through
-- 'renameADTIdentifiers'. 'adtIdentifierRenaming' carries the cross-family
-- check instead, where the whole declaration set is in scope.
pyMangle :: String -> String
pyMangle name
  | dropWhileEnd (== '_') name `elem` pythonKeywords = name ++ "_"
  | otherwise                                        = name

-- | 'pyMangle' for a constructor reference in a rendered value, which the test
-- harness may have qualified with a module path. Only the final segment is an
-- identifier this backend owns; a qualifier is the caller's and is passed
-- through untouched.
pyCtorRef :: String -> String
pyCtorRef name = case break (== '.') (reverse name) of
  (revLast, '.':revQual) -> reverse revQual ++ "." ++ pyMangle (reverse revLast)
  _                      -> pyMangle name

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs
onHead _ [] = []

generateFunctions :: Bool -> IREnv -> [String]
--contrary to the julia backend, we want to aggregate gen and prob into one classes. Ugly implementation, but it'll do for now.
generateFunctions genBoil env0 =
    -- Scalar backend: lower any IRSelect (from batched mode's select pass) back
    -- to IRIf up front, so the rest of codegen never sees it (pytorch-tensorizer
    -- M1, strategy B).
    let env@(IREnv funcs adtsEnv consts) = renameADTIdentifiers pyMangle (desugarSelectEnv env0)
        lut = envToLUT env ++ stdLib
        callableNames = [ fromMaybe (n ++ "_gen") (lookup (n ++ "_gen") lut)
                        | IRFunGroup{groupName=n, genFun=Just (e, _)} <- funcs
                        , null (fst (unwrapLambdas e)) ]
                        -- nullary ADT constructors must be emitted as instantiations,
                        -- otherwise the bare class never compares equal to enumerated instances
                        ++ [ pyMangle cName | decl <- adtsEnv, (cName, fields) <- constructors decl, null fields ]
    in if genBoil then
      ["from pythonLib import *",
      "import functools",
      "import math",
      "from torch.nn import Module", ""] ++
      generateADTClasses adtsEnv ++
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

-- Every identifier printed here goes through 'pyMangle'; the declaration itself
-- keeps the names the user wrote (see 'renameADTIdentifiers'). The one place
-- the *source* name is used instead is 'anyCtorTestMessage', which must read
-- identically across all three backends and the interpreter.
generateADTClass :: ADTConstructorDecl -> [String]
generateADTClass (name, fields) =
  -- Class declaration
  ["class " ++ cls ++ ":"]++
  indentOnce (
    -- Constructor
    ("def __init__(self, " ++ intercalate ", " fieldNames ++ "):") :
    case fieldNames of
      [] -> indentOnce ["pass"]
      fieldNamesList -> indentOnce (
        map (\f -> "self." ++f ++ " = " ++ f) fieldNamesList ++
        ["self._fields = [" ++ intercalate ", " fieldNamesList ++ "]"])
  ) ++ [""] ++
  indentOnce (
    "def __eq__(self, other):":
      indentOnce (
        ("if not isinstance(other, " ++ cls ++ "): return False"):
        map (\f -> "if not eq(self." ++ f ++ ", other." ++ f ++ "): return False") fieldNames ++
        ["return True"]
      )
  ) ++ [""] ++
  -- Is function. The ANY refusal keeps this in step with the interpreter's
  -- 'isImpl'; `isinstance` would answer False for a hole and silently drop the
  -- branch. See 'anyCtorTestMessage'.
  ["def is" ++ cls ++ "(x):"] ++
  indentOnce ["if isAny(x): throw(" ++ show (anyCtorTestMessage name) ++ ")",
              "return isinstance(x, " ++ cls ++ ")"] ++
  -- Field acceessors
  concatMap (\f ->
    ("def " ++ f ++ "(x):") :
    indentOnce ["return x." ++ f]
  ) fieldNames
  where cls = pyMangle name
        fieldNames = map pyMangle (map fst fields)

generateClass :: [(String, String)] -> [String] -> IRFunGroup -> [String]
generateClass lut callableNames (IRFunGroup name gen prob integ encode normal doc _) = let
  funcStringFromMaybe fname func = case func of
    Just a -> generateFunction True (fname, replaceCallsDecl a)
    Nothing -> return []
  ((i, p, g, e, n), (globalVars, _)) = evalSupply $ runStateT (do
    i' <- funcStringFromMaybe "integrate" integ
    p' <- funcStringFromMaybe "forward" prob
    g' <- funcStringFromMaybe "generate" gen
    e' <- funcStringFromMaybe "encode" encode
    n' <- funcStringFromMaybe "normal_params" normal
    return (i', p', g', e', n')) ([], callableNames)
  commentLines = map ("# " ++) (lines doc)
  initLine = "class " ++ onHead toUpper name ++ "(Module):"
  globalVarDecls = map (\(mv, varName)-> varName ++ " = " ++ pyMultiVal mv) globalVars
  funcs = i ++ [""] ++ p ++ [""] ++ g ++ [""] ++ e ++ [""] ++ n
  replaceCallsDecl (expr, d) = (irMap (replaceCalls lut) expr, d)
  in commentLines ++ initLine:indentOnce globalVarDecls ++ indentOnce funcs

generateFunction :: Bool -> (String, IRFunDecl) -> GlobalVariableSupply [String]
generateFunction classFunction (name, (expr, doc)) = do
  let (args, reducedExpr) = unwrapLambdas expr
  let args' = if classFunction then "self":args else args
  let l1 = "def " ++ name ++ "(" ++ intercalate ", " args' ++ "):"
  block <- generateStatementBlock reducedExpr
  let docLines = map ("# " ++) (lines doc)
  return $ docLines ++ [l1] ++ indentOnce block

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
containsIf (IRLogDensity _ x) = containsIf x
containsIf (IRLogCumulative _ x) = containsIf x
containsIf (IRMap f x)     = containsIf f || containsIf x
containsIf (IRIndex l i)   = containsIf l || containsIf i
containsIf (IRCons h t)    = containsIf h || containsIf t
containsIf (IRTheta x _)   = containsIf x
containsIf (IRSubtree x _) = containsIf x
containsIf _               = False

-- | Like generateExpression, but lifts complex IRIf nodes into temp variables,
-- returning prefix statements and the resulting expression.
--
-- The expression is built as a difference string (ShowS): the optimizer emits
-- world-sum spines as right-nested chains thousands of nodes deep, and plain
-- @chain ++ ")"@ concatenation re-wraps the whole suffix at every level, which
-- made rendering quadratic in chain length.  'renderLifted' forces the final
-- String exactly once per emitted statement.
generateExpressionLifted :: IRExpr -> GlobalVariableSupply ([String], ShowS)
generateExpressionLifted expr@(IRIf cond left right)
  | not (containsIf left || containsIf right) = do
      (condStmts, c) <- generateExpressionLifted cond
      l <- generateExpression left
      r <- generateExpression right
      return (condStmts, str "(" . str l . str " if " . c . str " else " . str r . str ")")
  | otherwise = do
      tmpId <- lift demandUniqueNumber
      let tmp = "_t" ++ show tmpId
      stmts <- generateLetInStatement tmp expr
      return (stmts, str tmp)
generateExpressionLifted (IRLetIn name val body) = do
  valStmts <- generateLetInStatement name val
  (bodyStmts, bodyExpr) <- generateExpressionLifted body
  return (valStmts ++ bodyStmts, bodyExpr)
generateExpressionLifted (IROp OpApprox l r) = do
  (ls, le) <- generateExpressionLifted l
  (rs, re) <- generateExpressionLifted r
  return (ls ++ rs, str "isclose(" . le . str ", " . re . str ")")
generateExpressionLifted (IROp op l r) = do
  (ls, le) <- generateExpressionLifted l
  (rs, re) <- generateExpressionLifted r
  return (ls ++ rs, str "(" . le . str " " . str (pyOps op) . str " " . re . str ")")
generateExpressionLifted (IRUnaryOp op e) = do
  (ss, se) <- generateExpressionLifted e
  return (ss, str (pyUnaryOps op) . str "(" . se . str ")")
generateExpressionLifted (IRTFst x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str "[0]")
generateExpressionLifted (IRTSnd x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str "[1]")
generateExpressionLifted (IRHead x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str "[0]")
generateExpressionLifted (IRTail x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str "[1:]")
generateExpressionLifted (IRLeft x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "Left(" . sx . str ")")
generateExpressionLifted (IRRight x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "Right(" . sx . str ")")
generateExpressionLifted (IRFromLeft x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "fromLeft(" . sx . str ")")
generateExpressionLifted (IRFromRight x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "fromRight(" . sx . str ")")
generateExpressionLifted (IRIsLeft x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "isinstance(" . sx . str ", Left)")
generateExpressionLifted (IRIsRight x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str "isinstance(" . sx . str ", Right)")
generateExpressionLifted (IRDensity dist x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str ("density_" ++ pyDistName dist) . str "(" . sx . str ")")
generateExpressionLifted (IRCumulative dist x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str ("cumulative_" ++ pyDistName dist) . str "(" . sx . str ")")
generateExpressionLifted (IRLogDensity dist x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str ("log_density_" ++ pyDistName dist) . str "(" . sx . str ")")
generateExpressionLifted (IRLogCumulative dist x) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, str ("log_cumulative_" ++ pyDistName dist) . str "(" . sx . str ")")
generateExpressionLifted (IRMap f x) = do
  (fs, fe) <- generateExpressionLifted f
  (xs, xe) <- generateExpressionLifted x
  return (fs ++ xs, str "mapList(" . fe . str ", " . xe . str ")")
generateExpressionLifted (IRCons hd tl) = do
  (hs, he) <- generateExpressionLifted hd
  (ts, te) <- generateExpressionLifted tl
  return (hs ++ ts, str "ConsInferenceList(" . he . str ", " . te . str ")")
generateExpressionLifted (IRIndex lst idx) = do
  (ls, le) <- generateExpressionLifted lst
  (is, ie) <- generateExpressionLifted idx
  return (ls ++ is, str "(" . le . str ")[" . ie . str "]")
generateExpressionLifted (IRTheta x i) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str ("[0][" ++ show i ++ "]"))
generateExpressionLifted (IRSubtree x i) = do
  (ss, sx) <- generateExpressionLifted x
  return (ss, sx . str ("[1][" ++ show i ++ "]"))
generateExpressionLifted (IRTCons f s) = do
  (fs, fe) <- generateExpressionLifted f
  (ss, se) <- generateExpressionLifted s
  return (fs ++ ss, str "T(" . fe . str ", " . se . str ")")
generateExpressionLifted expr@(IRApply _ _) = do
  let (fn, args) = collectApplyChain expr
  (fss, fn') <- generateExpressionLifted fn
  argResults <- mapM generateExpressionLifted args
  let argStmts = concatMap fst argResults
      args'    = map snd argResults
      sep = str ", "
  return (fss ++ argStmts, fn' . str "(" . foldr (.) id (intersperse sep args') . str ")")
generateExpressionLifted expr = do
  e <- generateExpression expr
  return ([], str e)

-- | Diagnostics for the tensor ranks and axes the backends do not emit. Shared
-- by all three scalar-ish backends via their own copies of the guard; the
-- message names the node so a future higher-rank producer fails with a pointer
-- rather than a mystery.
rankUnsupported :: String -> Int -> String
rankUnsupported what r =
  what ++ ": only rank-1 tensors are emitted, got rank " ++ show r
       ++ " (the representation admits it; no backend lowers it yet)"

axisUnsupported :: String -> Int -> String
axisUnsupported what ax =
  what ++ ": only axis 0 is emitted, got axis " ++ show ax
       ++ " (the representation admits it; no backend lowers it yet)"

-- | The Python runtime function reducing a tensor axis with each operator.
-- sum/max are Python's own builtins (both take an iterable, same as
-- logsumexp's own signature below), logsumexp is pythonLib.py's (already
-- backing IRLogEnumSum). max on an empty iterable raises in real Python,
-- same as every other reduction here has no defined empty-domain behaviour
-- (an enumerable domain from Analysis.materializationDomain is never empty --
-- see the "empty propagated domain" refusal in Analysis).
pyReduceOp :: ReduceOp -> String
pyReduceOp ROpAdd = "sum"
pyReduceOp ROpLogSumExp = "logsumexp"
pyReduceOp ROpMax = "max"

str :: String -> ShowS
str = showString

-- | Force a lifted expression into the single String it is emitted into.
renderLifted :: ShowS -> String
renderLifted e = e ""

generateStatementBlock :: IRExpr -> GlobalVariableSupply [String]
generateStatementBlock (IRLetIn name x body) = do
  s1 <- generateLetInStatement name x
  s2 <- generateStatementBlock body
  return (s1 ++ s2)
generateStatementBlock (IRIf cond left right) = do
  (condStmts, cCond) <- generateExpressionLifted cond
  cLeft  <- generateStatementBlock left
  cRight <- generateStatementBlock right
  let l1 = "if " ++ renderLifted cCond ++ ":"
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
  return (stmts ++ ["return " ++ renderLifted e])


generateLetInStatement :: String -> IRExpr -> GlobalVariableSupply [String]
generateLetInStatement name lmd@(IRLambda _ _) =
  generateFunction False (name, (lmd, "Inner function: " ++ name))
generateLetInStatement name (IRIf cond left right) = do
  (condStmts, c) <- generateExpressionLifted cond
  leftStmts  <- generateLetInStatement name left
  rightStmts <- generateLetInStatement name right
  return $ condStmts ++ ["if " ++ renderLifted c ++ ":"] ++ indentOnce leftStmts ++ mergeElif rightStmts
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
  return (stmts ++ [name ++ " = " ++ renderLifted expr])

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
generateExpression (IRLogDensity dist x) = do
  sx <- generateExpression x
  return ("log_density_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
generateExpression (IRLogCumulative dist x) = do
  sx <- generateExpression x
  return ("log_cumulative_" ++ pyDistName dist ++ "(" ++ sx ++ ")")
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
generateExpression (IRLogEnumSum name enumRange expr) = do
  e <- generateExpression expr
  varName <- addOrGetFromGlobalStorage enumRange
  return ("logsumexp(map((lambda " ++ name ++ ": " ++ e ++ "), multiValueToValueList(self." ++ varName ++ ")))")
generateExpression (IREnumSumPaired logSp name enumRange expr) = do
  e <- generateExpression expr
  varName <- addOrGetFromGlobalStorage enumRange
  return ("enumSumPaired((lambda " ++ name ++ ": " ++ e ++ "), multiValueToValueList(self."
          ++ varName ++ "), " ++ (if logSp then "True" else "False") ++ ")")
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
-- The tensor builtins (design ir-tensor-values). A scalar-mode tensor is a
-- flat Python list: scalar pythonLib.py is pure-Python (probabilities are
-- floats, there is no torch in scope), so there is no real tensor to lower a
-- "tensor of primitive" to here -- that specialization lives in the batched
-- backend, where an element is a [B] tensor and a reduce really is a stacked
-- sum. What scalar mode does get is an O(1) BIndex, against IRIndex's cons
-- walk.
--
-- Only rank 1 is emitted. The representation admits any rank, but nothing
-- produces a higher-rank tensor yet and untested stride arithmetic in three
-- backends would be dead weight; the guard says so rather than emitting
-- something plausible and wrong.
generateExpression (IRBuiltin (BTensor sh) elems)
  | shapeRank sh == 1 = do
      es <- mapM generateExpression elems
      return ("[" ++ intercalate ", " es ++ "]")
  | otherwise = error (rankUnsupported "BTensor" (shapeRank sh))
-- A comprehension rather than map(lambda ...): it binds the loop variable
-- directly, saving a Python call per element, and the bound name is already a
-- valid identifier.
generateExpression (IRBuiltin BMap [IRLambda v body, t]) = do
  b <- generateExpression body
  tt <- generateExpression t
  return ("[" ++ b ++ " for " ++ v ++ " in " ++ tt ++ "]")
generateExpression (IRBuiltin BMap [f, t]) = do
  ff <- generateExpression f
  tt <- generateExpression t
  return ("list(map(" ++ ff ++ ", " ++ tt ++ "))")
generateExpression (IRBuiltin (BReduce op ax) [t])
  | ax == 0 = do
      tt <- generateExpression t
      return (pyReduceOp op ++ "(" ++ tt ++ ")")
  | otherwise = error (axisUnsupported "BReduce" ax)
generateExpression (IRBuiltin (BIndex ax) [t, k])
  | ax == 0 = do
      tt <- generateExpression t
      kk <- generateExpression k
      return ("(" ++ tt ++ ")[" ++ kk ++ "]")
  | otherwise = error (axisUnsupported "BIndex" ax)
generateExpression (IRError e) =
  return ("throw(\"" ++ escapeStr e ++ "\")")
generateExpression (IRConformsTo t x) = do
  sx <- generateExpression x
  return (pyConforms t sx)
generateExpression x =
  error ("Unknown expression in PyTorch codegen: " ++ show x)

-- | Escape a Haskell string for embedding in a double-quoted target-language
-- string literal (e.g. an IRError message that may contain quotes from a show'd type).
escapeStr :: String -> String
escapeStr = concatMap esc
  where esc '"'  = "\\\""
        esc '\\' = "\\\\"
        esc '\n' = "\\n"
        esc c    = [c]

-- | A runtime type-tag check for the query-type guard (see IRConformsTo). Full-depth
-- structural check mirroring the interpreter's 'valueConformsTo': recurses into tuple
-- components, either arms, and every list element; precise for float/bool/int and
-- permissive ("True") only for types with no cheap runtime tag (so it never falsely
-- rejects). The marginal-query wildcard (isAny) is accepted at every level, matching
-- VAny, and short-circuits before any component accessor is evaluated. The Int arg is
-- a nesting depth used to name list-comprehension binders uniquely.
pyConforms :: RType -> String -> String
pyConforms = pyConformsAt 0

pyConformsAt :: Int -> RType -> String -> String
pyConformsAt d t e = "(isAny(" ++ e ++ ") or " ++ pyConformsShape d t e ++ ")"

pyConformsShape :: Int -> RType -> String -> String
pyConformsShape _ TFloat  e = "isinstance(" ++ e ++ ", float)"
pyConformsShape _ TBool   e = "isinstance(" ++ e ++ ", bool)"
pyConformsShape _ TInt    e = "(isinstance(" ++ e ++ ", int) and not isinstance(" ++ e ++ ", bool))"
pyConformsShape d (Tuple a b) e =
  "(isinstance(" ++ e ++ ", T) and " ++ pyConformsAt d a (e ++ ".t1") ++ " and " ++ pyConformsAt d b (e ++ ".t2") ++ ")"
pyConformsShape d (ListOf t) e =
  let v = "_ce" ++ show d
  in "(isinstance(" ++ e ++ ", InferenceList) and all(" ++ pyConformsAt (d + 1) t v ++ " for " ++ v ++ " in " ++ e ++ "))"
pyConformsShape d (TEither a b) e =
  "((isinstance(" ++ e ++ ", Left) and " ++ pyConformsAt d a (e ++ ".val") ++ ") or (isinstance(" ++ e ++ ", Right) and " ++ pyConformsAt d b (e ++ ".val") ++ "))"
pyConformsShape _ _ _ = "True"

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