module SPLL.CodeGenJulia (
  generateFunctions,
  juliaVal,
  juliaMangle,
  juliaKeywords
) where

import SPLL.IntermediateRepresentation
import SPLL.IRSelectPass (desugarSelectEnv)
import SPLL.Lang.Lang
import Data.List (intercalate, dropWhileEnd)
import SPLL.Lang.Types
import SPLL.Typing.RType (RType(..))
import SPLL.Typing.AlgebraicDataTypes (anyCtorTestMessage)
import Data.Maybe (fromMaybe)
import Data.Functor ((<&>))
import Control.Monad.State (StateT (runStateT), MonadState (get, put), MonadTrans (lift))
import Utils

--TODO: On the topic of memoization: Ideally we would want to optimize away redundant calls within a loop.
-- e.g. in MNist-Addition

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
juliaVal (VEither (Left a)) = "Left(" ++ juliaVal a ++ ")"
juliaVal (VEither (Right a)) = "Right(" ++ juliaVal a ++ ")"
juliaVal (VThetaTree tt) = juliaValTree tt
  where juliaValTree (ThetaTree val trees) = "([" ++ intercalate ", " (map show val) ++ "], [" ++ intercalate ", " (map juliaValTree trees) ++ "])"
juliaVal VUnit = "nothing"
juliaVal (VADT cName params) = juliaCtorRef cName ++ "(" ++ intercalate ", " (map juliaVal params) ++ ")"
juliaVal VAny = "\"ANY\""
juliaVal (VError e) = "throw(\"" ++ e ++ "\")"
juliaVal x = error ("unknown juliaVal for " ++ show x)
juliaMultiVal :: MultiValue -> String
juliaMultiVal MultiContinuous = "(\"C\", nothing)"
juliaMultiVal (MultiDiscretes vals) = "(\"D\", [" ++ intercalate ", " (map (juliaVal . valueToIR) vals) ++ "] )"
juliaMultiVal (MultiTuple l r) = "(\"T\", (" ++ juliaMultiVal l ++ ", " ++ juliaMultiVal r ++ "))"
juliaMultiVal (MultiEither l r) = "(\"E\", (" ++ juliaMultiVal l ++ ", " ++ juliaMultiVal r ++ "))"
juliaMultiVal (MultiADT constrs) = "(\"A\", [" ++ intercalate ", " (map (\(cName, fields) ->
  "(\"" ++ juliaMangle cName ++ "\", [" ++ intercalate ", " (map juliaMultiVal fields) ++ "])"
  ) constrs) ++ "] )"
juliaMultiVal x = error ("unknown juliaMultiVal for " ++ show x)

-- | Julia's reserved words. Unlike Python's, every one of them is lowercase,
-- so a constructor name (which SPLL capitalises) can never collide -- but a
-- *field* name can, and does so far more destructively than in Python: a field
-- named @end@ emits @struct Mk / end / end@, which closes the struct two lines
-- early and is mis-parsed rather than rejected at the offending token.
--
-- Contextual keywords that are legal identifiers elsewhere (@new@, @outer@,
-- @var@, and the @abstract@/@mutable@/@primitive@ modifiers) are included:
-- mangling a name that would have worked costs nothing, while missing one that
-- would not costs a silently mis-parsed module.
juliaKeywords :: [String]
juliaKeywords =
  [ "abstract", "baremodule", "begin", "break", "catch", "const", "continue"
  , "do", "else", "elseif", "end", "export", "false", "for", "function"
  , "global", "if", "import", "in", "isa", "let", "local", "macro", "module"
  , "mutable", "new", "outer", "primitive", "quote", "return", "struct", "true"
  , "try", "type", "using", "var", "where", "while"
  ]

-- | Make a name safe to emit as a Julia identifier. Same rule as
-- 'SPLL.CodeGenPyTorch.pyMangle', including the escape of a keyword followed by
-- a run of underscores -- without it the distinct fields @end@ and @end_@ would
-- both emit @end_@, and Julia rejects the resulting struct for a duplicate
-- field name. See that function for why injectivity stops at this family.
juliaMangle :: String -> String
juliaMangle name
  | dropWhileEnd (== '_') name `elem` juliaKeywords = name ++ "_"
  | otherwise                                       = name

-- | 'juliaMangle' for a constructor reference in a rendered value. The test
-- harness qualifies query-point constructors with the generated module name
-- (@Prog1.Leaf@); only the final segment is an identifier this backend owns.
juliaCtorRef :: String -> String
juliaCtorRef name = case break (== '.') (reverse name) of
  (revLast, '.':revQual) -> reverse revQual ++ "." ++ juliaMangle (reverse revLast)
  _                      -> juliaMangle name

generateADTClasses :: [ADTDecl] -> [String]
generateADTClasses decls = concatMap generateADTClass (concatMap constructors decls)

-- Every identifier printed here goes through 'juliaMangle'; the declaration
-- keeps the user's names (see 'renameADTIdentifiers'), and 'anyCtorTestMessage'
-- deliberately still quotes the source constructor name so the diagnostic reads
-- the same here, in Python, and in the interpreter.
generateADTClass :: ADTConstructorDecl -> [String]
generateADTClass (name, fields) =
  -- Struct declaration
  ["struct " ++ struct]++
  indentOnce (
    indentOnce fieldNames
  ) ++
  ["end"] ++
  -- Is function. Refuses a hole rather than answering False, matching the
  -- interpreter's 'isImpl' -- see 'anyCtorTestMessage'.
  ["is" ++ struct ++ "(x) = isAny(x) ? throw(" ++ show (anyCtorTestMessage name) ++ ") : x isa " ++ struct] ++
  -- Equals function
  ("Base.:(==)(other::Any, self::" ++ struct ++") = begin"):
    indentOnce
      (("if (!(other isa " ++ struct ++ ")) return false end"):
      -- Compare every field
      map (\f -> "if(!eq(self." ++ f ++ ", other." ++ f ++ ")) return false end") fieldNames ++ 
      ["return true"]) ++
  ["end"] ++
  -- Field acceessors
  concatMap (\f ->
    ("function " ++ f ++ "(x :: " ++ struct ++ ")") :
    indentOnce ["return x." ++ f] ++
    ["end"]
  ) fieldNames
  where struct = juliaMangle name
        fieldNames = map juliaMangle (map fst fields)

generateFunctions :: IREnv -> [String]
generateFunctions env0 = do
  -- Scalar backend: lower any IRSelect back to IRIf up front (pytorch-tensorizer
  -- M1, strategy B), so the rest of codegen never encounters it.
  let IREnv funcs adtDecls consts = renameADTIdentifiers juliaMangle (desugarSelectEnv env0)
  let adtClasses = generateADTClasses adtDecls
  let constsStr = map (\(name, val) -> name ++ " = " ++ juliaVal val) consts
  let callableNames = [ n ++ "_gen"
                      | IRFunGroup{groupName=n, genFun=Just (e, _)} <- funcs
                      , null (fst (unwrapLambdas e)) ]
                      -- nullary ADT constructors must be emitted as instantiations,
                      -- otherwise the bare struct type never compares equal to an
                      -- instance (same rule as CodeGenPyTorch's callableNames).
                      ++ [ juliaMangle cName | decl <- adtDecls, (cName, fields) <- constructors decl, null fields ]
  let funcGroupsMonadic = concatMapM generateFunctionGroup funcs
  let (funcStrs, (globalVars, _)) = evalSupply $ runStateT funcGroupsMonadic ([], callableNames)
  let varsStr = map (\(mv, name)-> name ++ " = " ++ juliaMultiVal mv) globalVars
  adtClasses ++ constsStr ++ varsStr ++ funcStrs

generateFunctionGroup :: IRFunGroup -> GlobalVariableSupply [String]
generateFunctionGroup IRFunGroup {groupName=n, genFun=g, probFun=p, integFun=i, encodeFun=e, normalFun=nrm, groupDoc=doc} = do
  let preemble = ("# === Function Group " ++ n ++ " ===") : map ("# " ++) (lines doc)
  gen <- fromMaybe (return []) (g <&> genF n "_gen")
  prob <- fromMaybe (return []) (p <&> genF n "_prob")
  integ <- fromMaybe (return []) (i <&> genF n "_integ")
  enc <- fromMaybe (return []) (e <&> genF n "_encode")
  norm <- fromMaybe (return []) (nrm <&> genF n "_normal")
  return $ preemble ++ gen ++ prob ++ integ ++ enc ++ norm
  where genF name suffix (fnBody, d) = generateFunction (name ++ suffix) d fnBody

generateFunction :: String -> String -> IRExpr -> GlobalVariableSupply [String]
generateFunction name doc expr = do
    let (args, reducedExpr) = unwrapLambdas expr
    let docLines = map ("# " ++) (lines doc)
    let l1 = "function " ++ name ++ "(" ++ intercalate ", " args ++ ")"
    block <- generateStatementBlock reducedExpr
    let lEnd = "end"
    return $ docLines ++ [l1] ++ indentOnce block ++ [lEnd]

unwrapLambdas :: IRExpr -> ([String], IRExpr)
unwrapLambdas (IRLambda name rest) = (name:otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

generateStatementBlock :: IRExpr -> GlobalVariableSupply [String]

generateStatementBlock (IRLetIn name lmd@(IRLambda _ _) body) = do
    funLines <- generateFunction name ("Inner function: " ++ name) lmd
    bodyLines <- generateStatementBlock body
    return (funLines ++ bodyLines)

generateStatementBlock (IRLetIn name val body) = do
    v <- generateExpression val
    rest <- generateStatementBlock body
    return ((name ++ " = " ++ v) : rest)

generateStatementBlock (IRError e) =
    return ["throw(\"" ++ escapeStr e ++ "\")"]

generateStatementBlock (IRIf cond left right) = do
    cCond  <- generateExpression cond
    cLeft  <- generateStatementBlock left
    cRight <- generateStatementBlock right
    let l1 = "if " ++ cCond
        l2 = "else"
        l3 = "end"
    return $ [l1] ++ indentOnce cLeft ++ [l2] ++ indentOnce cRight ++ [l3]

generateStatementBlock expr = do
    e <- generateExpression expr
    return ["return " ++ e]


generateExpression :: IRExpr -> GlobalVariableSupply String

generateExpression (IRIf cond left right) = do
    c <- generateExpression cond
    l <- generateExpression left
    r <- generateExpression right
    return $ "(" ++ c ++ " ? " ++ l ++ " : " ++ r ++ ")"
generateExpression (IROp OpApprox left right) = do
    l <- generateExpression left
    r <- generateExpression right
    return $ "isclose(" ++ l ++ ", " ++ r ++ ")"
generateExpression (IROp op left right) = do
    l <- generateExpression left
    r <- generateExpression right
    return $ "((" ++ l ++ ") " ++ juliaOps op ++ " (" ++ r ++ "))"
generateExpression (IRUnaryOp op expr) = do
    e <- generateExpression expr
    return $ juliaUnaryOps op ++ "(" ++ e ++ ")"
generateExpression (IRTheta expr i) = do
    e <- generateExpression expr
    return $ "(" ++ e ++ ")[1][" ++ show (i + 1) ++ "]"
generateExpression (IRSubtree expr i) = do
    e <- generateExpression expr
    return $ "(" ++ e ++ ")[2][" ++ show (i + 1) ++ "]"
generateExpression (IRConst v) =
    return $ juliaVal v
generateExpression (IRCons hd tl) = do
    h <- generateExpression hd
    t <- generateExpression tl
    return $ "prepend(" ++ h ++ ", " ++ t ++ ")"
generateExpression (IRElementOf el lst) = do
    e <- generateExpression el
    l <- generateExpression lst
    return $ "(" ++ e ++ " in " ++ l ++ ")"
generateExpression (IRTCons fs sn) = do
    f <- generateExpression fs
    s <- generateExpression sn
    return $ "T(" ++ f ++ ", " ++ s ++ ")"
generateExpression (IRHead x) = do
    e <- generateExpression x
    return $ "head(" ++ e ++ ")"
generateExpression (IRTail x) = do
    e <- generateExpression x
    return $ "tail(" ++ e ++ ")"
generateExpression (IRMap f x) = do
    ff <- generateExpression f
    xx <- generateExpression x
    return $ "mapList(" ++ ff ++ ", " ++ xx ++ ")"
generateExpression (IRTFst x) = do
    e <- generateExpression x
    return $ "(" ++ e ++ ")[1]"
generateExpression (IRTSnd x) = do
    e <- generateExpression x
    return $ "(" ++ e ++ ")[2]"
generateExpression (IRLeft x) = do
    e <- generateExpression x
    return $ "Left(" ++ e ++ ")"
generateExpression (IRRight x) = do
    e <- generateExpression x
    return $ "Right(" ++ e ++ ")"
generateExpression (IRFromLeft x) = do
    e <- generateExpression x
    return $ "fromLeft(" ++ e ++ ")"
generateExpression (IRFromRight x) = do
    e <- generateExpression x
    return $ "fromRight(" ++ e ++ ")"
generateExpression (IRIsLeft x) = do
    e <- generateExpression x
    return $ "(" ++ e ++ " isa Left)"
generateExpression (IRIsRight x) = do
    e <- generateExpression x
    return $ "(" ++ e ++ " isa Right)"
generateExpression (IRDensity dist x) = do
    e <- generateExpression x
    return $ "density_" ++ show dist ++ "(" ++ e ++ ")"
generateExpression (IRCumulative dist x) = do
    e <- generateExpression x
    return $ "cumulative_" ++ show dist ++ "(" ++ e ++ ")"
generateExpression (IRLogDensity dist x) = do
    e <- generateExpression x
    return $ "log_density_" ++ show dist ++ "(" ++ e ++ ")"
generateExpression (IRLogCumulative dist x) = do
    e <- generateExpression x
    return $ "log_cumulative_" ++ show dist ++ "(" ++ e ++ ")"
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
    return $ "(" ++ fn' ++ ")(" ++ intercalate ", " args' ++ ")"
generateExpression (IRIsPossible multiVal expr) = do
    e <- generateExpression expr
    var <- addOrGetFromGlobalStorage multiVal
    return $ "isPossible(" ++ var ++ ", " ++ e ++ ")"
generateExpression (IREnumSum name enumRange expr) = do
    e <- generateExpression expr
    var <- addOrGetFromGlobalStorage enumRange
    return $ "sum(map((" ++ name ++ " -> " ++ e ++ "), multiValueToValueList(" ++ var ++")))"
generateExpression (IRLogEnumSum name enumRange expr) = do
    e <- generateExpression expr
    var <- addOrGetFromGlobalStorage enumRange
    return $ "logsumexp(map((" ++ name ++ " -> " ++ e ++ "), multiValueToValueList(" ++ var ++")))"
generateExpression (IREnumSumPaired logSp name enumRange expr) = do
    e <- generateExpression expr
    var <- addOrGetFromGlobalStorage enumRange
    return $ "enumSumPaired((" ++ name ++ " -> " ++ e ++ "), multiValueToValueList(" ++ var
             ++ "), " ++ (if logSp then "true" else "false") ++ ")"
generateExpression (IRIndex lst idx) = do
    l <- generateExpression lst
    i <- generateExpression idx
    return $ "(" ++ l ++ ")[" ++ i ++ " + 1]"
generateExpression (IRLetIn name val body) = do
    v <- generateExpression val
    b <- generateExpression body
    return $ "(let " ++ name ++ " = " ++ v ++ "; " ++ b ++ " end)"
generateExpression (IRError e) =
    return $ "throw(\"" ++ escapeStr e ++ "\")"
generateExpression (IRConformsTo t x) = do
    sx <- generateExpression x
    return (jlConforms t sx)
generateExpression x =
    error ("Unknown expression in Julia codegen: " ++ show x)

-- | Escape a Haskell string for embedding in a double-quoted Julia string literal
-- (e.g. an IRError message that may contain quotes from a show'd type).
escapeStr :: String -> String
escapeStr = concatMap esc
  where esc '"'  = "\\\""
        esc '\\' = "\\\\"
        esc '\n' = "\\n"
        esc c    = [c]

-- | Runtime type-tag check for the query-type guard (see IRConformsTo). Full-depth
-- structural check mirroring the interpreter's 'valueConformsTo': recurses into tuple
-- components, either arms, and every list element; precise for float/bool/int and
-- permissive ("true") only for types with no cheap runtime tag. Note Bool <: Integer
-- in Julia, so TInt explicitly excludes Bool. The marginal-query wildcard (isAny) is
-- accepted at every level, matching VAny, and short-circuits before any component
-- accessor. The Int arg is a nesting depth used to name list-lambda binders uniquely.
jlConforms :: RType -> String -> String
jlConforms = jlConformsAt 0

jlConformsAt :: Int -> RType -> String -> String
jlConformsAt d t e = "(isAny(" ++ e ++ ") || " ++ jlConformsShape d t e ++ ")"

jlConformsShape :: Int -> RType -> String -> String
jlConformsShape _ TFloat  e = "(" ++ e ++ " isa AbstractFloat)"
jlConformsShape _ TBool   e = "(" ++ e ++ " isa Bool)"
jlConformsShape _ TInt    e = "((" ++ e ++ " isa Integer) && !(" ++ e ++ " isa Bool))"
jlConformsShape d (Tuple a b) e =
  "((" ++ e ++ " isa T) && " ++ jlConformsAt d a (e ++ ".t1") ++ " && " ++ jlConformsAt d b (e ++ ".t2") ++ ")"
jlConformsShape d (ListOf t) e =
  let v = "_ce" ++ show d
  in "((" ++ e ++ " isa InferenceList) && all(" ++ v ++ " -> " ++ jlConformsAt (d + 1) t v ++ ", " ++ e ++ "))"
jlConformsShape d (TEither a b) e =
  "(((" ++ e ++ " isa Left) && " ++ jlConformsAt d a (e ++ ".val") ++ ") || ((" ++ e ++ " isa Right) && " ++ jlConformsAt d b (e ++ ".val") ++ "))"
jlConformsShape _ _ _ = "true"

collectApplyChain :: IRExpr -> (IRExpr, [IRExpr])
collectApplyChain (IRApply f arg) = let (fn, args) = collectApplyChain f in (fn, args ++ [arg])
collectApplyChain expr = (expr, [])

generateLambdaExpression :: IRExpr -> GlobalVariableSupply String
generateLambdaExpression expr = do
    let (names, rest) = getLambdaNames expr
    body <- generateExpression rest
    return $ "((" ++ intercalate ", " names ++ ") -> " ++ body ++ ")"

getLambdaNames :: IRExpr -> ([String], IRExpr)
getLambdaNames (IRLambda n body) = (n:names, rest)
  where (names, rest) = getLambdaNames body
getLambdaNames x = ([], x)
