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
juliaVal (VEither (Left a)) = "Left(" ++ juliaVal a ++ ")"
juliaVal (VEither (Right a)) = "Right(" ++ juliaVal a ++ ")"
juliaVal (VThetaTree tt) = juliaValTree tt
  where juliaValTree (ThetaTree val trees) = "([" ++ intercalate ", " (map show val) ++ "], [" ++ intercalate ", " (map juliaValTree trees) ++ "])"
juliaVal (VADT cName params) = cName ++ "(" ++ intercalate ", " (map juliaVal params) ++ ")"
juliaVal VAny = "\"ANY\""
juliaVal x = error ("unknown juliaVal for " ++ show x)
juliaMultiVal :: MultiValue -> String
juliaMultiVal (MultiDiscretes vals) = "(\"D\", [" ++ intercalate ", " (map (juliaVal . valueToIR) vals) ++ "] )"
juliaMultiVal (MultiTuple l r) = "(\"T\", (" ++ juliaMultiVal l ++ ", " ++ juliaMultiVal r ++ "))"
juliaMultiVal (MultiEither l r) = "(\"E\", (" ++ juliaMultiVal l ++ ", " ++ juliaMultiVal r ++ "))"
juliaMultiVal (MultiADT constrs) = "(\"A\", [" ++ intercalate ", " (map (\(cName, fields) ->
  "(\"" ++ cName ++ "\", [" ++ intercalate ", " (map juliaMultiVal fields) ++ "])"
  ) constrs) ++ "] )"
juliaMultiVal x = error ("unknown juliaMultiVal for " ++ show x)
unlinesTrimLeft :: [String] -> String
unlinesTrimLeft = intercalate "\n"

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs

generateADTClasses :: [ADTDecl] -> [String]
generateADTClasses decls = concatMap generateADTClass (concatMap constructors decls)

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
  -- Equals function
  ("Base.:(==)(other::Any, self::" ++ name ++") = begin"):
    indentOnce
      (("if (!(other isa " ++ name ++ ")) return false end"):
      -- Compare every field
      map (\f -> "if(!eq(self." ++ f ++ ", other." ++ f ++ ")) return false end") fieldNames ++ 
      ["return true"]) ++
  ["end"] ++
  -- Field acceessors
  concatMap (\f ->
    ("function " ++ f ++ "(x :: " ++ name ++ ")") :
    indentOnce ["return x." ++ f] ++
    ["end"]
  ) fieldNames
  where fieldNames = map fst fields

generateFunctions :: IREnv -> [String]
generateFunctions (IREnv funcs adts consts) = do
  let adtClasses = generateADTClasses adts
  let constsStr = map (\(name, val) -> name ++ " = " ++ juliaVal val) consts
  let callableNames = [ n ++ "_gen"
                      | IRFunGroup{groupName=n, genFun=Just (e, _)} <- funcs
                      , null (fst (unwrapLambdas e)) ]
  let funcGroupsMonadic = concatMapM generateFunctionGroup funcs
  let (funcStrs, (globalVars, _)) = evalSupply $ runStateT funcGroupsMonadic ([], callableNames)
  let varsStr = map (\(mv, name)-> name ++ " = " ++ juliaMultiVal mv) globalVars
  adtClasses ++ constsStr ++ varsStr ++ funcStrs

generateFunctionGroup :: IRFunGroup -> GlobalVariableSupply [String]
generateFunctionGroup IRFunGroup {groupName=n, genFun=g, probFun=p, integFun=i, encodeFun=e, normalFun=nrm, groupDoc=doc} = do
  let preemble = [ "# === Function Group " ++ n ++ " ===\n# " ++ doc]
  gen <- fromMaybe (return []) (g <&> genF n "_gen")
  prob <- fromMaybe (return []) (p <&> genF n "_prob")
  integ <- fromMaybe (return []) (i <&> genF n "_integ")
  enc <- fromMaybe (return []) (e <&> genF n "_encode")
  norm <- fromMaybe (return []) (nrm <&> genF n "_normal")
  return $ preemble ++ gen ++ prob ++ integ ++ enc ++ norm
  where genF name suffix (e, d) = generateFunction (name ++ suffix) d e

generateFunction :: String -> String -> IRExpr -> GlobalVariableSupply [String]
generateFunction name doc expr = do
    let (args, reducedExpr) = unwrapLambdas expr
    let docLine = "# " ++ doc
    let l1 = "function " ++ name ++ "(" ++ intercalate ", " args ++ ")"
    block <- generateStatementBlock reducedExpr
    let lEnd = "end"
    return $ [docLine, l1] ++ indentOnce block ++ [lEnd]

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
    return ["throw(\"" ++ e ++ "\")"]

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
generateExpression (IRIndex lst idx) = do
    l <- generateExpression lst
    i <- generateExpression idx
    return $ "(" ++ l ++ ")[" ++ i ++ " + 1]"
generateExpression (IRLetIn name val body) = do
    v <- generateExpression val
    b <- generateExpression body
    return $ "(let " ++ name ++ " = " ++ v ++ "; " ++ b ++ " end)"
generateExpression (IRError e) =
    return $ "throw(\"" ++ e ++ "\")"
generateExpression x =
    error ("Unknown expression in Julia codegen: " ++ show x)

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
