{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module SPLL.Parser (
  testParse'
, pProg
, pExpr
, pIdentifier
, pValue
, tryParseProgram
, tryParseExpr
, reserved
) where

import Control.Monad
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import PrettyPrint
import Text.Pretty.Simple (pPrint)

import Data.Either (Either(..))
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad.Combinators.Expr
import Data.Void
import Control.Monad (void)
import Data.List.NonEmpty (NonEmpty (..))

import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import PredefinedFunctions (globalFEnv, parameterCount)
import SPLL.Prelude
import Debug.Trace
import Data.Functor ((<&>))
import Control.Monad.State
import Data.Functor.Identity
import Data.Foldable (foldl')

--import Text.Megaparsec.Debug (dbg)

dbg x y = y
--dbg x y = traceShow x y

--TODO: This parser can by necessity not disambiguate Apply f arg from certain special-treatment builtin functions,
-- like InjF

--TODO: This can't parse type annotations.
-- At some point this deserves fixing.

type Parser = Parsec Void String
type MonadParser m = (MonadParsec Void String m, MonadPlus m, MonadFail m, MonadState Int m)

demandUniqueNumber :: MonadState Int m => m Int
demandUniqueNumber = do
  old <- get
  put (old + 1)
  return old

sc :: MonadParser m => m ()
sc = L.space hspace1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: MonadParser m => m a -> m a
lexeme = L.lexeme sc

symbol :: MonadParser m => String -> m String
symbol = L.symbol sc

reserved :: [String]
reserved = ["data", "if", "then", "else", "let", "in", "theta", "subtree", "error", "ThetaTree", "Left", "Right"]

keyword :: MonadParser m => String -> m String
keyword = L.symbol sc

--Note: Won't parse capitalized constructors, if ever we add those.
pIdentifier :: MonadParser m => m String
pIdentifier = lexeme $ do
  x <- letterChar
  xs <- many alphaNumChar
  let ident = (x:xs)
  if ident `elem` reserved
    then fail $ "reserved word: " ++ ident
    else return ident

pUniform :: MonadParser m => m Expr
pUniform = do
  _ <- symbol "Uniform"
  return uniform

pNormal :: MonadParser m => m Expr
pNormal = do
  _ <- symbol "Normal"
  return normal

pIfThenElse :: MonadParser m => m Expr
pIfThenElse = do
  _ <- symbol "if"
  a <- pExpr
  _ <- symbol "then"
  b <- pExpr
  _ <- symbol "else"
  c <- pExpr
  return (ifThenElse a b c)

pLetIn :: MonadParser m => m Expr
pLetIn = do
  symbol "let"
  lhs <- pExpr
  symbol "="
  definition <- pExpr
  symbol "in"
  scope <- pExpr
  destr <- letInDestructor lhs
  return $ destr definition scope

-- Parses the identifier part of the letIn and constructs a accessors for letIns
-- Return type is a \v, b -> Let n = v in b
letInDestructor :: MonadParser m => Expr -> m (Expr -> Expr -> Expr)
letInDestructor (Var _ name) = return $ letIn name
letInDestructor (TCons _ a b) = do
  a' <- letInDestructor a
  b' <- letInDestructor b
  return $ \v body -> a' (tfst v) (b' (tsnd v) body)
letInDestructor (InjF _ "left" [x]) = do
  x' <- letInDestructor x
  return $ \v -> x' (sfromLeft v)
letInDestructor (InjF _ "right" [x]) = do
  x' <- letInDestructor x
  return $ \v -> x' (sfromRight v)
letInDestructor (Null _) = return $ \v b -> ifThenElse (isNull v) b (Error makeTypeInfo "RHS of letin is longer than LHS")
letInDestructor (Cons _ x xs) = do
  x' <- letInDestructor x
  xs' <- letInDestructor xs
  id <- demandUniqueNumber
  let varName = "p_d" ++ show id
  return $ \v body -> letIn varName v (x' (lhead (var varName)) (xs' (ltail (var varName)) body))
letInDestructor _ = fail "LHS of a letIn sould be an identifier or a complex type of identifiers"

pError :: MonadParser m => m Expr
pError = do
  keyword "error"
  char '"'
  message <- many (noneOf "\"")
  char '"'
  return (Error makeTypeInfo message)

pMaybeApply :: MonadParser m => m Expr
pMaybeApply = choice [parens pExpr, pVar]

pExpr :: MonadParser m => m Expr
pExpr = expr
{-
pExpr = dbg "expr" $ choice [
  try pBinaryOp,
  try pParensExpr,
  try pTheta,
  pIfThenElse,
  pUniform,
  pNormal,
  pLetIn,
  try pBinaryF,
  try pApply,
  try pConst,

  pVar
  ]
-}

-- TODO: I think this parser should accept any pExpr instead of identifiers. Might get ambiguous parses though.

pTheta :: MonadParser m => m Expr
pTheta = dbg "theta" $ do
  keyword "theta"
  thetaExpr <- pExpr
  symbol "@"
  ix <- pInt
  return $ theta thetaExpr ix

pSubtree :: MonadParser m => m Expr
pSubtree = dbg "subtree" $ do
  keyword "subtree"
  thetaExpr <- pExpr
  symbol "@"
  ix <- pInt
  return $ subtree thetaExpr ix

-- just to make this parser quite unambiguous, we're going to demand parens around both ops.
pBinaryOp :: MonadParser m => m Expr
pBinaryOp = dbg "binOp" $ do
  arg1 <- parens pExpr
  op <- pOp
  arg2 <- parens pExpr
  case op of
    ">=" -> return $ arg1 #># arg2
    _ -> fail $ "unknown operator: " ++ op

pOp :: MonadParser m => m String
pOp = lexeme $ do
    op <- some opChar
    if op `elem` reservedOps
        then fail $ "Reserved operator: " ++ op
        else return op
  where
    opChar = oneOf ("!#$%&*+.:/<=>?@\\^|-~" :: String)
    reservedOps = ["..","::","=","\\","|","<-","->","@","~","=>"]

applyN :: Expr -> [Expr] -> Expr
applyN function [] = function
applyN function (arg:args) = applyN (apply function arg) args -- $ foldl (\a f -> Apply makeTypeInfo f a) (Var makeTypeInfo function) (map (Var makeTypeInfo) args)

construct1 :: (Expr -> Expr) -> [Expr] -> Expr
construct1 constructor [arg] = constructor arg
construct1 _ _ = error "tried to apply the wrong number of arguments."

construct2 :: (Expr -> Expr -> Expr) -> [Expr] -> Expr
construct2 constructor [arg1, arg2] = constructor arg2 arg2
construct2 _ _ = error "tried to apply the wrong number of arguments."

constructN :: Int -> ([Expr] -> Expr) -> [Expr] -> Expr
constructN n constructor args | n == length args = constructor args
constructN _ _ _ = error "tried to apply the wrong number of arguments."

-- Constructs a partially applied function, by wrapping the constructor in lambdas and using the bound variables as missing parameters
constructNPartial :: MonadParser m => Int -> ([Expr] -> Expr) -> [Expr] -> m Expr
constructNPartial expected constructor params = do
  let missingParamCnt = expected - length params
  substituteParamIDs <- replicateM missingParamCnt demandUniqueNumber
  let substituteParamNames = map (("p_m" ++) . show) substituteParamIDs
  let extendedArgs = params ++ map var substituteParamNames
  return $ foldl (flip (#->#)) (constructor extendedArgs) substituteParamNames

pVar :: MonadParser m => m Expr
pVar = do
  varname <- lexeme pIdentifier
  return $ var varname

binaryFs :: [(String, Expr -> Expr -> Expr)]
binaryFs = [
  ("multF", (#*#)),
  ("multI", (#<*>#)),
  ("plusF", (#+#)),
  ("plusI", (#<+>#))
  ]

unaryFs :: [(String, Expr -> Expr)]
unaryFs = [
  ("negate", negF)
  ]

pValue :: MonadParser m => m Value
pValue = choice [pBool, try pFloat, pIntVal, pTupleVal, pEither, pAny, pList <&> constructVList, pThetaTree <&> VThetaTree]

pTupleVal :: MonadParser m => m Value
pTupleVal = do
  (symbol "(")
  val1 <- pValue
  _ <- symbol ","
  val2 <- pValue
  (symbol ")")
  return (VTuple val1 val2)

pConst :: MonadParser m => m Expr
pConst = do
  val <- pValue
  return (Constant makeTypeInfo val)

pBool :: MonadParser m => m Value
pBool = do
  b <- choice [keyword "True" >> return True, keyword "False" >> return False]
  return (VBool b)

pFloat :: MonadParser m => m Value
pFloat = dbg "float" $ do
  sign <- optional (symbol "-")
  f <- lexeme L.float
  case sign of
    Nothing -> return (VFloat f)
    Just "-" -> return (VFloat (-f))

pIntVal :: MonadParser m => m Value
pIntVal = dbg "int" $ do
  sign <- optional (symbol "-")
  i <- lexeme L.decimal
  case sign of
    Nothing -> return (VInt i)
    Just "-" -> return (VInt (-i))


pInt :: MonadParser m => m Int
pInt = do
  sign <- optional (symbol "-")
  i <- lexeme L.decimal
  case sign of
    Nothing -> return i
    Just "-" -> return (-i)

pEither :: MonadParser m => m Value
pEither = do
  side <- choice[keyword "Left", keyword "Right"]
  v <- pValue
  case side of
    "Left" -> return $ VEither (Left v)
    "Right" -> return $ VEither (Right v)
    s -> fail $ "Unrecognized Either constructor: " ++ s

pAny :: MonadParser m => m Value
pAny = do
  keyword "ANY"
  return VAny

pThetaTree :: MonadParser m => m ThetaTree
pThetaTree = do
  keyword "ThetaTree"
  symbol "["
  thetas <- (L.signed sc (lexeme L.float)) `sepBy` symbol ","
  symbol "]"
  symbol "["
  subtrees <- pThetaTree `sepBy` symbol ","
  symbol "]"
  return $ ThetaTree thetas subtrees

pBinaryF :: MonadParser m => m Expr
pBinaryF = do
  op <- choice (map (symbol . fst) binaryFs)
  left <- pExpr
  right <- pExpr
  case (lookup op binaryFs) of
    Nothing -> error "unexpected parse error"
    Just opconstructor -> return (opconstructor left right)

parseFromList :: MonadParser m => [(String, b)] -> m b
parseFromList kvlist = do
  key <- choice (map (symbol . fst) kvlist)
  case (lookup key kvlist) of
    Nothing -> error "unexpected parse error"
    Just value -> return value

rTypes :: [(String, RType)]
rTypes = [("Int", TInt), ("Float", TFloat), ("Bool", TBool), ("Symbol", TSymbol)]

-- this function needs to handle compound types such as "Int -> Float" as well 
-- first, we want to try parsing a compound type, and if that fails assume that a simple type is there instead.
pType :: MonadParser m => m RType
pType = dbg "type" $ do
  t <- choice [pCompoundType, pSimpleType]
  return t

pCompoundType :: MonadParser m => m RType
pCompoundType = parens $ do
  left <- pSimpleType
  combinator <- pTypeCombinator
  right <- SPLL.Parser.pType
  return $ combinator left right
    where
      pTypeCombinator = parseFromList combinators
      combinators = [("->", TArrow), ("," , Tuple)]

pSimpleType :: MonadParser m => m RType
pSimpleType =
  parseFromList rTypes

pList :: MonadParser m => m [Value]
pList = do
  (symbol "[")
  values <- pCSV
  (symbol "]")
  return values

pRange :: MonadParser m => m (Value, Value)
pRange = do
  (symbol "[")
  from <- valueParser
  (symbol "..")
  to <- valueParser
  (symbol "]")
  return (from, to)

pListExpr :: MonadParser m => m Expr
pListExpr = do
  (symbol "[")
  exprs <- expr `sepBy` (symbol ",")
  (symbol "]")
  return (foldr cons nul exprs)

valueParser :: MonadParser m => m Value
valueParser = pValue

pCSV :: MonadParser m => m [Value]
pCSV = valueParser `sepBy` (symbol ",")

pDefinition :: MonadParser m => m (Either FnDecl NeuralDecl)
pDefinition = do
  x <- choice [fmap Right pNeural, fmap Left pFunction]
  doesNotContinue
  return x

--TODO: Add validation via AutoNeural.
pNeural :: MonadParser m => m NeuralDecl
pNeural = dbg "neural" $ do
  _ <- keyword "neural"
  name <- pIdentifier
  _ <- symbol "::"
  ty <- SPLL.Parser.pType
  tag <- optional (symbol "of" *> listOrRange)
  return (name, ty, tag)
    where
      listOrRange = choice [try (pList >>= return . EnumList), pRange >>= return . EnumRange]


pFunction :: MonadParser m => m FnDecl
pFunction = dbg "function" $ do
  name <- pIdentifier
  args <- many pIdentifier
  _ <- symbol "="
  e <- pExpr
  let lambdas = foldr (#->#) e args
  return (name, lambdas)

pADT :: MonadParser m => m ADTDecl
pADT = do
  keyword "data"
  name <- pIdentifier
  symbol "="
  constrs <- pADTConstructor `sepBy` symbol "|"
  doesNotContinue
  return (name, constrs)

pADTConstructor :: MonadParser m => m ADTConstructorDecl
pADTConstructor = dbg "ADT Constr" $ do
  name <- pIdentifier
  rts <- many $ do
    fieldName <- pIdentifier
    symbol "::"
    fieldType <- choice [SPLL.Parser.pType <&> Left, pIdentifier <&> Right]
    let fieldRT = case fieldType of
                    Left rt -> rt
                    Right adt -> TADT adt
    return (fieldName, fieldRT)
  return (name, rts)

doesNotContinue :: MonadParser m => m ()
doesNotContinue = choice [eof, void eol]

pProg :: MonadParser m => m Program
pProg = do
  sc
  adts <- dbg "trying ADTs" (many pADT)
  defs <- dbg "trying definition" (many pDefinition)
  _ <- eof
  return (aggregateDefinitions adts defs)

aggregateDefinitions :: [ADTDecl] -> [Either FnDecl NeuralDecl] -> Program
aggregateDefinitions adts (Left fn : tail) = Program (fn:fns) neurals adtz
  where
    Program fns neurals adtz = aggregateDefinitions adts tail
aggregateDefinitions adts (Right nr : tail) = Program fns (nr:neurals) adtz
  where
    Program fns neurals adtz = aggregateDefinitions adts tail
aggregateDefinitions adts [] = Program [] [] adts

tryParseExpr :: FilePath -> String -> Either (ParseErrorBundle String Void) Expr
tryParseExpr filename src = do
  (res, _) <- runParser (runStateT parseExpr 0) filename src
  return res

tryParseProgram :: FilePath -> String -> Either (ParseErrorBundle String Void) Program
tryParseProgram filename src = do
  (prog, _) <- runParser (runStateT pProg 0) filename src
  case normalize prog of
    Right prog -> Right prog
    Left err -> Left $ ParseErrorBundle ((FancyError 0 (Set.singleton (ErrorFail err))) :| []) emptyPosState

emptyPosState :: PosState String
emptyPosState = PosState "" 0 (initialPos "<string>") (mkPos 0) ""

testParse' :: IO ()
testParse' = do
  let filename = "../../test.spll"
  source <- readFile filename
  let result = runParser (runStateT pProg 0) filename source
  case result of
    Left err -> putStrLn (errorBundlePretty err)
    Right (prog, _) -> do
      let flatProg = prog
      putStrLn "ASDF1"
      mapM_ putStrLn (prettyPrintProg prog)
      putStrLn "ASDF2"
      putStrLn (pPrintProg prog)
      putStrLn "ASDF3"
      pPrint flatProg
      putStrLn "ASDF4"
      print prog


pNull :: MonadParser m => m Expr
pNull = do
  _ <- symbol "[]"
  return $ nul

pTuple :: MonadParser m => m Expr
pTuple = parens $ do
  x <- expr
  _ <- symbol ","
  y <- expr
  return $ tuple x y


-- | Parse atomic expressions (no recursion)
atom :: MonadParser m => m Expr
atom = choice [
    pNull,
    try (pTuple),
    try (pListExpr),
    try (parens expr),  -- Parenthesized expressions first
    pUniform,     -- Built-in distributions
    pNormal,
    pConst,       -- Constants (numbers)
    var <$> pIdentifier  -- Variables last
  ] <* sc

-- | Parse expressions that start with keywords
keywordExpr :: MonadParser m => m Expr
keywordExpr = dbg "keywordExpr" $ choice [
    pIfThenElse,
    pLetIn,
    pLambda,
    pTheta,
    pSubtree,
    pError
  ] <* sc

-- | Lambda expressions
pLambda :: MonadParser m => m Expr
pLambda = do
    _ <- symbol "\\"
    param <- pIdentifier
    _ <- symbol "->"
    body <- expr
    return $ param #-># body

-- | Parse function application
-- This handles both normal application and built-in functions like multF
application :: MonadParser m => m Expr
application = dbg "application" $do
    func <- try atom
    args <- try $ many (try atom <|> try (parens expr))
    case func of
        Var _ name -> case lookup name binaryFs of
            Just constructor -> return (construct2 constructor args)
            Nothing -> case lookup name unaryFs of
                Just constructor -> return (construct1 constructor args)
                Nothing -> case lookup name (globalFEnv []) of
                  Just _ -> 
                    if length args == (parameterCount [] name) then
                      return (constructN (parameterCount [] name) (injF name) args)
                    else if length args < (parameterCount [] name) then
                      constructNPartial (parameterCount [] name) (injF name) args
                    else
                      fail $ "Function " ++ name ++ " expects " ++ show (parameterCount [] name) ++ " parameters, but got " ++ show (length args)
                  Nothing -> return $ foldl apply func args
        _ -> return $ foldl apply func args


-- | Main expression parser using makeExprParser
expr :: MonadParser m => m Expr
expr = dbg "expr" $ makeExprParser term opTable
  where
    term = choice [
        try application,
        try keywordExpr,
        atom
      ]

-- | Helper for debuggable subparsers
withDebug :: MonadParser m => String -> m a -> m a
withDebug label p = dbg label p

-- | Top level entry point
parseExpr :: MonadParser m => m Expr
parseExpr = sc *> expr <* eof

-- | Parse a parenthesized expression
parens :: MonadParser m => m a -> m a
parens = between (char '(' *> sc) (char ')' *> sc)

-- | Parse an identifier (simple Haskell-style variable)
identifier :: MonadParser m => m String
identifier = (:) <$> letterChar <*> many alphaNumChar <* sc

-- | Parse an atomic expression (identifier or parenthesized expression)
term :: MonadParser m => m Expr
term =  parens expr
    <|> pConst
    <|> var <$> identifier


-- | Handle function application
appTable :: MonadParser m => m Expr
appTable = do
  f <- term
  args <- many term
  return $ foldl apply f args

multLikeOpList :: [([Char], Expr -> Expr -> Expr)]
multLikeOpList = [("**", (#<*>#)), ("*", (#*#)), ("/", (#/#)), ("&&", (#&&#))]

addLikeOpList :: [([Char], Expr -> Expr -> Expr)]
addLikeOpList = [("++", (#<+>#)), ("+", (#+#)), ("-", \a b -> a #+# (negF b)), ("||", (#||#))]

listManipulationOpList :: [([Char], Expr -> Expr -> Expr)]
listManipulationOpList = [(":", (#:#))]

cmpOpList :: [([Char], Expr -> Expr -> Expr)]
cmpOpList = [(">", (#>#)), ("<", (#<#)), (":", (#:#))]

funLikeOps :: [([Char], Expr -> Expr)]
funLikeOps = [("not", (#!#))]

mkInfixOp :: MonadParser m => [([Char], Expr -> Expr -> Expr)] -> [Operator m Expr]
mkInfixOp tbl = map infx tbl
  where infx (name, f) = InfixL (f <$ symbol name)

mkPrefixOp :: MonadParser m => [([Char], Expr -> Expr)] -> [Operator m Expr]
mkPrefixOp tbl = map infx tbl
  where infx (name, f) = Prefix (f <$ symbol name)


-- | Operator table (precedence and associativity)
opTable :: MonadParser m => [[Operator m Expr]]
opTable =
  [ mkPrefixOp funLikeOps,
    mkInfixOp multLikeOpList,
    mkInfixOp addLikeOpList,
    mkInfixOp listManipulationOpList,
    mkInfixOp cmpOpList
  ]


-- | Top-level parser
expressionParser :: MonadParser m => m Expr
expressionParser = sc *> expr <* eof

type ExprBuilder m = [Expr] -> m (Either String Expr)
type BuilderMap m = Map.Map String (ExprBuilder m)

-- | Normalize a Program
--  After normalization, all Vars should be properly resolved as either a ReadNN, a InjF, or a plain Var.
normalize :: Program -> Either String Program
normalize prog =
  let neuralMap = buildNeuralMap (neurals prog) :: BuilderMap (State Int)
      invMap = buildInvMap (adts prog)
      globalFunctionMap = globalFunctions prog
      injFMap = buildInjFMap prog
      --benignVars = collectBenignVars prog
      paramMap = Map.unions [neuralMap, invMap, injFMap]  -- neural builders take precedence
      functionMap = Map.unions [globalFunctionMap, injFMap] -- InjF are in both Maps, because they can be partially applied, which means they can have zero parameters
  in if Map.disjoint invMap neuralMap && Map.disjoint invMap globalFunctionMap && Map.disjoint neuralMap globalFunctionMap
    then do
      --mapExprInProgram (normalizeExpr (builderMap, functionMap, Set.empty)) prog
      evalState (mapExprInProgram (normalizeExpr (paramMap, functionMap, Set.empty)) prog) 0
    else Left $ "Found identifiers that are in multiple scopes."

-- Build maps from identifiers to expression builders
buildNeuralMap :: MonadState Int m => [NeuralDecl] -> BuilderMap m
buildNeuralMap decls = Map.fromList
  [(name, \[arg] -> return $ Right $ readNN name arg) | (name, _, _) <- decls]

buildInvMap :: MonadState Int m => [ADTDecl] -> BuilderMap m
buildInvMap adts = Map.fromList
  [(name, \args -> case args of
    a | length a /= parameterCount adts name -> do
      let missingParamCnt = parameterCount adts name - length a
      substituteParamIDs <- replicateM missingParamCnt demandUniqueNumber
      let substituteParamNames = map (("p_m" ++) . show) substituteParamIDs
      let extendedArgs = args ++ map var substituteParamNames
      return $ Right $ foldl (flip (#->#)) (injF name extendedArgs) substituteParamNames
    _ -> return $ Right $ injF name args)
   | name <- fNames]
  where fNames = map fst (globalFEnv adts)

globalFunctions :: MonadState Int m =>  Program -> BuilderMap m
globalFunctions prog = Map.fromList ([(name, \[] -> return $ Right $ var name) | (name, _) <- functions prog])

buildInjFMap:: MonadState Int m => Program -> BuilderMap m
buildInjFMap prog = Map.fromList 
  [(name, \[] -> do
      substituteParamIDs <- replicateM (parameterCount (adts prog) name) demandUniqueNumber
      let substituteParamNames = map (("p_m" ++) . show) substituteParamIDs
      let args = map var substituteParamNames
      return $ Right $ foldl (flip (#->#)) (injF name args) substituteParamNames)
    | (name, _) <- globalFEnv (adts prog)]

-- Collect all variables that should not be transformed
collectBenignVars :: Program -> Set.Set String
collectBenignVars prog = Set.fromList [name | (name, _) <- functions prog]

-- Main expression normalization function
normalizeExpr :: MonadState Int m => (BuilderMap m, BuilderMap m, Set.Set String) -> Expr -> m (Either String Expr)
normalizeExpr env@(parametricBuilders, atomicBuilders, benign) expr =
  case expr of
    -- Handle scopes first, adding bound variables before processing sub-expressions
    Lambda ti name body -> do
      let body' = normalizeExpr (parametricBuilders, atomicBuilders, Set.insert name benign) body
      fmap (fmap (Lambda ti name)) body'

    LetIn ti name def body -> do
      -- def is normalized with current scope
      let def' = normalizeExpr env def
      -- body is normalized with name added to scope
      let body' = normalizeExpr (parametricBuilders, atomicBuilders, Set.insert name benign) body
      let a = fmap (fmap (LetIn ti name)) def'
      fmap (<*>) a <*> body'

    -- For all other expressions, normalize sub-expressions first then check for Apply pattern
    _ -> do
      subExprs <- fmap sequence (mapM (normalizeExpr env) (getSubExprs expr))
      let mExpr = fmap (setSubExprs expr) subExprs
      case mExpr of
        Left s -> return $ Left s
        Right expr' ->
          case expr' of
            -- Start of an Apply chain
            Apply ti (Apply _ _ _) _ ->
              -- Need to collect all args in the chain and find base function
              let (base, args) = collectApplyChain expr
              in case base of
                Var _ fname | Just builder <- Map.lookup fname parametricBuilders -> do
                  build <- builder args
                  case build of
                    Left _ -> return $ Right expr' -- This prevents InjFs, which have multiple arguments from failing to build because here only one argument is applied
                    e -> return e
                _ -> return $ Right expr
            Apply ti (Var _ fname) arg
              | not (Set.member fname benign)
              , Just builder <- Map.lookup fname parametricBuilders -> do
                build <- builder [arg]
                case build of
                  Left _ -> return $ Right expr' -- This prevents InjFs, which have multiple arguments from failing to build because here only one argument is applied
                  e -> return e
            Var ti fname
              | not (Set.member fname benign)
              , Just builder <- Map.lookup fname atomicBuilders -> builder []
            _ -> return $ Right expr'

--replaceExpr :: Expr -> Expr -> Expr
--replaceExpr

-- Returns (base expression, arguments in application order)
collectApplyChain :: Expr -> (Expr, [Expr])
collectApplyChain (Apply _ left arg) =
  let (base, args) = collectApplyChain left
  in (base, args ++ [arg])  -- maintain order of application
-- Quick and dirty fix for multi parameter InjFs. The normalizatzion first creates a 1 parameter InjF and then stops with the normalization
-- We bypass this by tricking the normalization  that the InjF is in reality an application on a variable
collectApplyChain (InjF t name args) = (Var t name, args)
collectApplyChain e = (e, [])

-- Helper to map over all expressions in a program
mapExprInProgram :: MonadState Int m => (Expr -> m (Either String Expr)) -> Program -> m (Either String Program)
mapExprInProgram f prog = do
  newFuncs <- mapM (\(name, expr) -> f expr >>= \e -> return (name, e)) (functions prog)
  let newFuncs' = mapM (\(s, e) -> (e <&> \ex -> (s, ex))) newFuncs
  case newFuncs' of
    Right fs -> return $ Right $ prog { functions = fs }
    Left err -> return $ Left err
