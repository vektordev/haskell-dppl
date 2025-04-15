module SPLL.Parser (
  testParse
, pProg
, pExpr
, pIdentifier
, pValue
, tryParseProgram
, tryParseExpr
, testParser
, reserved
) where

--import Control.Applicative
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
import PredefinedFunctions (globalFenv, parameterCount)
import SPLL.Prelude

--import Text.Megaparsec.Debug (dbg)
dbg x y = y

--TODO: This parser can by necessity not disambiguate Apply f arg from certain special-treatment builtin functions,
-- like InjF

--TODO: This can't parse type annotations.
-- At some point this deserves fixing.

type Parser = Parsec Void String


sc = L.space hspace1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

reserved :: [String]
reserved = ["if", "then", "else", "let", "in"]

keyword :: String -> Parser String
keyword = L.symbol sc

--Note: Won't parse capitalized constructors, if ever we add those.
pIdentifier :: Parser String
pIdentifier = lexeme $ do
  x <- lowerChar
  xs <- many alphaNumChar
  let ident = (x:xs)
  if ident `elem` reserved
    then fail $ "reserved word: " ++ ident
    else return ident

pUniform :: Parser Expr
pUniform = do
  _ <- symbol "Uniform"
  return uniform

pNormal :: Parser Expr
pNormal = do
  _ <- symbol "Normal"
  return normal

pIfThenElse :: Parser Expr
pIfThenElse = do
  _ <- symbol "if"
  a <- pExpr
  _ <- symbol "then"
  b <- pExpr
  _ <- symbol "else"
  c <- pExpr
  return (ifThenElse a b c)

pLetIn :: Parser Expr
pLetIn = do
  _ <- symbol "let"
  name <- pIdentifier
  _ <- symbol "="
  definition <- pExpr
  _ <- symbol "in"
  scope <- pExpr
  return (letIn name definition scope)

--parens :: Parser a -> Parser a
--parens = between (symbol "(") (symbol ")")

pMaybeApply :: Parser Expr
pMaybeApply = choice [parens pExpr, pVar]

pParensExpr = dbg "parensExpr" $ parens pExpr

pExpr :: Parser Expr
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
pApply :: Parser Expr
pApply = dbg "apply" $ do
  function <- pMaybeApply
  args <- some pMaybeApply
  case function of
    (Var _ name) -> case lookup name binaryFs of
      Just constructor -> return (construct2 constructor args)
      Nothing -> case lookup name unaryFs of
        Just constructor -> return (construct1 constructor args)
        Nothing -> case lookup name injFs of
          Just (expectedParams, constructor) -> return (constructN expectedParams constructor args)
          Nothing -> return (applyN function args)
    otherwise -> return (applyN function args)

pTheta :: Parser Expr
pTheta = dbg "theta" $ do
  thetaName <- pIdentifier
  _ <- symbol "["
  ix <- pInt
  _ <- symbol "]"
  return $ theta (var thetaName) ix

-- just to make this parser quite unambiguous, we're going to demand parens around both ops.
pBinaryOp :: Parser Expr
pBinaryOp = dbg "binOp" $ do
  arg1 <- parens pExpr
  op <- pOp
  arg2 <- parens pExpr
  case op of
    ">=" -> return $ arg1 #># arg2
    _ -> fail $ "unknown operator: " ++ op

pOp :: Parser String
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

pVar :: Parser Expr
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

injFs :: [(String, (Int, [Expr] -> Expr))]
injFs = [(name, (parameterCount name, injF name)) | (name, _) <- globalFenv]

pValue :: Parser Value
pValue = choice [pBool, try pFloat, pIntVal, pTupleVal, pList>>=(return . constructVList)]

pTupleVal :: Parser Value
pTupleVal = do
  (symbol "(")
  val1 <- pValue
  _ <- symbol ","
  val2 <- pValue
  (symbol ")")
  return (VTuple val1 val2)

pConst :: Parser Expr
pConst = do
  val <- pValue
  return (Constant makeTypeInfo val)

pBool :: Parser Value
pBool = do
  b <- choice [keyword "True" >> return True, keyword "False" >> return False]
  return (VBool b)

pFloat :: Parser Value
pFloat = do
  f <- L.signed sc (lexeme L.float)
  return (VFloat f)

pIntVal :: Parser Value
pIntVal = do
  i <- L.signed sc (lexeme L.decimal)
  return (VInt i)

pInt :: Parser Int
pInt = L.signed sc (lexeme L.decimal)

pBinaryF :: Parser Expr
pBinaryF = do
  op <- choice (map (symbol . fst) binaryFs)
  left <- pExpr
  right <- pExpr
  case (lookup op binaryFs) of
    Nothing -> error "unexpected parse error"
    Just opconstructor -> return (opconstructor left right)

parseFromList :: [(String, b)] -> Parser b
parseFromList kvlist = do
  key <- choice (map (symbol . fst) kvlist)
  case (lookup key kvlist) of
    Nothing -> error "unexpected parse error"
    Just value -> return value

rTypes :: [(String, RType)]
rTypes = [("Int", TInt), ("Float", TFloat), ("Symbol", TSymbol)]

-- this function needs to handle compound types such as "Int -> Float" as well 
-- first, we want to try parsing a compound type, and if that fails assume that a simple type is there instead.
pType :: Parser RType
pType = dbg "type" $ do
  t <- choice [pCompoundType, pSimpleType]
  return t

pCompoundType :: Parser RType
pCompoundType = parens $ do
  left <- pSimpleType
  combinator <- pTypeCombinator
  right <- SPLL.Parser.pType
  return $ combinator left right
    where
      pTypeCombinator = parseFromList combinators
      combinators = [("->", TArrow), ("," , Tuple)]

pSimpleType :: Parser RType
pSimpleType = 
  parseFromList rTypes

pList :: Parser [Value]
pList = do
  (symbol "[")
  values <- pCSV
  (symbol "]")
  return values

pRange :: Parser (Value, Value)
pRange = do
  (symbol "[")
  from <- valueParser
  (symbol "..")
  to <- valueParser
  (symbol "]")
  return (from, to)

pListExpr :: Parser Expr
pListExpr = do
  (symbol "[")
  exprs <- expr `sepBy` (symbol ",")
  (symbol "]")
  return (foldr cons nul exprs)

valueParser :: Parser Value
valueParser = pValue

pCSV :: Parser [Value]
pCSV = valueParser `sepBy` (symbol ",")

pDefinition :: Parser (Either FnDecl NeuralDecl)
pDefinition = do
  x <- choice [pNeural, pFunction]
  doesNotContinue
  return x

--TODO: Add validation via AutoNeural.
pNeural :: Parser (Either FnDecl NeuralDecl)
pNeural = dbg "neural" $ do
  _ <- keyword "neural"
  name <- pIdentifier
  _ <- symbol "::"
  ty <- SPLL.Parser.pType
  tag <- optional (symbol "of" *> listOrRange)
  return $ Right (name, ty, tag)
    where
      listOrRange = choice [try (pList >>= return . EnumList), pRange >>= return . EnumRange]


pFunction :: Parser (Either FnDecl NeuralDecl)
pFunction = dbg "function" $ do
  name <- pIdentifier
  args <- many pIdentifier
  _ <- symbol "="
  e <- pExpr
  let lambdas = foldr (#->#) e args
  return (Left (name, lambdas))

doesNotContinue :: Parser ()
doesNotContinue = choice [eof, void eol]

pProg :: Parser Program
pProg = do
  sc
  defs <- dbg "trying definition" (many pDefinition)
  _ <- eof
  return (aggregateDefinitions defs)

aggregateDefinitions :: [Either FnDecl NeuralDecl] -> Program
aggregateDefinitions (Left fn : tail) = Program (fn:fns) neurals
  where
    Program fns neurals = aggregateDefinitions tail
aggregateDefinitions (Right nr : tail) = Program fns (nr:neurals)
  where
    Program fns neurals = aggregateDefinitions tail
aggregateDefinitions [] = Program [] []

tryParseExpr :: FilePath -> String -> Either (ParseErrorBundle String Void) Expr
tryParseExpr filename src = runParser parseExpr filename src

tryParseProgram :: FilePath -> String -> Either (ParseErrorBundle String Void) Program
tryParseProgram filename src = do
  prog <- runParser pProg filename src
  case normalize prog of
    Right prog -> Right prog
    Left err -> Left $ ParseErrorBundle ((FancyError 0 (Set.singleton (ErrorFail err))) :| []) emptyPosState

emptyPosState :: PosState String
emptyPosState = PosState "" 0 (SourcePos "" (mkPos 0)(mkPos 0)) (mkPos 0) ""

testParse :: IO ()
testParse = do
  let filename = "../../test.spll"
  source <- readFile filename
  let result = runParser (pProg :: Parser Program) filename source
  case result of
    Left err -> putStrLn (errorBundlePretty err)
    Right prog -> do
      let flatProg = prog
      putStrLn "ASDF1"
      mapM_ putStrLn (prettyPrintProg prog)
      putStrLn "ASDF2"
      putStrLn (pPrintProg prog)
      putStrLn "ASDF3"
      pPrint flatProg
      putStrLn "ASDF4"
      print prog


pNull :: Parser Expr
pNull = do
  _ <- symbol "[]"
  return $ nul

pTuple :: Parser Expr
pTuple = parens $ do
  x <- expr
  _ <- symbol ","
  y <- expr
  return $ tuple x y


-- | Parse atomic expressions (no recursion)
atom :: Parser Expr
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
keywordExpr :: Parser Expr
keywordExpr = choice [
    pIfThenElse,
    pLetIn,
    pLambda
  ] <* sc

-- | Lambda expressions
pLambda :: Parser Expr
pLambda = do
    _ <- symbol "\\"
    param <- pIdentifier
    _ <- symbol "->"
    body <- expr
    return $ param #-># body

-- | Parse function application
-- This handles both normal application and built-in functions like multF
application :: Parser Expr
application = do
    func <- try atom
    args <- many (try atom <|> try (parens expr))
    case func of
        Var _ name -> case lookup name binaryFs of
            Just constructor -> return (construct2 constructor args)
            Nothing -> case lookup name unaryFs of
                Just constructor -> return (construct1 constructor args)
                Nothing -> case lookup name injFs of
                  Just (expectedParams, constructor) -> return (constructN expectedParams constructor args)
                  Nothing -> return $ foldl apply func args
        _ -> return $ foldl apply func args


-- | Main expression parser using makeExprParser
expr :: Parser Expr
expr = makeExprParser term opTable
  where
    term = choice [
        try application,
        try keywordExpr,
        atom
      ]

-- | Helper for debuggable subparsers
withDebug :: String -> Parser a -> Parser a
withDebug label p = dbg label p

-- | Top level entry point
parseExpr :: Parser Expr
parseExpr = sc *> expr <* eof

-- | Parse a parenthesized expression
parens :: Parser a -> Parser a
parens = between (char '(' *> sc) (char ')' *> sc)

-- | Parse an identifier (simple Haskell-style variable)
identifier :: Parser String
identifier = (:) <$> letterChar <*> many alphaNumChar <* sc

-- | Parse an atomic expression (identifier or parenthesized expression)
term :: Parser Expr
term =  parens expr
    <|> pConst
    <|> var <$> identifier


-- | Handle function application
appTable :: Parser Expr
appTable = do
  f <- term
  args <- many term
  return $ foldl apply f args

arithOpList :: [([Char], Expr -> Expr -> Expr)]
arithOpList = [("++", (#<+>#)), ("**", (#<*>#)), ("+", (#+#)), ("*", (#*#)), ("/", (#/#)), (":", (#:#)),
          ("-", \a b -> a #+# (negF b))]

cmpOpList :: [([Char], Expr -> Expr -> Expr)]
cmpOpList = [(">", (#>#)), ("<", (#<#))]

funLikeOps :: [([Char], Expr -> Expr)]
funLikeOps = [("not", (#!#))]

mkInfixOp :: [([Char], Expr -> Expr -> Expr)] -> [Operator Parser Expr]
mkInfixOp tbl = map infx tbl
  where infx (name, f) = InfixL (f <$ symbol name)

mkPrefixOp :: [([Char], Expr -> Expr)] -> [Operator Parser Expr]
mkPrefixOp tbl = map infx tbl
  where infx (name, f) = Prefix (f <$ symbol name)


-- | Operator table (precedence and associativity)
opTable :: [[Operator Parser Expr]]
opTable =
  [ mkPrefixOp funLikeOps,
    mkInfixOp arithOpList,  -- Left-associative operators
    mkInfixOp cmpOpList
  ]


-- | Top-level parser
expressionParser :: Parser Expr
expressionParser = sc *> expr <* eof

-- | Test the parser
testParser :: String -> Either (ParseErrorBundle String Void) Expr
testParser input = parse expressionParser "" input



type ExprBuilder = [Expr] -> Either String Expr
type BuilderMap = Map.Map String ExprBuilder

-- | Normalize a Program
--  After normalization, all Vars should be properly resolved as either a ReadNN, a InjF, or a plain Var.
normalize :: Program -> Either String Program
normalize prog =
  let neuralMap = buildNeuralMap (neurals prog)
      invMap = buildInvMap globalFenv
      functionMap = globalFunctions prog
      --benignVars = collectBenignVars prog
      builderMap = Map.unions [neuralMap, invMap]  -- neural builders take precedence
  in if Map.disjoint invMap neuralMap && Map.disjoint invMap functionMap && Map.disjoint neuralMap functionMap
    then mapExprInProgram (normalizeExpr (builderMap, functionMap, Set.empty)) prog
    else Left $ "Found identifiers that are in multiple scopes."

-- Build maps from identifiers to expression builders
buildNeuralMap :: [NeuralDecl] -> BuilderMap
buildNeuralMap decls = Map.fromList
  [(name, \[arg] -> Right $ readNN name arg) | (name, _, _) <- decls]

buildInvMap :: [(String, a)] -> BuilderMap
buildInvMap fenv = Map.fromList
  [(name, \args -> case args of
    [] -> Left $ name ++ " requires arguments"
    --[_] -> Left $ name ++ " requires multiple arguments"
    _ -> Right $ injF name args)
   | (name, _) <- fenv]

globalFunctions :: Program -> BuilderMap
globalFunctions prog = Map.fromList [(name, \[] -> Right $ var name) | (name, _) <- functions prog]

-- Collect all variables that should not be transformed
collectBenignVars :: Program -> Set.Set String
collectBenignVars prog = Set.fromList [name | (name, _) <- functions prog]

-- Main expression normalization function
normalizeExpr :: (BuilderMap, BuilderMap, Set.Set String) -> Expr -> Either String Expr
normalizeExpr env@(parametricBuilders, atomicBuilders, benign) expr =
  case expr of
    -- Handle scopes first, adding bound variables before processing sub-expressions
    Lambda ti name body ->
      normalizeExpr (parametricBuilders, atomicBuilders, Set.insert name benign) body
      >>= \body' -> Right $ Lambda ti name body'

    LetIn ti name def body -> do
      -- def is normalized with current scope
      def' <- normalizeExpr env def
      -- body is normalized with name added to scope
      body' <- normalizeExpr (parametricBuilders, atomicBuilders, Set.insert name benign) body
      Right $ LetIn ti name def' body'

    -- For all other expressions, normalize sub-expressions first then check for Apply pattern
    _ -> do
      subExprs <- mapM (normalizeExpr env) (getSubExprs expr)
      let expr' = setSubExprs expr subExprs
      case expr' of
        -- Start of an Apply chain
        Apply ti (Apply _ _ _) _ ->
          -- Need to collect all args in the chain and find base function
          let (base, args) = collectApplyChain expr
          in case base of
            Var _ fname | Just builder <- Map.lookup fname parametricBuilders ->
              builder args  -- builder now takes [Expr]
            _ -> Right expr
        Apply ti (Var _ fname) arg
          | not (Set.member fname benign)
          , Just builder <- Map.lookup fname parametricBuilders -> builder [arg]
        Var ti fname
          | not (Set.member fname benign)
          , Just builder <- Map.lookup fname atomicBuilders -> builder []
        _ -> Right expr'

-- Returns (base expression, arguments in application order)
collectApplyChain :: Expr -> (Expr, [Expr])
collectApplyChain (Apply _ left arg) =
  let (base, args) = collectApplyChain left
  in (base, args ++ [arg])  -- maintain order of application
collectApplyChain e = (e, [])

-- Helper to map over all expressions in a program
mapExprInProgram :: (Expr -> Either String Expr) -> Program -> Either String Program
mapExprInProgram f prog = do
  newFuncs <- mapM (\(name, expr) -> f expr >>= \e -> Right (name, e)) (functions prog)
  Right $ prog { functions = newFuncs }
