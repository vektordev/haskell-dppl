module SPLL.Parser (
  testParse
, pProg
, pExpr
, pIdentifier
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
import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import PrettyPrint
import Text.Pretty.Simple (pPrint)

import Control.Monad.Combinators.Expr
import Data.Void
import Control.Monad (void)

--import Text.Megaparsec.Debug (dbg)
dbg x y = y

--TODO: This parser can by necessity not disambiguate Apply f arg from certain special-treatment builtin functions,
-- like InjF

--TODO: This can't parse type annotations.
-- its type signature doesn't have a space to put them (Program () a instead of Program TypeInfo)
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
  return (Uniform makeTypeInfo)

pNormal :: Parser Expr
pNormal = do
  _ <- symbol "Normal"
  return (Normal makeTypeInfo)

pIfThenElse :: Parser Expr
pIfThenElse = do
  _ <- symbol "if"
  a <- pExpr
  _ <- symbol "then"
  b <- pExpr
  _ <- symbol "else"
  c <- pExpr
  return (IfThenElse makeTypeInfo a b c)

pLetIn :: Parser Expr
pLetIn = do
  _ <- symbol "let"
  name <- pIdentifier
  _ <- symbol "="
  definition <- pExpr
  _ <- symbol "in"
  scope <- pExpr
  return (LetIn makeTypeInfo name definition scope)

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
        Nothing -> return (applyN function args)
    otherwise -> return (applyN function args)

pTheta :: Parser Expr
pTheta = dbg "theta" $ do
  thetaName <- pIdentifier
  _ <- symbol "["
  ix <- pInt
  _ <- symbol "]"
  return $ ThetaI makeTypeInfo (Var makeTypeInfo thetaName) ix

-- just to make this parser quite unambiguous, we're going to demand parens around both ops.
pBinaryOp :: Parser Expr
pBinaryOp = dbg "binOp" $ do
  arg1 <- parens pExpr
  op <- pOp
  arg2 <- parens pExpr
  case op of
    ">=" -> return $ GreaterThan makeTypeInfo arg1 arg2
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
applyN function (arg:args) = applyN (Apply makeTypeInfo function arg) args -- $ foldl (\a f -> Apply makeTypeInfo f a) (Var makeTypeInfo function) (map (Var makeTypeInfo) args)

construct1 constructor [arg] = constructor makeTypeInfo arg
construct1 _ _ = error "tried to apply the wrong number of arguments."

construct2 :: (TypeInfo -> Expr -> Expr -> Expr) -> [Expr] -> Expr
construct2 constructor [arg1, arg2] = constructor makeTypeInfo arg2 arg2
construct2 _ _ = error "tried to apply the wrong number of arguments."

pVar :: Parser Expr
pVar = do
  varname <- lexeme pIdentifier
  return $ Var makeTypeInfo varname

binaryFs :: [(String, TypeInfo -> Expr -> Expr -> Expr)]
binaryFs = [
  ("multF", MultF),
  ("multI", MultI),
  ("plusF", PlusF),
  ("plusI", PlusI)
  ]
  
unaryFs :: [(String, TypeInfo -> Expr -> Expr)]
unaryFs = [
  ("negate", NegF)
  ]

pConst :: Parser Expr
pConst = choice [try pFloat, pIntVal]

pFloat :: Parser Expr
pFloat = do
  f <- L.signed sc (lexeme L.float)
  return $ Constant makeTypeInfo (VFloat f)

pIntVal :: Parser Expr
pIntVal = do
  i <- L.signed sc (lexeme L.decimal)
  return $ Constant makeTypeInfo (VInt i)

pInt :: Parser Int
pInt = L.signed sc (lexeme L.decimal)

pBinaryF :: Parser Expr
pBinaryF = do
  op <- choice (map (symbol . fst) binaryFs)
  left <- pExpr
  right <- pExpr
  case (lookup op binaryFs) of
    Nothing -> error "unexpected parse error"
    Just opconstructor -> return (opconstructor makeTypeInfo left right )

parseFromList :: [(String, b)] -> Parser b
parseFromList kvlist = do
  key <- choice (map (symbol . fst) kvlist)
  case (lookup key kvlist) of
    Nothing -> error "unexpected parse error"
    Just value -> return value

rTypes :: [(String, RType)]
rTypes = [("Int", TInt), ("Float", TFloat)]

pType :: Parser RType
pType = parseFromList rTypes

pList :: Parser [Value]
pList = do
  (symbol "[")
  values <- pCSV
  (symbol "]")
  return values

valueParser :: Parser Value
valueParser = do
  x <- L.decimal
  return (VInt x)

pCSV :: Parser [Value]  
pCSV = valueParser `sepBy` (symbol ",")

pDefinition :: Parser (Either FnDecl NeuralDecl)
pDefinition = do
  x <- choice [pNeural, pFunction]
  doesNotContinue
  return x

pNeural :: Parser (Either FnDecl NeuralDecl)
pNeural = dbg "neural" $ do
  _ <- keyword "neural"
  name <- pIdentifier
  _ <- symbol "::"
  ty <- SPLL.Parser.pType
  _ <- symbol "of"
  range <- pList
  return  (Right (name, ty, (EnumList range)))

pFunction :: Parser (Either FnDecl NeuralDecl)
pFunction = dbg "function" $ do
  name <- pIdentifier
  args <- many pIdentifier
  _ <- symbol "="
  e <- pExpr
  let lambdas = foldr (Lambda makeTypeInfo) e args
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
tryParseProgram filename src = runParser pProg filename src

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
  return $ Null makeTypeInfo

pTuple :: Parser Expr
pTuple = parens $ do
  x <- expr
  _ <- symbol ","
  y <- expr
  return $ TCons makeTypeInfo x y


-- | Parse atomic expressions (no recursion)
atom :: Parser Expr
atom = choice [
    pNull,
    try (pTuple),
    try (parens expr),  -- Parenthesized expressions first
    pUniform,     -- Built-in distributions
    pNormal,
    pConst,       -- Constants (numbers)
    Var makeTypeInfo <$> pIdentifier  -- Variables last
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
    return $ Lambda makeTypeInfo param body

-- | Parse function application
-- This handles both normal application and built-in functions like multF
application :: Parser Expr
application = do
    func <- try atom
    args <- many (try atom <|> try (parens expr))
    case func of
        Var _ name -> case lookup name binaryFs of
            Just constructor -> case args of
                [arg1, arg2] -> return $ constructor makeTypeInfo arg1 arg2
                _ -> fail $ "Binary function " ++ name ++ " requires exactly 2 arguments"
            Nothing -> case lookup name unaryFs of
                Just constructor -> case args of
                    [arg] -> return $ constructor makeTypeInfo arg
                    _ -> fail $ "Unary function " ++ name ++ " requires exactly 1 argument"
                Nothing -> return $ foldl (Apply makeTypeInfo) func args
        _ -> return $ foldl (Apply makeTypeInfo) func args


-- | Main expression parser using makeExprParser
expr :: Parser Expr
expr = makeExprParser term operatorTable
  where
    term = choice [
        try application,
        try keywordExpr,
        atom
      ]

-- | Operator table for makeExprParser
operatorTable :: [[Operator Parser Expr]]
operatorTable = [
    [ InfixL (mkOp)
    -- Add other operators here at appropriate precedence levels
    ]
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
    <|> Var makeTypeInfo <$> identifier


-- | Handle function application
appTable :: Parser Expr
appTable = do
  f <- term
  args <- many term
  return $ foldl (Apply makeTypeInfo) f args

opList = [(">", GreaterThan), ("++", PlusI), ("**", MultI), ("+", PlusF), ("*", MultF), (":", Cons)]

mkOp :: Parser (Expr -> Expr -> Expr)
mkOp = do
  op <- pOp
  case lookup op opList of
    Just constructor -> return $ constructor makeTypeInfo
    Nothing -> fail $ "unknown operator: " ++ op
  

-- | Operator table (precedence and associativity)
opTable :: [[Operator Parser Expr]]
opTable =
  [ [ InfixL (mkOp) ]  -- Left-associative operators
  ]

-- | Top-level parser
expressionParser :: Parser Expr
expressionParser = sc *> expr <* eof

-- | Test the parser
testParser :: String -> Either (ParseErrorBundle String Void) Expr
testParser input = parse expressionParser "" input

