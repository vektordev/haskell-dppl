module SPLL.Parser (
  testParse
, pProg
, tryParseProgram
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


--import Text.Megaparsec.Debug (dbg)
dbg :: symbol -> result -> result
dbg a b = b

--TODO: This can't parse type annotations.
-- its type signature doesn't have a space to put them (Program () a instead of Program TypeInfo a)
-- At some point this deserves fixing.

type Parser = Parsec Void String


sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

--TODO:
keyword :: String -> Parser String
keyword = symbol

--Note: Won't parse capitalized constructors, if ever we add those.
pIdentifier :: Parser String
pIdentifier = lexeme $ do
  x <- lowerChar
  xs <- many alphaNumChar
  return (x:xs)

pUniform :: Parser (Expr a)
pUniform = do
  _ <- symbol "uniform"
  return (Uniform makeTypeInfo)

pIfThenElse :: RealFloat a => Parser (Expr a)
pIfThenElse = do
  _ <- symbol "if"
  a <- pExpr
  _ <- symbol "then"
  b <- pExpr
  _ <- symbol "else"
  c <- pExpr
  return (IfThenElse makeTypeInfo a b c)

pLetIn :: RealFloat a => Parser (Expr a)
pLetIn = do
  _ <- symbol "let"
  name <- lexeme pIdentifier
  _ <- symbol "="
  definition <- pExpr
  _ <- symbol "in"
  scope <- pExpr
  return (LetIn makeTypeInfo name definition scope)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

pExpr :: RealFloat a => Parser (Expr a)
pExpr = choice [
  parens pExpr,
  pIfThenElse,
  pUniform,
  pLetIn,
  pBinaryF,
  pApply,
  pConst,
  pVar
  ]

-- TODO: I think this parser should accept any pExpr instead of identifiers. Might get ambiguous parses though.
pApply :: Parser (Expr a)
pApply = do
  function <- pIdentifier
  args <- some pIdentifier
  case lookup function binaryFs of
    Nothing -> return (applyN (Var makeTypeInfo function) (map (Var makeTypeInfo) args))
    Just constructor -> return (construct2 constructor (map (Var makeTypeInfo) args))

applyN :: Expr a -> [Expr a] -> Expr a
applyN function [] = function
applyN function (arg:args) = applyN (Apply makeTypeInfo function arg) args -- $ foldl (\a f -> Apply makeTypeInfo f a) (Var makeTypeInfo function) (map (Var makeTypeInfo) args)

construct2 :: (TypeInfo a -> Expr a -> Expr a -> Expr a) -> [Expr a] -> Expr a
construct2 constructor [arg1, arg2] = constructor makeTypeInfo arg2 arg2
construct2 _ _ = error "tried to apply the wrong number of arguments."

pVar :: Parser (Expr a)
pVar = do
  varname <- lexeme pIdentifier
  return $ Var makeTypeInfo varname

binaryFs = [
  ("multF", MultF),
  ("multI", MultI),
  ("plusF", PlusF),
  ("plusI", PlusI)
  ]

pConst :: RealFloat a => Parser (Expr a)
pConst = choice [pFloat, pInt]

pFloat :: RealFloat a => Parser (Expr a)
pFloat = do
  f <- lexeme L.float
  return $ Constant makeTypeInfo (VFloat f)

pInt :: Parser (Expr a)
pInt = do
  i <- lexeme L.decimal
  return $ Constant makeTypeInfo (VInt i)

pBinaryF :: RealFloat a => Parser (Expr a)
pBinaryF = do
  op <- choice (map (symbol . fst) binaryFs)
  left <- pExpr
  right <- pExpr
  case (lookup op binaryFs) of
    Nothing -> error "unexpected parse error"
    Just opconstructor -> return (opconstructor makeTypeInfo left right )

parseFromList kvlist = do
  key <- choice (map (symbol . fst) kvlist)
  case (lookup key kvlist) of
    Nothing -> error "unexpected parse error"
    Just value -> return value

rTypes :: [(String, RType)]
rTypes = [("Int", TInt), ("Float", TFloat)]

pType :: Parser RType
pType = parseFromList rTypes

pList :: Parser [Value a]
pList = do
  (symbol "[")
  values <- pCSV
  (symbol "]")
  return values

valueParser :: Parser (Value a)
valueParser = do
  x <- L.decimal
  return (VInt x)

pCSV :: Parser [Value a]  
pCSV = valueParser `sepBy` (symbol ",")

pDefinition :: (Show a, RealFloat a) => Parser (Either (FnDecl a) (NeuralDecl a))
pDefinition = choice [try pFunction, pNeural]

pNeural :: Parser (Either (FnDecl a) (NeuralDecl a))
pNeural = do
  _ <- keyword "neural"
  name <- pIdentifier
  _ <- symbol "::"
  ty <- SPLL.Parser.pType
  _ <- symbol "of"
  range <- pList
  return  (Right (name, ty, (EnumList range)))

pFunction :: (Show a, RealFloat a) => Parser (Either (FnDecl a) (NeuralDecl a))
pFunction = dbg "function" $ do
  name <- pIdentifier
  args <- many pIdentifier
  _ <- symbol "="
  e <- pExpr
  let lambdas = foldr (Lambda makeTypeInfo) e args
  return (Left (name, lambdas))

pProg :: (Show a, RealFloat a) => Parser (Program a)
pProg = do
  defs <- dbg "trying definition" (many pDefinition)
  _ <- eof
  return (aggregateDefinitions defs)

aggregateDefinitions :: [Either (FnDecl a) (NeuralDecl a)] -> Program a
aggregateDefinitions (Left fn : tail) = Program (fn:fns) neurals
  where
    Program fns neurals = aggregateDefinitions tail
aggregateDefinitions (Right nr : tail) = Program fns (nr:neurals)
  where
    Program fns neurals = aggregateDefinitions tail
aggregateDefinitions [] = Program [] []

tryParseProgram :: (Show a, RealFloat a) => FilePath -> String -> Either (ParseErrorBundle String Void) (Program a)
tryParseProgram filename src = runParser pProg filename src

testParse :: IO ()
testParse = do
  let filename = "../../test.spll"
  source <- readFile filename
  let result = runParser (pProg :: Parser (Program Float)) filename source
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
{--
langDef :: Tok.LanguageDef ()
langDef = Tok.LanguageDef
  { Tok.commentStart    = "{-"
  , Tok.commentEnd      = "-}"
  , Tok.commentLine     = "--"
  , Tok.nestedComments  = True
  , Tok.identStart      = letter
  , Tok.identLetter     = alphaNum <|> oneOf "_'"
  , Tok.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Tok.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Tok.reservedNames   = []
  , Tok.reservedOpNames = []
  , Tok.caseSensitive   = True
  }

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser langDef

parens :: Parser a -> Parser a
parens = Tok.parens lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

semiSep :: Parser a -> Parser [a]
semiSep = Tok.semiSep lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer


-- if/then/else
ifthen :: Parser (Expr () a)
ifthen = do
  reserved "if"
  cond <- expr
  reservedOp "then"
  tr <- expr
  reserved "else"
  fl <- expr
  return (IfThenElse cond tr fl)

expr :: Parser (Expr () a)
expr = Ex.buildExpressionParser table factor

factor :: Parser (Expr () a)
factor =
      ifthen
  <|> parens expr


--program :: Parsec s () a
--program

parseSPLL :: String -> Program (TypeInfo a) a
parseSPLL = parse program "filename"
-}