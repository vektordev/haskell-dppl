module TestCaseParser (
  TestCase(..),
  isProbTestCase,
  isArgmaxPTestCase,
  parseTestCases,
  parseProgram
) where

import SPLL.Parser (tryParseProgram, pValue)
import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import SPLL.Lang.Lang

import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Data.Void
import Debug.Trace


data TestCase = ProbTestCase String IRValue [IRValue] (IRValue, IRValue)
              | ArgmaxPTestCase String [IRValue] IRValue 
              deriving (Show)

isProbTestCase :: TestCase -> Bool
isProbTestCase (ProbTestCase _ _ _ _) = True
isProbTestCase _ = False

isArgmaxPTestCase :: TestCase -> Bool
isArgmaxPTestCase (ArgmaxPTestCase _ _ _) = True
isArgmaxPTestCase _ = False

type Parser = Parsec Void String
sc = L.space hspace1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

symbol :: String -> Parser String
symbol = L.symbol sc

-- Either a windows or a linux newline
pNewline :: Parser String
pNewline = choice [symbol "\n", symbol "\r\n"] 

pIRValue :: Parser IRValue
pIRValue = pValue >>= return . valueToIR

tryRunParser :: Parser a -> FilePath -> String -> a
tryRunParser parser fp s = case runParser parser fp s of
  Left err -> error (errorBundlePretty err)
  Right val -> val

pProbTestCase :: String -> Parser TestCase
pProbTestCase name = do
  _ <- symbol "p("
  params <- pIRValue `sepBy` (symbol ",")
  _ <- (symbol ")=")
  VTuple resP resD <- pIRValue
  return $ ProbTestCase name (head params) (tail params) (resP, resD)

pArgmaxPTestCase :: String -> Parser TestCase
pArgmaxPTestCase name = do
  symbol "argmax_p("
  params <- pIRValue `sepBy` (symbol ",")
  symbol ")="
  res <- pIRValue
  return $ ArgmaxPTestCase name  params res

pTestCases :: String -> Parser [TestCase]
pTestCases name = choice[pProbTestCase name , pArgmaxPTestCase name] `sepBy` pNewline

parseTestCases :: FilePath -> IO [TestCase]
parseTestCases fp = do
  content <- readFile fp
  return $ tryRunParser (pTestCases fp) fp content

parseProgram :: FilePath -> IO Program
parseProgram fp = do
  src <- readFile fp
  let prog =  tryParseProgram fp src
  case prog of
    Left str -> error $ "Error parsing " ++ fp ++ ": " ++ errorBundlePretty str
    Right p -> return p