module TestCaseParser (
  TestCase(..),
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


data TestCase = ProbTestCase IRValue [IRValue] (IRValue, IRValue)
              | ArgMaxPTextCase [IRValue] IRValue 
              deriving (Show)

type Parser = Parsec Void String
sc = L.space hspace1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

symbol :: String -> Parser String
symbol = L.symbol sc

pIRValue :: Parser IRValue
pIRValue = pValue >>= return . valueToIR

tryRunParser :: Parser a -> FilePath -> String -> a
tryRunParser parser fp s = case runParser parser fp s of
  Left err -> error (errorBundlePretty err)
  Right val -> val

pProbTestCase :: Parser TestCase
pProbTestCase = do
  _ <- symbol "p("
  params <- pIRValue `sepBy` (symbol ",")
  _ <- (symbol ")=(")
  resP <- pIRValue
  _ <- (symbol ",")
  resD <- pIRValue
  return $ ProbTestCase (head params) (tail params) (resP, resD)

pTestCases :: Parser [TestCase]
pTestCases = pProbTestCase `sepBy` newline

parseTestCases :: FilePath -> IO [TestCase]
parseTestCases fp = do
  content <- readFile fp
  return $ tryRunParser pTestCases fp content

parseProgram :: FilePath -> IO Program
parseProgram fp = do
  src <- readFile fp
  let prog =  tryParseProgram fp src
  case prog of
    Left str -> error $ "Error parsing " ++ fp ++ ": " ++ errorBundlePretty str
    Right p -> return p