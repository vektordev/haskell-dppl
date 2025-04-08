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


data TestCase = ProbTestCase IRValue [IRValue] (IRValue, IRValue)
              | ArgmaxPTestCase [IRValue] IRValue 
              deriving (Show)

isProbTestCase :: TestCase -> Bool
isProbTestCase (ProbTestCase _ _ _) = True
isProbTestCase _ = False

isArgmaxPTestCase :: TestCase -> Bool
isArgmaxPTestCase (ArgmaxPTestCase _ _) = True
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

pProbTestCase :: Parser TestCase
pProbTestCase = do
  _ <- symbol "p("
  params <- pIRValue `sepBy` (symbol ",")
  _ <- (symbol ")=")
  VTuple resP resD <- pIRValue
  return $ ProbTestCase (head params) (tail params) (resP, resD)

pArgmaxPTestCase :: Parser TestCase
pArgmaxPTestCase = do
  symbol "argmax_p("
  params <- pIRValue `sepBy` (symbol ",")
  symbol ")="
  res <- pIRValue
  return $ ArgmaxPTestCase params res

pTestCases :: Parser [TestCase]
pTestCases = choice[pProbTestCase, pArgmaxPTestCase] `sepBy` pNewline

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