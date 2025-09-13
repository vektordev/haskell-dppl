{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module TestCaseParser (
  TestCase(..),
  isProbTestCase,
  isArgmaxPTestCase,
  testCaseName,
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
import Control.Monad.State
import Control.Monad (MonadPlus)
import Text.Megaparsec hiding (State)
import Data.Void


data TestCase = ProbTestCase String IRValue [IRValue] (IRValue, IRValue)
              | ArgmaxPTestCase String [IRValue] IRValue 
              deriving (Show)

isProbTestCase :: TestCase -> Bool
isProbTestCase (ProbTestCase _ _ _ _) = True
isProbTestCase _ = False

isArgmaxPTestCase :: TestCase -> Bool
isArgmaxPTestCase (ArgmaxPTestCase _ _ _) = True
isArgmaxPTestCase _ = False

testCaseName :: TestCase -> String
testCaseName (ProbTestCase name _ _ _) = name
testCaseName (ArgmaxPTestCase name _ _) = name

type Parser = Parsec Void String
type MonadParser m = (MonadParsec Void String m, MonadPlus m, MonadFail m, MonadState Int m)

sc :: MonadParser m => m ()
sc = L.space hspace1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

symbol :: MonadParser m => String -> m String
symbol = L.symbol sc

-- Either a windows or a linux newline
pNewline :: MonadParser m => m String
pNewline = choice [symbol "\n", symbol "\r\n"] 

pIRValue :: MonadParser m => m IRValue
pIRValue = pValue >>= return . valueToIR

pProbTestCase :: MonadParser m => String -> m TestCase
pProbTestCase name = do
  _ <- symbol "p("
  params <- pIRValue `sepBy` (symbol ",")
  _ <- (symbol ")=")
  VTuple resP resD <- pIRValue
  return $ ProbTestCase name (head params) (tail params) (resP, resD)

pArgmaxPTestCase :: MonadParser m => String -> m TestCase
pArgmaxPTestCase name = do
  symbol "argmax_p("
  params <- pIRValue `sepBy` (symbol ",")
  symbol ")="
  res <- pIRValue
  return $ ArgmaxPTestCase name  params res

pTestCases :: MonadParser m => String -> m [TestCase]
pTestCases name = choice[pProbTestCase name , pArgmaxPTestCase name] `sepBy` pNewline

parseTestCases :: FilePath -> IO [TestCase]
parseTestCases fp = do
  content <- readFile fp
  case runParser (runStateT (pTestCases fp) 0) fp content of
    Left err -> error (errorBundlePretty err)
    Right (val, _) -> return $ val

parseProgram :: FilePath -> IO Program
parseProgram fp = do
  src <- readFile fp
  let prog =  tryParseProgram fp src
  case prog of
    Left str -> error $ "Error parsing " ++ fp ++ ": " ++ errorBundlePretty str
    Right p -> return p