{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module TestCaseParser (
  TestCase(..),
  Backend(..),
  allBackends,
  isProbTestCase,
  isCumulTestCase,
  isArgmaxPTestCase,
  isEncodingLengthTestCase,
  isEncodingSlotTestCase,
  testCaseName,
  parseTestCases,
  parseTestCasesFromString,
  FreezeCase(..),
  FreezeMode(..),
  parseFreezeCasesFromString,
  parseProgram
) where

import Data.List (isPrefixOf)

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


-- Which execution backends a .tst file's cases run against. Declared via an
-- optional first line `backends: interpreter, julia` (any non-empty subset);
-- a file without the header runs against all three.
data Backend = Interpreter | Julia | Python
  deriving (Eq, Show, Enum, Bounded)

allBackends :: [Backend]
allBackends = [minBound .. maxBound]

data TestCase = ProbTestCase String IRValue [IRValue] (IRValue, IRValue)
              | CumulTestCase String IRValue [IRValue] (IRValue, IRValue)
              | ArgmaxPTestCase String [IRValue] IRValue
              | EncodingLengthTestCase String String [IRValue] Int             -- target fn, explicit args, expected output list length
              | EncodingSlotTestCase String String [IRValue] IRValue Double  -- target fn, explicit args, indexOf-value, expected float
              deriving (Show)

isProbTestCase :: TestCase -> Bool
isProbTestCase (ProbTestCase _ _ _ _) = True
isProbTestCase _ = False

isArgmaxPTestCase :: TestCase -> Bool
isArgmaxPTestCase (ArgmaxPTestCase _ _ _) = True
isArgmaxPTestCase _ = False

isCumulTestCase :: TestCase -> Bool
isCumulTestCase (CumulTestCase _ _ _ _) = True
isCumulTestCase _ = False

isEncodingLengthTestCase :: TestCase -> Bool
isEncodingLengthTestCase (EncodingLengthTestCase {}) = True
isEncodingLengthTestCase _ = False

isEncodingSlotTestCase :: TestCase -> Bool
isEncodingSlotTestCase (EncodingSlotTestCase {}) = True
isEncodingSlotTestCase _ = False

testCaseName :: TestCase -> String
testCaseName (ProbTestCase name _ _ _) = name
testCaseName (CumulTestCase name _ _ _) = name
testCaseName (ArgmaxPTestCase name _ _) = name
testCaseName (EncodingLengthTestCase name _ _ _) = name
testCaseName (EncodingSlotTestCase name _ _ _ _) = name

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
  symbol "p("
  params <- pIRValue `sepBy` symbol ","
  symbol ")="
  VTuple resP resD <- pIRValue
  case params of 
    [] -> fail "ProbTestCase must have at least one parameter (the sample)"
    _  -> return $ ProbTestCase name (head params) (tail params) (resP, resD)

pArgmaxPTestCase :: MonadParser m => String -> m TestCase
pArgmaxPTestCase name = do
  symbol "argmax_p("
  params <- pIRValue `sepBy` symbol ","
  symbol ")="
  res <- pIRValue
  return $ ArgmaxPTestCase name params res

pCumulParser :: MonadParser m => String -> m TestCase
pCumulParser name = do
  symbol "cdf("
  params <- pIRValue `sepBy` symbol ","
  symbol ")="
  VTuple resP resD <- pIRValue
  case params of 
    [] -> fail "ProbTestCase must have at least one parameter (the sample)"
    _  -> return $ CumulTestCase name (head params) (tail params) (resP, resD)

-- Optional endpoint addressing: `[fn]` selects which top-level function's encode to query.
-- Defaults to "main" (the f == main case of the one per-function-encode rule).
pEncodeTarget :: MonadParser m => m String
pEncodeTarget = option "main" (between (symbol "[") (symbol "]") pTargetName)
  where pTargetName = L.lexeme sc (some (alphaNumChar <|> char '_'))

-- Optional explicit argument list passed verbatim to the endpoint's encode (e.g. `(0.3)`
-- for `isRed s` with s = 0.3). Empty when omitted; the harness then falls back to mock-NN
-- argument fabrication for decoder programs.
pEncodeArgs :: MonadParser m => m [IRValue]
pEncodeArgs = option [] (between (symbol "(") (symbol ")") (pIRValue `sepBy` symbol ","))

pEncodingLengthTestCase :: MonadParser m => String -> m TestCase
pEncodingLengthTestCase name = do
  symbol "encode_len"
  target <- pEncodeTarget
  args <- pEncodeArgs
  symbol "="
  n <- L.decimal
  return $ EncodingLengthTestCase name target args n

-- encode_at[fn](arg1, ..., indexOf(v)) ~= e
-- The values before the trailing `indexOf(...)` are the endpoint's explicit arguments
-- (possibly none); `indexOf(v)` selects the logit slot for value v within the endpoint's plan.
pEncodingSlotTestCase :: MonadParser m => String -> m TestCase
pEncodingSlotTestCase name = do
  symbol "encode_at"
  target <- pEncodeTarget
  symbol "("
  args <- many (try (pIRValue <* symbol ","))
  symbol "indexOf("
  idxOf <- pIRValue
  symbol ")"
  symbol ")"
  symbol "~="
  expected <- L.float
  return $ EncodingSlotTestCase name target args idxOf expected

pTestCases :: MonadParser m => String -> m [TestCase]
pTestCases name = choice [pProbTestCase name, pCumulParser name, pArgmaxPTestCase name, pEncodingLengthTestCase name, pEncodingSlotTestCase name] `sepEndBy` pNewline

pBackend :: MonadParser m => m Backend
pBackend = choice
  [ symbol "interpreter" >> return Interpreter
  , symbol "julia" >> return Julia
  , symbol "python" >> return Python
  ]

pBackendsHeader :: MonadParser m => m [Backend]
pBackendsHeader = do
  symbol "backends:"
  bs <- pBackend `sepBy1` symbol ","
  pNewline
  return bs

-- An optional standalone `slow` header line, order-independent with the
-- backends header. Marks the file's cases as expensive enough to belong in
-- the opt-in Slow test group (see End2EndTesting.slowEnd2EndTests) rather
-- than the default `stack test` run.
pSlowHeader :: MonadParser m => m ()
pSlowHeader = do
  symbol "slow"
  pNewline
  return ()

-- Both headers are optional and may appear in either order (or not at all).
pHeaders :: MonadParser m => m ([Backend], Bool)
pHeaders = go allBackends False
  where
    go bs slow =
      (try pBackendsHeader >>= \bs' -> go bs' slow) <|>
      (try pSlowHeader >> go bs True) <|>
      return (bs, slow)

pTestFile :: MonadParser m => String -> m ([Backend], Bool, [TestCase])
pTestFile name = do
  (bs, slow) <- pHeaders
  tcs <- pTestCases name
  return (bs, slow, tcs)

parseTestCasesFromString :: FilePath -> String -> Either String ([Backend], Bool, [TestCase])
parseTestCasesFromString fp content =
  case runParser (runStateT (pTestFile fp) 0) fp content of
    Left err -> Left (errorBundlePretty err)
    Right (val, _) -> Right val

parseTestCases :: FilePath -> IO ([Backend], Bool, [TestCase])
parseTestCases fp = do
  content <- readFile fp
  either error return (parseTestCasesFromString fp content)

-- ---------------------------------------------------------------------------
-- Showcase behavioural-freeze lines (examples/showcase.freeze)
-- ---------------------------------------------------------------------------
-- Each line pins the inference result of ONE named top-level definition, driven
-- directly by name rather than through `main`. See test/TestShowcase.hs.

data FreezeMode = FreezeProb | FreezeCdf
  deriving (Eq, Show)

-- FreezeCase <def> <args> <mode> <sample> <expected probability>
data FreezeCase = FreezeCase String [IRValue] FreezeMode IRValue Double
  deriving (Show)

-- An identifier followed by an OPTIONAL parenthesised argument list. The args
-- must be distinguished from the mode's own `(` -- they only bind when the `(`
-- immediately follows the name (no separating space, unlike `... p(`).
pFreezeArgs :: MonadParser m => m [IRValue]
pFreezeArgs = option [] (between (char '(') (symbol ")") (pIRValue `sepBy` symbol ","))

pFreezeCase :: MonadParser m => m FreezeCase
pFreezeCase = do
  sc
  name <- some (alphaNumChar <|> char '_')
  args <- pFreezeArgs
  sc
  mode <- choice [symbol "p(" >> return FreezeProb, symbol "cdf(" >> return FreezeCdf]
  sample <- pIRValue
  symbol ")"
  symbol "="
  expected <- L.signed sc (L.lexeme sc L.float)
  return $ FreezeCase name args mode sample expected

-- | Parse a whole showcase.freeze file. Blank lines and `--` comment lines are
-- dropped, then each remaining line is parsed independently so that a single
-- malformed line names itself in the error rather than derailing the file.
parseFreezeCasesFromString :: FilePath -> String -> Either String [FreezeCase]
parseFreezeCasesFromString fp = traverse parseLine . relevantLines
  where
    relevantLines = filter (not . irrelevant) . map (dropWhile (== ' ')) . lines
    irrelevant l = null l || "--" `isPrefixOf` l
    parseLine l = case runParser (runStateT (pFreezeCase <* eof) 0) fp l of
      Left err  -> Left (errorBundlePretty err)
      Right (v, _) -> Right v

parseProgram :: FilePath -> IO Program
parseProgram fp = do
  src <- readFile fp
  let prog =  tryParseProgram fp src
  case prog of
    Left str -> error $ "Error parsing " ++ fp ++ ": " ++ errorBundlePretty str
    Right p -> return p