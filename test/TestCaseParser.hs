{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module TestCaseParser (
  TestCase(..),
  Expectation(..),
  expectationProb,
  expectationDim,
  expectationImposs,
  Backend(..),
  allBackends,
  defaultBackends,
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

import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Data.Void
import Control.Monad.State
import Control.Monad (MonadPlus, void)


-- Which execution backends a .tst file's cases run against. Declared via an
-- optional first line `backends: interpreter, julia` (any non-empty subset);
-- a file without the header runs against the three scalar backends
-- ('defaultBackends').
--
-- `batched` is deliberately NOT part of that default: it is an opt-in
-- declaration that the program is expected to be batched-mode eligible (see
-- End2EndTesting.batchedPythonTests), asserted rather than filtered, so
-- silently losing eligibility fails the suite. Listing it does not remove the
-- file from any scalar backend -- spell those out alongside it.
-- `dense` is the same kind of declaration one level in: that the program's
-- *query domain* is finite, so batched mode emits dense-enumeration entry points
-- for it (design heterogeneous-batch-inference, M3). It presupposes `batched`
-- and does not imply it -- list both.
data Backend = Interpreter | Julia | Python | Batched | Dense
  deriving (Eq, Show, Enum, Bounded)

-- Every Backend constructor. Note this now includes 'Batched' and 'Dense', so it
-- is NOT the right default for a header-less file -- use 'defaultBackends'.
allBackends :: [Backend]
allBackends = [minBound .. maxBound]

-- What a .tst file without a `backends:` header routes to: the three scalar
-- backends, but not batched mode.
defaultBackends :: [Backend]
defaultBackends = [Interpreter, Julia, Python]

-- | The expected result of a prob/cumulative query. Two shapes, spelled
-- distinctly in a .tst file rather than folded into one tuple (see
-- CLAUDE.md's ".tst dim expectations" note, task
-- tst-dim-unasserted-at-zero-probability):
--
-- * @Possible prob dim mImp@ -- an ordinary point: @(prob, dim)@ or
--   @(prob, dim, imposs)@ in the .tst source. Both @prob@ and @dim@ are
--   always checked (unconditionally -- there is no "probability happened to
--   compute to zero so skip the dim check" special case any more); @mImp@ is
--   @Just b@ when the .tst line spelled a third component, @Nothing@ when it
--   did not (impossibility flag not checked).
--
-- * @Impossible@ -- the dedicated shape for a genuinely impossible query
--   point (wrong Either arm, off-support sample, unmatched indicator, ...),
--   spelled @is impossible@ in the .tst source instead of a numeric tuple.
--   At such a point the dim has no fact of the matter (a hard zero is
--   neither a density nor a mass), so none is stated or checked; the
--   probability is asserted zero and the impossibility flag is asserted
--   @True@, both unconditionally. This is the *only* way to spell a
--   zero-probability, impossible point -- 'pTupleExpectation' refuses a
--   @(0.0, dim, True)@ tuple, so a .tst author can never write a dim number
--   that silently goes unchecked.
data Expectation = Possible IRValue IRValue (Maybe Bool)
                  | Impossible
  deriving (Show, Eq)

-- | The expected probability, always meaningful regardless of shape.
expectationProb :: Expectation -> Double
expectationProb (Possible (VFloat p) _ _) = p
expectationProb (Possible other _ _) = error ("expected probability must be a float, got: " ++ show other)
expectationProb Impossible = 0.0

-- | The expected dim, when the shape states one. 'Impossible' states none --
-- callers that need a dim to compare against should skip such rows, not
-- invent a placeholder.
expectationDim :: Expectation -> Maybe Double
expectationDim (Possible _ (VFloat d) _) = Just d
expectationDim (Possible _ other _) = error ("expected dim must be a float, got: " ++ show other)
expectationDim Impossible = Nothing

-- | The expected impossibility flag. 'Impossible' always declares 'True';
-- 'Possible' declares whatever its optional third component said, or
-- 'Nothing' (not checked) if it stated none.
expectationImposs :: Expectation -> Maybe Bool
expectationImposs (Possible _ _ mImp) = mImp
expectationImposs Impossible = Just True

data TestCase = ProbTestCase String IRValue [IRValue] Expectation
              | CumulTestCase String IRValue [IRValue] Expectation
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

type MonadParser m = (MonadParsec Void String m, MonadPlus m, MonadFail m, MonadState Int m)

sc :: MonadParser m => m ()
sc = L.space hspace1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

-- L.symbol yields the matched text, which no caller in this module wants:
-- every use is a delimiter in `>>`, `between`, `sepBy` or `<*`. Returning ()
-- keeps a bare `symbol "..."` in a do block from discarding a result.
symbol :: MonadParser m => String -> m ()
symbol = void . L.symbol sc

-- Either a windows or a linux newline
pNewline :: MonadParser m => m ()
pNewline = choice [symbol "\n", symbol "\r\n"]

-- Full-file whitespace: blank lines and whole-line `--`/`{- -}` comments.
-- Only consumed at the very start of the file (before any headers) and at the
-- very end (after the last test case, before 'eof') -- comments interleaved
-- between test-case lines are not supported.
scn :: MonadParser m => m ()
scn = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

pIRValue :: MonadParser m => m IRValue
pIRValue = pValue >>= return . valueToIR

-- | The expected result of a prob/cumulative line. Two shapes -- see
-- 'Expectation':
--
-- * @is impossible@ -- 'Impossible'.
-- * @(prob, dim)@ or @(prob, dim, imposs)@ -- 'Possible', via
--   'pTupleExpectation'.
--
-- Spelled out here rather than delegating to 'pValue' because SPLL's own tuple
-- syntax is strictly binary: a three-component expectation is a .tst-level
-- expectation triple, not an SPLL value.
pExpectation :: MonadParser m => m Expectation
pExpectation = choice
  [ Impossible <$ symbol "is impossible"
  , pTupleExpectation
  ]

-- | The @(prob, dim)@ / @(prob, dim, imposs)@ tuple shape. The third
-- component is spelled with the same @True@/@False@ literals 'pValue' uses
-- for booleans everywhere else; omitting it (the shape most pre-existing
-- corpus lines have) means "do not check the flag".
--
-- A row whose probability is @0@ and whose impossibility flag would be
-- @True@ is refused here: that combination is a genuinely impossible point
-- with nothing to say about @dim@, and must be spelled @is impossible@
-- instead, so there is exactly one way to state it and it can never carry an
-- unchecked, misleading dim number (task
-- tst-dim-unasserted-at-zero-probability).
pTupleExpectation :: MonadParser m => m Expectation
pTupleExpectation = do
  symbol "="
  symbol "("
  resP <- pIRValue
  symbol ","
  resD <- pIRValue
  mImp <- optional (symbol "," >> pIRValue)
  symbol ")"
  mImp' <- case mImp of
    Nothing        -> return Nothing
    Just (VBool b) -> return (Just b)
    Just other     -> fail ("the third component of an expected result is the impossibility flag "
                            ++ "and must be True or False, got: " ++ show other)
  case (resP, mImp') of
    (VFloat 0.0, Just True) -> fail
      ("a row whose probability is 0 and impossibility flag is True is a genuinely "
       ++ "impossible point and must be spelled `is impossible`, not a (prob, dim, True) "
       ++ "tuple -- the tuple's dim would go unchecked and misleading")
    _ -> return (Possible resP resD mImp')

pProbTestCase :: MonadParser m => String -> m TestCase
pProbTestCase name = do
  symbol "p("
  params <- pIRValue `sepBy` symbol ","
  symbol ")"
  expct <- pExpectation
  case params of
    [] -> fail "ProbTestCase must have at least one parameter (the sample)"
    _  -> return $ ProbTestCase name (head params) (tail params) expct

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
  symbol ")"
  expct <- pExpectation
  case params of
    [] -> fail "ProbTestCase must have at least one parameter (the sample)"
    _  -> return $ CumulTestCase name (head params) (tail params) expct

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
  , symbol "batched" >> return Batched
  , symbol "dense" >> return Dense
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
-- A missing `backends:` header means 'defaultBackends' (the three scalar
-- backends), never 'allBackends': `batched` must be opted into explicitly.
pHeaders :: MonadParser m => m ([Backend], Bool)
pHeaders = go defaultBackends False
  where
    go bs slow =
      (try pBackendsHeader >>= \bs' -> go bs' slow) <|>
      (try pSlowHeader >> go bs True) <|>
      return (bs, slow)

pTestFile :: MonadParser m => String -> m ([Backend], Bool, [TestCase])
pTestFile name = do
  scn
  (bs, slow) <- pHeaders
  tcs <- pTestCases name
  scn
  eof
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