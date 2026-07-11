-- | Drift guard for the documentation examples.
--
-- The syntax showcase (@examples/showcase.ppl@) and the fenced @```spll@
-- code blocks in @README.md@ are checked here so that documented syntax
-- cannot silently rot out of sync with the parser/compiler.
--
-- What is checked:
--   * the whole showcase file PARSES (catches any snippet's syntax rot);
--   * showcase `main` runs in all three inference modes: it forward-samples
--     (generate) and its probability/cumulative values match
--     examples/showcase.tst;
--   * every @```spll@ block in the README parses and compiles.
--
-- Note: only `main`'s path is forced, not every helper definition. The helpers
-- are parse-only syntax demonstrations (see the file header) and some are
-- intentionally generate-only, so whole-program compilation is not required.
module TestShowcase (showcaseTests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure, assertBool, (@?=))

import Control.Exception (try, evaluate, SomeException)
import Control.Monad (forM_)
import Control.Monad.Random (evalRand)
import System.Random (mkStdGen)
import Data.List (stripPrefix)
import Data.Void (Void)
import Text.Megaparsec (ParseErrorBundle, errorBundlePretty)

import SPLL.Lang.Types
import SPLL.Parser (tryParseProgram)
import SPLL.Prelude (compile, runGenC, runProbC, runIntegC)
import SPLL.IntermediateRepresentation (defaultCompilerConfig, IREnv, IRValue)
import TestCaseParser (TestCase(..), parseTestCasesFromString)
import TestTolerances (probTolerance)

showcasePath :: FilePath
showcasePath = "examples/showcase.ppl"

showcaseTstPath :: FilePath
showcaseTstPath = "examples/showcase.tst"

readmePath :: FilePath
readmePath = "README.md"

-- | The README currently documents this many @```spll@ examples. The count is
-- asserted so that dropping the language tag (which would silently exclude a
-- block from the drift check) fails the suite instead of passing quietly.
expectedReadmeBlocks :: Int
expectedReadmeBlocks = 5

showcaseTests :: IO TestTree
showcaseTests = do
  scSrc     <- readFile showcasePath
  tstSrc    <- readFile showcaseTstPath
  readmeSrc <- readFile readmePath
  let scProg  = tryParseProgram showcasePath scSrc
      tstCases = either (const []) snd (parseTestCasesFromString showcaseTstPath tstSrc)
      readmeBlocks = spllBlocks readmeSrc
  return $ testGroup "Showcase"
    [ testCase (showcasePath ++ " parses") $
        assertParses showcasePath scSrc
    , testCase (showcasePath ++ " main generates") $
        either (assertFailure . prettyParse) assertGenerates scProg
    , testCase (showcasePath ++ " main matches showcase.tst (probability + cumulative)") $
        either (assertFailure . prettyParse) (assertTstMatches tstCases) scProg
    , testGroup "README ```spll examples" $
        [ testCase ("README ```spll block " ++ show i ++ " parses & compiles") $ do
            assertParses (readmePath ++ " block " ++ show i) block
            either (assertFailure . prettyParse) assertCompiles (tryParseProgram readmePath block)
        | (i, block) <- zip [1 :: Int ..] readmeBlocks
        ] ++
        [ testCase "README has the expected number of ```spll blocks" $
            length readmeBlocks @?= expectedReadmeBlocks
        ]
    ]

prettyParse :: ParseErrorBundle String Void -> String
prettyParse = errorBundlePretty

assertParses :: String -> String -> IO ()
assertParses label src =
  case tryParseProgram label src of
    Left err -> assertFailure ("Parse failed for " ++ label ++ ":\n" ++ errorBundlePretty err)
    Right _  -> return ()

-- | Forces a forward sample from @main@, proving the generate mode compiles and
-- runs. Only @main@'s path is forced (not the parse-only demo helpers, some of
-- which are intentionally generate-only syntax examples).
assertGenerates :: Program -> IO ()
assertGenerates p = case compile defaultCompilerConfig p of
  Left err -> assertFailure ("Compilation failed:\n" ++ show err)
  Right env -> do
    let sample = evalRand (runGenC p env []) (mkStdGen 0) :: IRValue
    forced <- try (evaluate (length (show sample))) :: IO (Either SomeException Int)
    case forced of
      Left e  -> assertFailure ("generate raised an exception:\n" ++ show e)
      Right _ -> return ()

-- | Fully forces the compiler so that lazily-thrown IR errors (e.g. an
-- unsupported construct) surface as a test failure rather than a thunk.
-- Used for README snippets, which are self-contained compilable programs.
assertCompiles :: Program -> IO ()
assertCompiles p = do
  forced <- try (evaluate (length (show (compile defaultCompilerConfig p))))
              :: IO (Either SomeException Int)
  case forced of
    Left e  -> assertFailure ("Compilation raised an exception:\n" ++ show e)
    Right _ -> case compile defaultCompilerConfig p of
      Left err -> assertFailure ("Compilation failed:\n" ++ show err)
      Right _  -> return ()

assertTstMatches :: [TestCase] -> Program -> IO ()
assertTstMatches cases p = case compile defaultCompilerConfig p of
  Left err -> assertFailure ("Compilation failed:\n" ++ show err)
  Right env -> forM_ cases (checkCase p env)

checkCase :: Program -> IREnv -> TestCase -> IO ()
checkCase p env (ProbTestCase name sample params (VFloat expProb, _)) =
  checkQuery "probability" name (runProbC p env params sample) expProb
checkCase p env (CumulTestCase name sample params (VFloat expProb, _)) =
  checkQuery "cumulative" name (runIntegC p env params sample) expProb
checkCase _ _ _ = return ()  -- showcase.tst only carries prob/cdf cases

checkQuery :: String -> String -> Either e IRValue -> Double -> IO ()
checkQuery mode name result expProb = do
  forced <- try (evaluate (either (const Nothing) extractProb result))
              :: IO (Either SomeException (Maybe Double))
  case forced of
    Left e -> assertFailure (mode ++ " case " ++ name ++ " raised: " ++ show e)
    Right Nothing -> assertFailure (mode ++ " case " ++ name ++ " did not return a probability tuple")
    Right (Just got) -> assertBool
      (mode ++ " case " ++ name ++ ": expected " ++ show expProb ++ " got " ++ show got)
      (abs (got - expProb) < probTolerance)
  where
    extractProb (VTuple (VFloat prob) _) = Just prob
    extractProb _                        = Nothing

-- | Extract the contents of every @```spll@ fenced code block from markdown.
spllBlocks :: String -> [String]
spllBlocks = go . lines
  where
    go [] = []
    go (l:ls)
      | isFenceOpen l = let (body, rest) = break isFenceClose ls
                        in unlines body : go (drop 1 rest)
      | otherwise     = go ls
    isFenceOpen l  = maybe False (== "spll") (stripPrefix "```" (trim l))
    isFenceClose l = trim l == "```"
    trim = dropWhile (== ' ')
