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
--   * every DEFINITION listed in examples/showcase.freeze is driven directly
--     by name and its probability/cumulative result is pinned -- this freezes
--     the behaviour of the individual documented helpers, not just `main`;
--   * every @```spll@ block in the README parses and compiles; a @```text@
--     block placed immediately after one supplies expected p()/cdf() output
--     (in showcase.tst syntax) which is then verified against that snippet.
--
-- Definitions absent from showcase.freeze are guaranteed only to PARSE (some
-- are intentionally generate-only or parse-only syntax demonstrations); the
-- freeze file is the opt-in list of definitions whose behaviour is frozen.
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
import SPLL.Prelude (compile, runGenC, runProbC, runIntegC, runProbNamedC, runIntegNamedC)
import SPLL.IntermediateRepresentation (defaultCompilerConfig, IREnv, IRValue)
import TestCaseParser (TestCase(..), parseTestCasesFromString,
                       FreezeCase(..), FreezeMode(..), parseFreezeCasesFromString)
import TestTolerances (probTolerance)

showcasePath :: FilePath
showcasePath = "examples/showcase.ppl"

showcaseTstPath :: FilePath
showcaseTstPath = "examples/showcase.tst"

showcaseFreezePath :: FilePath
showcaseFreezePath = "examples/showcase.freeze"

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
  freezeSrc <- readFile showcaseFreezePath
  readmeSrc <- readFile readmePath
  let scProg       = tryParseProgram showcasePath scSrc
      tstCases     = either (const []) (\(_, _, tcs) -> tcs) (parseTestCasesFromString showcaseTstPath tstSrc)
      freezeParsed = parseFreezeCasesFromString showcaseFreezePath freezeSrc
      readmeBlocks = spllBlocksWithExpected readmeSrc
  return $ testGroup "Showcase"
    [ testCase (showcasePath ++ " parses") $
        assertParses showcasePath scSrc
    , testCase (showcasePath ++ " main generates") $
        either (assertFailure . prettyParse) assertGenerates scProg
    , testCase (showcasePath ++ " main matches showcase.tst (probability + cumulative)") $
        either (assertFailure . prettyParse) (assertTstMatches tstCases) scProg
    , freezeTests scProg freezeParsed
    , readmeTests readmeBlocks
    ]

-- | Per-definition behavioural freeze: drive each definition named in
-- showcase.freeze by name and pin its inference result.
freezeTests :: Either (ParseErrorBundle String Void) Program -> Either String [FreezeCase] -> TestTree
freezeTests scProg freezeParsed = testGroup "showcase.freeze anchors" $
  case (scProg, freezeParsed) of
    (Left e, _) -> [ testCase "showcase parses" $ assertFailure (prettyParse e) ]
    (_, Left e) -> [ testCase (showcaseFreezePath ++ " parses") $ assertFailure e ]
    (Right p, Right cases) -> case compile defaultCompilerConfig p of
      Left err  -> [ testCase "showcase compiles" $ assertFailure (show err) ]
      Right env ->
        testCase (showcaseFreezePath ++ " is non-empty")
                 (assertBool "no freeze anchors parsed" (not (null cases)))
        : [ testCase (freezeLabel c) $ assertFreeze env p c | c <- cases ]

freezeLabel :: FreezeCase -> String
freezeLabel (FreezeCase name args mode sample _) =
  name ++ argStr ++ " " ++ modeStr mode ++ "(" ++ show sample ++ ")"
  where argStr = if null args then "" else show args
        modeStr FreezeProb = "p"
        modeStr FreezeCdf  = "cdf"

assertFreeze :: IREnv -> Program -> FreezeCase -> IO ()
assertFreeze env p c@(FreezeCase name args mode sample expected) =
  checkQuery (modeName mode) (freezeLabel c) result expected
  where
    result = case mode of
      FreezeProb -> runProbNamedC p env name args sample
      FreezeCdf  -> runIntegNamedC p env name args sample
    modeName FreezeProb = "probability"
    modeName FreezeCdf  = "cumulative"

-- | README examples: every @```spll@ block parses and compiles, and if an
-- expected-output @```text@ block follows it, its p()/cdf() lines are verified.
readmeTests :: [(String, Maybe String)] -> TestTree
readmeTests blocks = testGroup "README ```spll examples" $
  [ testCase (label ++ suffix mexp) $ do
      assertParses label block
      case tryParseProgram readmePath block of
        Left e     -> assertFailure (prettyParse e)
        Right prog -> do
          assertCompiles prog
          case mexp of
            Nothing       -> return ()
            Just expected -> case parseTestCasesFromString label expected of
              Left perr           -> assertFailure ("expected-output block failed to parse:\n" ++ perr)
              Right (_, _, cases) -> assertTstMatches cases prog
  | (i, (block, mexp)) <- zip [1 :: Int ..] blocks
  , let label = readmePath ++ " ```spll block " ++ show i
  ] ++
  [ testCase "README has the expected number of ```spll blocks" $
      length blocks @?= expectedReadmeBlocks ]
  where suffix Nothing  = " parses & compiles"
        suffix (Just _) = " parses, compiles & matches expected output"

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

-- | Extract every @```spll@ fenced block from markdown, each paired with the
-- expected-output @```text@ block that immediately follows it (only blank lines
-- may separate them), if any.
spllBlocksWithExpected :: String -> [(String, Maybe String)]
spllBlocksWithExpected = go . lines
  where
    go [] = []
    go (l:ls)
      | isFenceOpen "spll" l =
          let (body, rest)     = break isFenceClose ls
              afterSpll        = drop 1 rest
              (mexp, rest')    = grabExpected afterSpll
          in (unlines body, mexp) : go rest'
      | otherwise = go ls
    grabExpected ls = case dropWhile (null . trim) ls of
      (l:rest) | isFenceOpen "text" l ->
          let (body, rest') = break isFenceClose rest
          in (Just (unlines body), drop 1 rest')
      _ -> (Nothing, ls)
    isFenceOpen tag l = maybe False (== tag) (stripPrefix "```" (trim l))
    isFenceClose l    = trim l == "```"
    trim = dropWhile (== ' ')
