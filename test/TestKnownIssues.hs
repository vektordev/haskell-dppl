{-# LANGUAGE PatternSynonyms #-}
-- | Drives @test/cases/known-issues/@ (design testcases-corpus-restructure):
-- a folder of @.ppl@/@.tst@ pairs pinned to a *specific*, known compiler bug,
-- each carrying an @expect-failure:@ header naming the shape it demonstrates
-- (see 'TestCaseParser.ExpectFailure'). Unlike the rest of the corpus (whose
-- programs are all expected to compile and run correctly), every program here
-- is expected to keep failing exactly as documented -- so the suite fails
-- loudly, not silently, the day the underlying bug gets fixed and a case here
-- needs to move out (to the ordinary corpus, or to "TestRejection" if the fix
-- turned it into a deliberate, graceful refusal).
--
-- This folder is deliberately excluded from 'TestCaseParser.listCorpusPplFiles'
-- (and so from every ordinary corpus sweep -- End2End, the batched groups,
-- the @Corpus@ metamorphic properties, ...), since those all assume a program
-- compiles; a known issue by definition does not.
--
-- Coexists with "TestRejection" rather than replacing it: a bespoke,
-- multi-assertion regression (e.g. one that also checks a *different* variant
-- is unaffected) stays a hand-written HUnit group there. This module is for
-- the common single-diagnostic shape only, filed by dropping in a program
-- instead of writing new Haskell.
module TestKnownIssues (knownIssuesTests) where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (filterM)
import Data.List (intercalate, isInfixOf)
import Data.Maybe (isNothing)
import System.Directory (doesDirectoryExist, getCurrentDirectory, listDirectory)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), isExtensionOf, takeBaseName)
import System.IO (hClose, hPutStr)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertFailure)

import SPLL.Lang.Types (CompilerError, Program, GenericValue(..))
import SPLL.IntermediateRepresentation
  ( IREnv(..), IRValue, defaultCompilerConfig, lookupIREnv
  , IRFunGroup(..), showRefusal
  , resultImpossible, pattern VProbDim
  )
import SPLL.Prelude (compile, runProbC, runIntegC)
import TestCaseParser
  ( Backend(..), ExpectFailure(..), TestCase(..), Expectation(..), corpusRoot
  , parseProgram, parseTestCasesFromString
  )
import TestTolerances (probTolerance)
import End2EndTesting (networkMocks, pythonTestScript, resolveNeuralTestCase, shapeNeuralTestCase)

knownIssuesDir :: FilePath
knownIssuesDir = corpusRoot </> "known-issues"

-- | Every known-issues base name, found by a flat listing (unlike the rest of
-- the corpus, this folder is not itself subdivided into topics).
knownIssueBaseNames :: IO [String]
knownIssueBaseNames = do
  exists <- doesDirectoryExist knownIssuesDir
  if not exists
    then return []
    else do
      entries <- listDirectory knownIssuesDir
      return [ takeBaseName e | e <- entries, ".ppl" `isExtensionOf` e ]

knownIssuesTests :: IO TestTree
knownIssuesTests = do
  names <- knownIssueBaseNames
  -- A `slow`-headered pin runs only under NEST_SLOW_TESTS, like the slow
  -- programs of the ordinary corpus. The header is read here, while the tree
  -- is built, so a skipped pin is absent rather than a passing no-op.
  runSlow <- maybe False (const True) <$> lookupEnv "NEST_SLOW_TESTS"
  kept <- filterM (\n -> (runSlow ||) . not <$> isSlow n) names
  return $ testGroup "KnownIssues" (map knownIssueTest kept)
  where
    isSlow n = do
      let tstPath = knownIssuesDir </> (n ++ ".tst")
      src <- readFile tstPath
      (_, slow, _, _) <- either error return (parseTestCasesFromString tstPath src)
      length src `seq` return slow

knownIssueTest :: String -> TestTree
knownIssueTest baseName = testCase baseName $ do
  let pplPath = knownIssuesDir </> (baseName ++ ".ppl")
      tstPath = knownIssuesDir </> (baseName ++ ".tst")
  prog <- parseProgram pplPath
  tstSrc <- readFile tstPath
  (backends, _, mEf, tcs) <- either error return (parseTestCasesFromString tstPath tstSrc)
  case mEf of
    Nothing -> assertFailure (tstPath ++ " is a known-issues .tst but declares no \
                              \`expect-failure:` header -- every case here must name \
                              \which of the five shapes it pins")
    Just ef -> checkExpectFailure baseName prog backends ef tcs

checkExpectFailure :: String -> Program -> [Backend] -> ExpectFailure -> [TestCase] -> IO ()
checkExpectFailure name prog _ ExpectCrash _ =
  assertCrashes name (compile defaultCompilerConfig prog) Nothing
checkExpectFailure name prog _ (ExpectDiagnostic needle) _ =
  assertCrashes name (compile defaultCompilerConfig prog) (Just needle)
checkExpectFailure name prog _ (ExpectRefused needle) _ = do
  result <- forced (compile defaultCompilerConfig prog)
  case result of
    Left ex -> assertFailure (name ++ ": expected a refused variant, but compile crashed: " ++ show ex)
    Right _ -> case compile defaultCompilerConfig prog of
      Left err -> assertFailure (name ++ ": expected a refused variant, but the compile was \
                                 \refused outright: " ++ err)
      Right env ->
        let reasons = [ groupName g ++ "." ++ lbl ++ ": " ++ showRefusal r
                      | g <- envGroups env, (lbl, r) <- refusedVariants g ]
        in assertBool (name ++ ": expected a variant refused with a reason containing \""
                       ++ needle ++ "\", but the recorded refusals are: "
                       ++ (if null reasons then "(none) -- the bug it pins may be fixed; if so, \
                                                \move or retire this known-issues case"
                           else intercalate "\n" reasons))
             (any (needle `isInfixOf`) reasons)
  where envGroups (IREnv gs _ _) = gs
checkExpectFailure name prog _ ExpectNoCode _ = do
  result <- forced (compile defaultCompilerConfig prog)
  case result of
    Left ex -> assertFailure (name ++ ": expected compile to succeed with a silently absent \
                              \variant, but it crashed instead: " ++ show ex)
    Right _ -> case compile defaultCompilerConfig prog of
      Left err -> assertFailure (name ++ ": expected compile to succeed with a silently \
                                 \absent variant, but it was refused outright: " ++ err)
      Right env ->
        let m = lookupIREnv "main" env
        in assertBool (name ++ ": expected at least one of generate/probability/integrate \
                       \to be silently absent, but main compiled all three")
             (isNothing (genFun m) || isNothing (probFun m) || isNothing (integFun m))
-- The rows below the header pin the (known-wrong) value the compiled program
-- produces today, on every backend the @backends:@ header declares that this
-- harness can evaluate (see 'checkableBackends'). Each row must still match:
-- a fix changes the number and fails the pin, and so does the wrong value
-- drifting. A compile that crashes or is refused, a query that crashes or is
-- refused, and a non-prob/dim result all fail too -- the pin documents a
-- program that compiles and answers, just wrongly.
checkExpectFailure name prog backends ExpectWrongResult tcs = do
  checked <- requireCheckable "wrong-result" name backends
  let rows = queryRows tcs
  if null rows
    then assertFailure (name ++ ": an `expect-failure: wrong-result` pin has no p()/cdf() rows, \
                        \so nothing pins the wrong value")
    else do
      result <- forced (compile defaultCompilerConfig prog)
      case result of
        Left ex -> assertFailure (name ++ ": expected a wrong-result pin to compile, but the \
                                  \compile crashed: " ++ show ex)
        Right _ -> case compile defaultCompilerConfig prog of
          Left err -> assertFailure (name ++ ": expected a wrong-result pin to compile, but it \
                                     \was refused outright: " ++ err)
          Right env -> mapM_ (\b -> mapM_ (assertStillWrong b name prog env) rows) checked
-- The mechanism is unpinned: the rows below state the *idealized* value, and
-- the case passes as long as the compiled program does not yet produce it
-- on any backend the @backends:@ header declares (read exactly as the rest
-- of the corpus reads it: no header means the three scalar backends). The
-- header names where the bug is pinned, so a Python-only bug is spelled
-- @backends: python@ and is not reported "may be fixed" merely because the
-- interpreter already gets it right.
checkExpectFailure name prog backends ExpectBroken tcs = do
  checked <- requireCheckable "broken" name backends
  result <- forced (compile defaultCompilerConfig prog)
  case result of
    Left _ -> return ()      -- crashed at compile time: still broken everywhere
    Right _ -> case compile defaultCompilerConfig prog of
      Left _ -> return ()    -- refused outright: still broken everywhere
      Right env -> mapM_ (\b -> mapM_ (assertStillBroken b name prog env) (queryRows tcs)) checked

-- | The backends a @broken@ or @wrong-result@ pin's rows can be run against
-- here: the interpreter in-process, and the Python backend through the same
-- emitted script End2End runs. Julia is not (it is not installed everywhere
-- the suite runs, and a missing binary would read as "still broken", i.e. a
-- silently green pin), nor are batched/dense. A pin declaring only those
-- fails loudly instead of passing vacuously.
checkableBackends :: [Backend]
checkableBackends = [Interpreter, Python]

-- | The declared backends this harness can evaluate, failing the pin when
-- there are none (it would otherwise pass without checking anything).
requireCheckable :: String -> String -> [Backend] -> IO [Backend]
requireCheckable shape name backends = do
  let checked = filter (`elem` checkableBackends) backends
  if null checked
    then assertFailure (name ++ ": an `expect-failure: " ++ shape ++ "` pin must declare at \
                        \least one backend the known-issues harness can evaluate (" ++
                        intercalate ", " (map show checkableBackends) ++
                        "); declared only " ++ intercalate ", " (map show backends) ++
                        ", so its rows would never be checked")
    else return checked

-- | The p()/cdf() rows: both checks only cover the two ordinary probability
-- query shapes, so anything else (argmax_p, writeLogits) is left unchecked.
queryRows :: [TestCase] -> [TestCase]
queryRows = filter isQuery
  where
    isQuery ProbTestCase{}  = True
    isQuery CumulTestCase{} = True
    isQuery _               = False

-- | One idealized row on one backend: assert the result does not yet match
-- the documented-correct value. A crash (at codegen, module load, or run
-- time), a refused query, or a non-prob/dim result are all still "broken";
-- only an exact (within-tolerance) match to the idealized row counts as "may
-- be fixed now".
assertStillBroken :: Backend -> String -> Program -> IREnv -> TestCase -> IO ()
assertStillBroken Interpreter name prog env (ProbTestCase caseName sample params expct) =
  checkStillBroken name caseName expct (runProbC prog env params sample)
assertStillBroken Interpreter name prog env (CumulTestCase caseName sample params expct) =
  checkStillBroken name caseName expct (runIntegC prog env params sample)
assertStillBroken Python name prog env tc = do
  matched <- pythonRowMatches prog env tc
  assertBool
    (name ++ "/" ++ rowName tc ++ " [python]: the Python backend now matches the documented \
             \idealized value -- this known issue may be fixed; if so, tighten or move this \
             \case out of known-issues")
    (not matched)
assertStillBroken _ _ _ _ _ = return ()

-- | One pinned (wrong) row on one backend: assert the result still matches
-- it. Anything else -- a different value, a crash, a refused query, a
-- non-prob/dim result -- means the bug moved or was fixed.
assertStillWrong :: Backend -> String -> Program -> IREnv -> TestCase -> IO ()
assertStillWrong Interpreter name prog env (ProbTestCase caseName sample params expct) =
  checkStillWrong name caseName expct (runProbC prog env params sample)
assertStillWrong Interpreter name prog env (CumulTestCase caseName sample params expct) =
  checkStillWrong name caseName expct (runIntegC prog env params sample)
assertStillWrong Python name prog env tc = do
  matched <- pythonRowMatches prog env tc
  assertBool
    (name ++ "/" ++ rowName tc ++ " [python]: no longer produces the pinned wrong value \
             \(or failed to load/run) -- the bug may be fixed or may have moved; triage \
             \this known-issues case (move it to the corpus if fixed, re-pin if the wrong \
             \value changed)")
    matched
assertStillWrong _ _ _ _ _ = return ()

checkStillWrong :: String -> String -> Expectation -> Either CompilerError IRValue -> IO ()
checkStillWrong name caseName expct er = do
  r <- try (evaluate (length (show er)) >> return er)
         :: IO (Either SomeException (Either CompilerError IRValue))
  let here = name ++ "/" ++ caseName ++ " [interpreter]: "
      triage = " -- the bug may be fixed or may have moved; triage this known-issues case \
               \(move it to the corpus if fixed, re-pin if the wrong value changed)"
  case r of
    Left ex -> assertFailure (here ++ "the query crashed instead of producing the pinned \
                                      \wrong value: " ++ show ex ++ triage)
    Right (Left err) -> assertFailure (here ++ "the query was refused instead of producing \
                                               \the pinned wrong value: " ++ err ++ triage)
    Right (Right res@(VProbDim outProb outDim)) ->
      assertBool (here ++ "got " ++ show res ++ ", not the pinned wrong value " ++ show expct ++ triage)
        (matchesExpectation expct outProb outDim res)
    Right (Right res) -> assertFailure (here ++ "got a non-prob/dim result " ++ show res ++ triage)

rowName :: TestCase -> String
rowName (ProbTestCase n _ _ _)  = n
rowName (CumulTestCase n _ _ _) = n
rowName _                       = "?"

-- | Run one row through the emitted Python module (End2End's own script, with
-- neural parameters resolved and identity network mocks, exactly as
-- 'End2EndTesting.testPython' does). True iff the script exits 0, i.e. the
-- module loaded and the row matched within tolerance. Output is captured, not
-- echoed: a still-broken pin failing to load is the expected outcome here.
-- A Haskell-side codegen crash counts as "does not match".
pythonRowMatches :: Program -> IREnv -> TestCase -> IO Bool
pythonRowMatches prog env tc = do
  projectDir <- getCurrentDirectory
  let script = pythonTestScript projectDir (networkMocks prog) env [resolveNeuralTestCase prog (shapeNeuralTestCase prog tc)]
  forcedScript <- try (evaluate (length script)) :: IO (Either SomeException Int)
  case forcedScript of
    Left _ -> return False
    Right _ -> withSystemTempFile "spll_known_issue.py" $ \tmpPath h -> do
      hPutStr h script
      hClose h
      (code, _, _) <- readProcessWithExitCode "python3" [tmpPath] ""
      return (code == ExitSuccess)

checkStillBroken :: String -> String -> Expectation -> Either CompilerError IRValue -> IO ()
checkStillBroken name caseName expct er = do
  r <- try (evaluate (length (show er)) >> return er)
         :: IO (Either SomeException (Either CompilerError IRValue))
  case r of
    Left _ -> return ()               -- runtime crash: still broken
    Right (Left _) -> return ()       -- query refused outright: still broken
    Right (Right res@(VProbDim outProb outDim)) ->
      assertBool
        (name ++ "/" ++ caseName ++ " [interpreter]: now matches the documented idealized value -- \
                 \this known issue may be fixed; if so, tighten or move this case out \
                 \of known-issues")
        (not (matchesExpectation expct outProb outDim res))
    Right (Right _) -> return ()      -- not a prob/dim result: still broken

matchesExpectation :: Expectation -> Double -> Double -> IRValue -> Bool
matchesExpectation (Possible (VFloat expectedProb) (VFloat expectedDim) mImp) outProb outDim res =
  abs (outProb - expectedProb) < probTolerance
    && outDim == expectedDim
    && matchesImposs mImp res
matchesExpectation (Possible {}) _ _ _ = False
matchesExpectation Impossible outProb _ res =
  abs outProb < probTolerance && matchesImposs (Just True) res

matchesImposs :: Maybe Bool -> IRValue -> Bool
matchesImposs Nothing _ = True
matchesImposs (Just expected) res = resultImpossible res == Just expected

-- | Force a compile result, catching either a genuine crash (an uncaught
-- exception thrown while forcing it) or an ordinary, non-crashing result
-- (a graceful 'Left', or a 'Right' that forces cleanly).
forced :: Show a => Either CompilerError a -> IO (Either SomeException Int)
forced = try . evaluate . length . show

-- | 'ExpectCrash'/'ExpectDiagnostic': the known issue must still crash at
-- compile time. A graceful @Left@ does not count -- that is an intended
-- refusal, not the bug this folder pins.
assertCrashes :: String -> Either CompilerError IREnv -> Maybe String -> IO ()
assertCrashes name compiled mNeedle = do
  result <- forced compiled
  case result of
    Left ex -> case mNeedle of
      Nothing -> return ()
      Just needle -> assertBool
        (name ++ ": crashed, but not with the pinned diagnostic \"" ++ needle
               ++ "\": " ++ show ex)
        (needle `isInfixOf` show ex)
    Right _ -> assertFailure
      (name ++ ": expected this known issue to still crash at compile time, but it did not \
              \-- the bug it pins may be fixed; if so, move or retire this known-issues case")
