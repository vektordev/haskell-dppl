-- | Drives @tests/cases/known-issues/@ (design testcases-corpus-restructure):
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
import Data.List (isInfixOf)
import Data.Maybe (isNothing)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>), isExtensionOf, takeBaseName)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertFailure)

import SPLL.Lang.Types (CompilerError, Program)
import SPLL.IntermediateRepresentation (IREnv, defaultCompilerConfig, lookupIREnv, genFun, probFun, integFun)
import SPLL.Prelude (compile)
import TestCaseParser (ExpectFailure(..), corpusRoot, parseProgram, parseTestCasesFromString)

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
  return $ testGroup "KnownIssues" (map knownIssueTest names)

knownIssueTest :: String -> TestTree
knownIssueTest baseName = testCase baseName $ do
  let pplPath = knownIssuesDir </> (baseName ++ ".ppl")
      tstPath = knownIssuesDir </> (baseName ++ ".tst")
  prog <- parseProgram pplPath
  tstSrc <- readFile tstPath
  (_, _, mEf, _tcs) <- either error return (parseTestCasesFromString tstPath tstSrc)
  case mEf of
    Nothing -> assertFailure (tstPath ++ " is a known-issues .tst but declares no \
                              \`expect-failure:` header -- every case here must name \
                              \which of the four shapes it pins")
    Just ef -> checkExpectFailure baseName prog ef

checkExpectFailure :: String -> Program -> ExpectFailure -> IO ()
checkExpectFailure name prog ExpectCrash =
  assertCrashes name (compile defaultCompilerConfig prog) Nothing
checkExpectFailure name prog (ExpectDiagnostic needle) =
  assertCrashes name (compile defaultCompilerConfig prog) (Just needle)
checkExpectFailure name prog ExpectNoCode = do
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
-- Documentation only: the ordinary p()/cdf() rows below the header already
-- pin the (known-wrong) value, and the corpus's usual tuple comparison
-- already fails loudly the day a fix changes the computed number.
checkExpectFailure _ _ ExpectWrongResult = return ()

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
