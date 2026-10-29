{-# LANGUAGE ScopedTypeVariables #-}
-- | The IR contract on every corpus program (task
-- ir-package-boundary-c2-corpus-checks-contract, step C2 of design
-- ir-package-boundary).
--
-- The IR type checker ('SPLL.IRTypeCheck') is the contract between the
-- compiler and the backends. A corpus row can pass while the compiled IR
-- violates it, since the offending code is often unreachable, so this sweep
-- checks the contract itself: each program is compiled and 'checkIREnvWith'
-- runs on two environments of the same compile,
--
-- * @pre-optimizer@: the IR exactly as IR compilation, branch-count stripping,
--   per-value installation and the select pass left it ("After Select Pass"),
--   which is where @IRSelect@ is introduced under @--batched@;
-- * @final@: the environment the backends receive.
--
-- A program that fails at @final@ only was broken by the optimizer or one of
-- the batched post-passes; one that fails at @pre-optimizer@ was broken by
-- the compiler. The failure says which.
--
-- A program whose violation is known carries @ir-contract: violated
-- "<substring>"@ in its @.tst@ (docs/testing.md): the sweep then requires a
-- rejection whose message contains the substring, and fails when the program
-- starts to check, like an @expect-failure:@. A program that does not compile
-- has no IR and passes: the sweeps that run it own that failure.
--
-- The checker is cheap (about a second over the corpus); what the sweep costs
-- is the compile, which it does not share with other sweeps (a result shared
-- by many tasty threads is the shape that deadlocked the fuzz tier). It is
-- never skipped by the impact manifest: the verdict depends on the checker,
-- which the manifest's keys do not cover, and a skipped program would not be
-- checked.
--
-- Not covered: @--topK@, whose @writeLogits@ functions read @main_prob@ as if
-- it took no cutoff (docs task topk-writelogits-contract-violation).
module TestIRContract
  ( irContractTests
  , slowIrContractTests
  , contractVerdict
  , contractConfigs
  ) where

import Control.Exception (SomeException, evaluate, try)
import Data.List (intercalate, isInfixOf)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (lookupEnv)
import System.FilePath ((</>), isExtensionOf, takeBaseName)
import Test.Tasty (TestTree, testGroup)
import Data.Either (isLeft, isRight)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, testCaseInfo)

import SPLL.CompilerConfig
import SPLL.IR.Neural (oracleSignatures)
import SPLL.IRTypeCheck (checkIREnvWith, showIRTypeError)
import SPLL.IntermediateRepresentation (IREnv)
import SPLL.Lang.Types (Program)
import SPLL.Parser (tryParseProgram)
import SPLL.Prelude (compileStages, StageSnapshot(..), StageValue(..))
import MockNN (programMockOracle)

import CorpusSweep
import TestCaseParser (ExpectFailure(..), TstFile(..), corpusRoot, parseTstFileFromString)

-- | The configurations a program is compiled under, by tier. The default tier
-- covers the scalar and the batched pipeline (the latter adds @IRSelect@).
-- The Slow tier adds the log-space and branch-counting variants of every
-- program, and all four for the programs that are @slow@ themselves.
contractConfigs :: Tier -> Bool -> [(String, CompilerConfig)]
contractConfigs Default _ = scalarAndBatched
contractConfigs _ slowProgram =
  [ ("logSpace", defaultCompilerConfig { logSpace = True })
  , ("branch counts", defaultCompilerConfig { countBranches = True }) ]
  ++ (if slowProgram then scalarAndBatched else [])

scalarAndBatched :: [(String, CompilerConfig)]
scalarAndBatched =
  [ ("default", defaultCompilerConfig)
  , ("batched", defaultCompilerConfig { batched = True }) ]

-- | One check: which config and stage, and the checker's message if it
-- rejected the environment.
type Check = (String, Maybe String)

-- | The verdict on a program's checks against its @ir-contract:@ header.
-- 'Left' is the failure message, 'Right' what the passing test reports.
contractVerdict :: Maybe String -> [Check] -> Either String String
contractVerdict Nothing checks = case [ c | c@(_, Just _) <- checks ] of
  [] -> Right (show (length checks) ++ " checks")
  bad@((what, Just msg) : _) ->
    Left ("the compiled IR violates the IR contract (" ++ what ++ "): " ++ msg
          ++ (if length bad > 1 then "\nalso rejected at: " ++ intercalate ", " (map fst (tail bad)) else "")
          ++ "\nIf this is a known compiler bug, pin it with `ir-contract: violated \"<substring of the message>\"` in the .tst and file it.")
  _ -> Right ""
contractVerdict (Just sub) checks = case [ (what, msg) | (what, Just msg) <- checks ] of
  [] -> Left ("the compiled IR now type-checks at all " ++ show (length checks)
              ++ " checks, so the `ir-contract: violated` header is stale: remove it (the known issue may be fixed)")
  rejected
    | any ((sub `isInfixOf`) . snd) rejected -> Right ("known violation, rejected at " ++ intercalate ", " (map fst rejected))
    | otherwise -> Left ("the compiled IR is rejected, but not with a message containing " ++ show sub
                         ++ ", so the violation changed shape. Rejected at " ++ fst (head rejected) ++ ": " ++ snd (head rejected))

-- | Compile a program under each config and check the pre-optimizer and the
-- final environment. 'Nothing': nothing to check (the compile refused or
-- raised).
checksOf :: [(String, CompilerConfig)] -> Program -> IO (Maybe [Check])
checksOf configs p = do
  rs <- mapM one configs
  return (if null (concat rs) then Nothing else Just (concat rs))
  where
    externals = oracleSignatures (programMockOracle p)
    one (name, conf) = do
      r <- try (evaluate (forceChecks (stagesOf conf)))
      return $ case r of
        Left (_ :: SomeException) -> []
        Right cs -> [ (name ++ " " ++ stage, m) | (stage, m) <- cs ]
    stagesOf conf = case compileStages conf p of
      (snaps, Right final) ->
        [ ("pre-optimizer", verdictOf e) | StageSnapshot "After Select Pass" (StageIR e) <- snaps ]
        ++ [ ("final", verdictOf final) ]
      (_, Left _) -> []
    verdictOf :: IREnv -> Maybe String
    verdictOf e = either (Just . showIRTypeError) (const Nothing) (checkIREnvWith externals e)
    forceChecks cs = sum [ maybe 0 length m | (_, m) <- cs ] `seq` cs

-- | One program as a test.
programTest :: [(String, CompilerConfig)] -> String -> Maybe String -> Program -> TestTree
programTest configs name header p = testCaseInfo name $ do
  r <- checksOf configs p
  case r of
    Nothing -> return "does not compile, nothing to check"
    Just checks -> either assertFailure return (contractVerdict header checks)

-- | The default tier: every non-slow corpus program, and the known issues.
irContractTests :: Corpus -> IO TestTree
irContractTests corpus = do
  swept <- corpusSweep corpus SweepSpec
    { sweepName = "IRContract.Corpus", sweepTier = Default, sweepSlow = SkipSlow
    , sweepSelect = const True
    , sweepNote = "the compiled IR (before and after the optimizer, scalar and batched) type-checks" }
    (\e -> programTest (contractConfigs Default False) (ceName e) (ceIrContract e) (ceProgram e))
  known <- knownIssueContractTests
  return (testGroup "IRContract" [verdictTests, swept, known])

-- | The verdict rules, which no corpus program exercises in the failing
-- direction.
verdictTests :: TestTree
verdictTests = testGroup "verdict"
  [ testCase "no header, all accepted" $ assertBool "passes" (isRight (contractVerdict Nothing [("a final", Nothing)]))
  , testCase "no header, a rejection fails" $ assertBool "fails" (isLeft (contractVerdict Nothing [("a pre-optimizer", Nothing), ("a final", Just "boom")]))
  , testCase "header, matching rejection passes" $ assertBool "passes" (isRight (contractVerdict (Just "oo") [("a final", Just "boom")]))
  , testCase "header, program now accepted fails" $ assertBool "fails" (isLeft (contractVerdict (Just "oo") [("a final", Nothing)]))
  , testCase "header, a different message fails" $ assertBool "fails" (isLeft (contractVerdict (Just "zz") [("a final", Just "boom")]))
  ]

-- | The Slow tier: the other pipelines' configurations, and the programs that
-- are @slow@ themselves, bar the ones too slow to compile.
slowIrContractTests :: Corpus -> IO TestTree
slowIrContractTests corpus = corpusSweep corpus SweepSpec
  { sweepName = "Slow.IRContractConfigs (slow)", sweepTier = Slow, sweepSlow = IgnoreSlow
  , sweepSelect = notSlowForCompileCost
  , sweepNote = "the IR contract under log-space and branch counting, and on the slow programs" }
  (\e -> programTest (contractConfigs Slow (ceSlow e)) (ceName e) (ceIrContract e) (ceProgram e))

-- | The known issues are not part of the corpus ('TestKnownIssues'), but
-- their compiled IR is where a contract violation is most likely to be
-- pinned. Performance pins have no program to check (a template, or a compile
-- that does not terminate).
knownIssueContractTests :: IO TestTree
knownIssueContractTests = do
  let dir = corpusRoot </> "known-issues"
  exists <- doesDirectoryExist dir
  names <- if exists then (\es -> [ takeBaseName e | e <- es, ".ppl" `isExtensionOf` e ]) <$> listDirectory dir
                     else return []
  runSlow <- maybe False (const True) <$> lookupEnv "NEST_SLOW_TESTS"
  parsed <- mapM (\n -> do
                    src <- readFile (dir </> (n ++ ".tst"))
                    pplSrc <- readFile (dir </> (n ++ ".ppl"))
                    return (n, parseTstFileFromString (dir </> (n ++ ".tst")) src, pplSrc)) names
  let eligible = [ (n, t, pplSrc) | (n, Right t, pplSrc) <- parsed
                 , runSlow || not (tstSlow t), not (isPerformancePin (tstExpectFailure t)) ]
  return $ testGroup "KnownIssues"
    [ case tryParseProgram (dir </> (n ++ ".ppl")) pplSrc of
        Left _ -> testCaseInfo n (return "does not parse, nothing to check")
        Right p -> programTest (contractConfigs Default False) n (tstIrContract t) p
    | (n, t, pplSrc) <- eligible ]
  where
    isPerformancePin (Just ExpectGrowthAbove{})   = True
    isPerformancePin (Just ExpectCodeSizeAbove{}) = True
    isPerformancePin (Just ExpectHang{})          = True
    isPerformancePin _                            = False
