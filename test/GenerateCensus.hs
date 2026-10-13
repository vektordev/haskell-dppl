{-# LANGUAGE ScopedTypeVariables #-}
-- | The generate-body census (docs-repo task
-- @impact-analysis-m2-drop-runtime-from-key@, section "Generate bodies:
-- assumed, not fuzzed").
--
-- 'TestFuzz.prop_Fuzz_BackendsAgree' never compares a generate body across
-- backends: a sample has no single value to agree on. M2 drops the runtimes
-- from generate-dependent keys on the argument that a generate body is (a)
-- sampling primitives, each small enough to test on its own, plus (b)
-- non-random IR built from constructs the agreement property compares.
--
-- This test keeps (b) honest in two links. "BackendCoverage" already requires
-- that every construct of a corpus /inference/ body is either compared by
-- the fuzzer or listed in 'fuzzCoverageExceptions'. So it is enough to require
-- here that every construct of a corpus /generate/ body is a sampling
-- primitive ('samplingConstructs') or also occurs in some corpus inference
-- body, bar exactly 'generateOnlyConstructs'. Equality, not inclusion, as in
-- "BackendCoverage": a construct that stops being generate-only must leave
-- the list, and one a generate body starts using alone must be added. The
-- chain avoids a second fuzz sample, which is where nearly all of
-- "BackendCoverage"'s time goes.
--
-- A construct census says nothing about evaluation order or sharing, which
-- only a body with effects can observe; that half of the argument is in the
-- task document, not here.
module GenerateCensus (generateCensusTests, samplingConstructs, generateOnlyConstructs) where

import Control.Exception (SomeException, try, evaluate)
import Control.Monad (forM)
import Data.List (sort, nub, (\\), intercalate)
import System.IO (hPutStrLn, stderr)
import System.Timeout (timeout)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure)

import SPLL.Prelude (compile)
import SPLL.IntermediateRepresentation (IREnv(..), IRExpr, IRFunGroup(..), defaultCompilerConfig)
import BackendAgreement (irEnvConstructs, inferenceBodies)
import BackendCoverage (fuzzCoverageExceptions)
import CorpusSweep

-- | The sampling primitives: the draws themselves, and the inverse-CDF
-- categorical index a neural read's sampler is built on (pure given its
-- uniform, but it exists only to turn a uniform into a categorical draw, and
-- appears only in generate bodies). Each has its own runtime function per
-- backend (@rand@, @randn@, @categorical_index@).
samplingConstructs :: [String]
samplingConstructs =
  [ "IRExpr:IRSample", "Sample:IRNormal", "Sample:IRUniform", "Builtin:BCategoricalIndex" ]

-- | Constructs of corpus generate bodies that are not sampling primitives and
-- occur in no corpus inference body, each with why. Empty as measured
-- 2026-10-09 over 556 programs: generate bodies use 47 constructs, the four
-- sampling primitives among them, and the other 43 all occur in some
-- inference body.
generateOnlyConstructs :: [(String, String)]
generateOnlyConstructs = []

genBodies :: IREnv -> [IRExpr]
genBodies (IREnv gs _ _) = [ b | g <- gs, Just (b, _) <- [genFun g] ]

-- | Non-slow programs, as "BackendCoverage" reads them, so the two links
-- range over one corpus.
generateCensusTests :: Corpus -> IO TestTree
generateCensusTests corpusIn = corpusSweepAll corpusIn SweepSpec
  { sweepName = "Slow.GenerateCensus", sweepTier = Slow, sweepSlow = SkipSlow
  , sweepSelect = const True
  , sweepNote = "every non-sampling construct of a corpus generate body occurs in a corpus inference body, bar a listed few" } $ \es ->
  return $ testGroup "GenerateCensus"
  [ testCase "generate-body constructs that are neither sampling nor in an inference body are exactly generateOnlyConstructs" $ do
      progs <- fmap concat $ forM es $ \e -> do
        let compiled = compile defaultCompilerConfig (ceProgram e)
            census which = either (const []) (irEnvConstructs which) compiled
        r <- timeout (30 * 1000 * 1000) $ try (evaluate (forced (census genBodies, census inferenceBodies)))
        return $ case r of
          Just (Right cs) -> [(ceName e, cs)]
          Just (Left (_ :: SomeException)) -> []
          Nothing -> []
      let genUsed = sort (nub (concatMap (fst . snd) progs))
          infUsed = nub (concatMap (snd . snd) progs)
          sampling = filter (`elem` samplingConstructs) genUsed
          generateOnly = (genUsed \\ samplingConstructs) \\ infUsed
          unfuzzed = filter (`elem` map fst fuzzCoverageExceptions) genUsed
          listed = map fst generateOnlyConstructs
          new = generateOnly \\ listed
          stale = listed \\ generateOnly
          users c = [ n | (n, (g, _)) <- progs, c `elem` g ]
          describe c = c ++ "  (" ++ show (length (users c)) ++ " corpus programs, e.g. "
                         ++ intercalate ", " (take 3 (users c)) ++ ")"
      hPutStrLn stderr ("generate census: corpus generate bodies use " ++ show (length genUsed)
                        ++ " constructs over " ++ show (length progs) ++ " programs; sampling primitives "
                        ++ show sampling ++ "; generate-only " ++ show generateOnly
                        ++ "; in fuzzCoverageExceptions (never compared): " ++ show unfuzzed)
      if null new && null stale then return () else assertFailure $ unlines $
        [ "generateOnlyConstructs is out of date." ]
        ++ (if null new then [] else "In a corpus generate body, not sampling, in no corpus inference body, and not listed:" : map (("  " ++) . describe) new)
        ++ (if null stale then [] else "Listed, but now in an inference body or unused (remove them):" : map ("  " ++) stale)
  ]
  where
    forced :: ([String], [String]) -> ([String], [String])
    forced t@(a, b) = length (concat (a ++ b)) `seq` t
