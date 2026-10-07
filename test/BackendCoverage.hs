{-# LANGUAGE ScopedTypeVariables #-}
-- | The other half of docs-repo task @backend-agreement-fuzzing@: which IR
-- constructs the corpus asks of the text backends that
-- 'TestFuzz.prop_Fuzz_BackendsAgree' never exercises.
--
-- @emitted-code-test-impact-analysis@ M2 wants to drop the runtimes and the
-- interpreter from a corpus program's test key on the strength of the
-- agreement property. That is only justified for constructs the property
-- actually puts through both backends, so this test computes, over the
-- probability and integrate bodies of
--
--   * the corpus (every non-slow program, default config), and
--   * a fixed-seed sample of the agreement property's own draws (the ones
--     with at least one interpreter-answered query -- what the property
--     compares),
--
-- the constructs ('BackendAgreement.irConstructs') the corpus uses and the
-- sample does not, and requires that set to be exactly
-- 'fuzzCoverageExceptions'. That list is two things at once: the generator's
-- to-do (@typed-program-generator-expansion@), and M2's exception list -- a
-- program emitting a listed construct keeps the runtime fingerprint in its
-- key. Equality, not inclusion, so the list cannot rot in either direction: a
-- construct the generator starts reaching must leave it, and one the corpus
-- starts using must be added (and so be seen).
--
-- Only inference bodies are compared on both sides, because only they are
-- compared by the property. Generate bodies are never checked across
-- backends (a sample is random, so there is no point value to agree on), nor
-- are writeLogits or normal functions; every corpus program has a generate
-- function, so M2 cannot drop the runtimes for /those/ on this evidence at
-- all. That is stated in the task doc rather than encoded here, since a
-- construct list cannot express it.
module BackendCoverage (backendCoverageTests, fuzzCoverageExceptions) where

import Control.Exception (SomeException, try, evaluate)
import Control.Monad (forM)
import Data.Either (rights)
import Data.List (sort, nub, (\\), intercalate)
import System.IO (hPutStrLn, stderr)
import System.Timeout (timeout)
import Test.QuickCheck (arbitrary, resize, vectorOf)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertFailure)

import SPLL.Prelude (compile)
import SPLL.IntermediateRepresentation (defaultCompilerConfig)
import BackendAgreement (AgreementCase(..), irEnvConstructs, inferenceBodies)
import CorpusSweep
import TestFuzz (prepareAgreementCase, genAgreementProgram, agreementFuzzSize)

-- | Corpus constructs the agreement property does not reach, each with why.
-- See the module header for what this list means and why it must be exact.
fuzzCoverageExceptions :: [(String, String)]
fuzzCoverageExceptions =
  -- Measured 2026-10-06 (sample of 1000 draws, ~550 compared, against 476
  -- non-slow corpus programs; the corpus uses 59 constructs, the sample
  -- covers 54). BIndex joined 2026-10-06 (60 constructs).
  [ ("Accessor:AcSubtree", "theta trees: the generator emits no ThetaI/Subtree (thetaTree, subtree)")
  , ("Accessor:AcTheta",   "theta trees: the generator emits no ThetaI (lambdaThetaInverse, affineChainEndpoint)")
  , ("Builtin:BIndex",     "agreement point query: needs the agreement fusion's `right v` arm over a contiguous Int domain (categoricalProductFusion)")
  , ("Builtin:BMapList",   "list map: the generator has no higher-order map over a list (map, mapMultList)")
  , ("Builtin:BZip OpMult", "agreement fusion: needs two independent categoricals compared with == (categoricalProductFusion)")
  , ("Operand:OpMax",      "max is forward-only and reaches an inference body only with enumerable operands (maxEnumerateBoth)")
  ]

-- | How many draws the fixed-seed sample takes, and from which seed. Large
-- enough that a construct the generator reaches at all is in it: a run of the
-- property compares ~150 programs, this sample ~4x that.
coverageDraws :: Int
coverageDraws = 1000

coverageSeed :: Int
coverageSeed = 20261006

backendCoverageTests :: Corpus -> IO TestTree
backendCoverageTests corpusIn = corpusSweepAll corpusIn SweepSpec
  { sweepName = "Slow.BackendAgreementCoverage", sweepTier = Slow, sweepSlow = SkipSlow
  , sweepSelect = const True
  , sweepNote = "the constructs the corpus compiles to and the agreement fuzzer never compares are listed" } $ \es ->
  return $ testGroup "BackendAgreementCoverage"
  [ testCase "corpus constructs the agreement fuzzer misses are exactly fuzzCoverageExceptions" $ do
      corpus <- corpusConstructs es
      fuzz <- fuzzConstructs
      let fuzzSet = nub (concat fuzz)
          used = sort (nub (concatMap snd corpus))
          uncovered = used \\ fuzzSet
          listed = map fst fuzzCoverageExceptions
          new = uncovered \\ listed
          stale = listed \\ uncovered
          users c = [ n | (n, cs) <- corpus, c `elem` cs ]
          example c = c ++ "  (" ++ show (length (users c)) ++ " corpus programs, e.g. "
                        ++ intercalate ", " (take 3 (users c)) ++ ")"
      hPutStrLn stderr ("backend agreement coverage: corpus uses " ++ show (length used)
                        ++ " constructs in inference bodies over " ++ show (length corpus)
                        ++ " programs; the fuzz sample (" ++ show (length fuzz) ++ " compared of "
                        ++ show coverageDraws ++ " drawn) covers " ++ show (length (used \\ uncovered))
                        ++ "; uncovered: " ++ show uncovered)
      if null new && null stale then return () else assertFailure $ unlines $
        [ "fuzzCoverageExceptions is out of date." ]
        ++ (if null new then [] else "Used by the corpus, never compared by the fuzzer, and not listed:" : map (("  " ++) . example) new)
        ++ (if null stale then [] else "Listed, but now covered by the fuzzer (remove them):" : map ("  " ++) stale)
  ]

-- | Per corpus program of the sweep (non-slow), the constructs of its inference bodies.
-- A program that does not compile in time is skipped: the corpus's own
-- groups are what report that.
corpusConstructs :: [CorpusEntry] -> IO [(String, [String])]
corpusConstructs entries =
  fmap concat $ forM entries $ \e -> do
      let p = ceProgram e
      r <- timeout (30 * 1000 * 1000) $ try (evaluate (forceList (either (const []) (irEnvConstructs inferenceBodies) (compile defaultCompilerConfig p))))
      return $ case r of
        Just (Right cs) -> [(ceName e, cs)]
        Just (Left (_ :: SomeException)) -> []
        Nothing -> []
  where
    forceList :: [String] -> [String]
    forceList xs = length (concat xs) `seq` xs

-- | The constructs of each compared program in the fixed-seed sample.
fuzzConstructs :: IO [[String]]
fuzzConstructs = do
  let draws = unGen (vectorOf coverageDraws ((,) <$> resize agreementFuzzSize genAgreementProgram <*> arbitrary))
                    (mkQCGen coverageSeed) agreementFuzzSize
  prepared <- mapM prepareAgreementCase draws
  forM (rights prepared) $ \c -> do
    r <- try (evaluate (forceList (irEnvConstructs inferenceBodies (acEnv c)))) :: IO (Either SomeException [String])
    return (either (const []) id r)
  where
    forceList xs = length (concat xs) `seq` xs
