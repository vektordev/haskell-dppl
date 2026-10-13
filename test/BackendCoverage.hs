{-# LANGUAGE ScopedTypeVariables #-}
-- | The other half of docs-repo task @backend-agreement-fuzzing@: which IR
-- constructs the corpus asks of the text backends that
-- 'TestFuzz.prop_Fuzz_BackendsAgree' never exercises.
--
-- @emitted-code-test-impact-analysis@ M2 wants to drop the runtimes and the
-- interpreter from a corpus program's test key on the strength of the
-- agreement property. That is only justified for constructs the property
-- actually puts through both backends, so this test computes, over the
-- deterministic bodies (probability, integrate, writeLogits and normal) of
--
--   * the corpus (every non-slow program, default config;
--     'BackendAgreement.deterministicBodies'), and
--   * a fixed-seed sample of the agreement property's own draws (the ones
--     with at least one interpreter-answered query, and of those only the
--     bodies the property evaluates; 'BackendAgreement.comparedBodies'),
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
-- Generate bodies are left out on both sides: they are never checked across
-- backends (a sample is random, so there is no point value to agree on; task
-- @backend-agreement-writelogits-and-normal-functions@). M2 carries the
-- argument that generate is equivalent anyway: its random primitives are few
-- and simple, and its non-random IR is built from the constructs this census
-- certifies. That is stated in the task docs rather than encoded here, since a
-- construct list cannot express it.
module BackendCoverage (backendCoverageTests, fuzzCoverageExceptions, batchedFuzzCoverageExceptions) where

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
import Control.Concurrent.MVar (newMVar, modifyMVar)
import SPLL.IntermediateRepresentation (defaultCompilerConfig, CompilerConfig(..), IREnv, IRExpr)
import BackendAgreement (AgreementCase, irConstructs, irEnvConstructs, deterministicBodies, comparedBodies, maskedConstruct,
                         inferenceBodies, batchedComparedBodies)
import CorpusSweep
import TestCaseParser (Backend(Batched))
import TestFuzz (prepareAgreementCase, prepareAgreementBatched, genAgreementProgram, agreementFuzzSize)

-- | Corpus constructs the agreement property does not reach, each with why.
-- See the module header for what this list means and why it must be exact.
fuzzCoverageExceptions :: [(String, String)]
fuzzCoverageExceptions =
  -- Measured 2026-10-06 (sample of 1000 draws, ~550 compared, against 476
  -- non-slow corpus programs; the corpus uses 59 constructs, the sample
  -- covers 54). BIndex joined 2026-10-06 (60 constructs). Re-measured
  -- 2026-10-09 over all deterministic bodies (writeLogits and normal added;
  -- 556 non-slow corpus programs, 545 of 1000 draws compared): the corpus
  -- uses 62 constructs, the sample reaches 56 of them; IRSample and
  -- Sample:IRNormal, the writeLogits dead-arm noise, are masked rather than
  -- compared and so listed (maskedConstruct), leaving 54 covered.
  [ ("Accessor:AcSubtree", "theta trees: the generator emits no ThetaI/Subtree (thetaTree, subtree)")
  , ("Accessor:AcTheta",   "theta trees: the generator emits no ThetaI (lambdaThetaInverse, affineChainEndpoint)")
  , ("Builtin:BIndex",     "agreement point query: needs the agreement fusion's `right v` arm over a contiguous Int domain (categoricalProductFusion)")
  , ("Builtin:BMapList",   "list map: the generator has no higher-order map over a list (map, mapMultList)")
  , ("Builtin:BZip OpMult", "agreement fusion: needs two independent categoricals compared with == (categoricalProductFusion)")
  , ("Operand:OpMax",      "max is forward-only and reaches an inference body only with enumerable operands (maxEnumerateBoth)")
  , ("IRExpr:IRSample",    "writeLogits dead-arm noise: a random draw, whose slots the agreement property masks rather than compares (maskedConstruct)")
  , ("Sample:IRNormal",    "writeLogits dead-arm noise: a random draw, whose slots the agreement property masks rather than compares (maskedConstruct)")
  ]

-- | The batched arm's counterpart of 'fuzzCoverageExceptions' (task
-- @backend-agreement-batched-arm@): constructs of the probability and
-- integrate bodies of the corpus programs that declare @batched@, compiled
-- for batched mode, that the agreement property never puts through the
-- batched backend. Exact, like the scalar list: it says which
-- @batched-vs-expected@ checks the fuzzer certifies (a program none of whose
-- batched constructs is listed). Only the value check: the corpus's batched
-- gradient, generate-density, dense and topK checks are not compared by the
-- fuzzer at all.
batchedFuzzCoverageExceptions :: [(String, String)]
batchedFuzzCoverageExceptions =
  -- Measured 2026-10-09 (the same 1000-draw sample: 337 of its 548 compared
  -- programs are batched-eligible; 233 non-slow corpus programs declare
  -- `batched`): the corpus uses 56 constructs, the sample reaches 54.
  [ ("Accessor:AcSubtree", "theta trees: the generator emits no ThetaI/Subtree (thetaTree, subtree)")
  , ("Accessor:AcTheta",   "theta trees: the generator emits no ThetaI (gaussianTrajectory4, theta)")
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
  , sweepNote = "the constructs the corpus compiles to and the agreement fuzzer never compares are listed" } $ \es -> do
  -- Both censuses draw the same sample; whichever runs first prepares it.
  cache <- newMVar Nothing
  let sample = modifyMVar cache $ \c -> case c of
        Just cs -> return (c, cs)
        Nothing -> do
          cs <- sampleCases
          return (Just cs, cs)
  return $ testGroup "BackendAgreementCoverage"
    [ testCase "corpus constructs the agreement fuzzer misses are exactly fuzzCoverageExceptions" $ do
        corpus <- corpusConstructs es
        fuzz <- fuzzConstructs sample
        checkExceptions "scalar" "fuzzCoverageExceptions" "deterministic bodies" corpus fuzz fuzzCoverageExceptions
    , testCase "batched corpus constructs the agreement fuzzer misses are exactly batchedFuzzCoverageExceptions" $ do
        corpus <- corpusConstructsWith (defaultCompilerConfig { batched = True }) inferenceBodies
                    [ e | e <- es, Batched `elem` ceBackends e ]
        fuzz <- batchedFuzzConstructs sample
        checkExceptions "batched" "batchedFuzzCoverageExceptions" "the batched-compiled inference bodies of `batched`-declaring programs," corpus fuzz batchedFuzzCoverageExceptions
    ]

-- | The census verdict: the constructs the corpus uses and the fuzz sample
-- does not must be exactly @listed@.
checkExceptions :: String -> String -> String -> [(String, [String])] -> [[String]] -> [(String, String)] -> IO ()
checkExceptions arm listName what corpus fuzz exceptions = do
  let fuzzSet = filter (not . maskedConstruct) (nub (concat fuzz))
      used = sort (nub (concatMap snd corpus))
      uncovered = used \\ fuzzSet
      listed = map fst exceptions
      new = uncovered \\ listed
      stale = listed \\ uncovered
      users c = [ n | (n, cs) <- corpus, c `elem` cs ]
      example c = c ++ "  (" ++ show (length (users c)) ++ " corpus programs, e.g. "
                    ++ intercalate ", " (take 3 (users c)) ++ ")"
  hPutStrLn stderr ("backend agreement coverage (" ++ arm ++ "): corpus uses " ++ show (length used)
                    ++ " constructs in " ++ what ++ " over " ++ show (length corpus)
                    ++ " programs; the fuzz sample (" ++ show (length fuzz) ++ " compared of "
                    ++ show coverageDraws ++ " drawn) covers " ++ show (length (used \\ uncovered))
                    ++ "; uncovered: " ++ show uncovered)
  if null new && null stale then return () else assertFailure $ unlines $
    [ listName ++ " is out of date." ]
    ++ (if null new then [] else "Used by the corpus, never compared by the fuzzer, and not listed:" : map (("  " ++) . example) new)
    ++ (if null stale then [] else "Listed, but now covered by the fuzzer (remove them):" : map ("  " ++) stale)

-- | Per corpus program of the sweep (non-slow), the constructs of its
-- deterministic bodies.
-- A program that does not compile in time is skipped: the corpus's own
-- groups are what report that.
corpusConstructs :: [CorpusEntry] -> IO [(String, [String])]
corpusConstructs = corpusConstructsWith defaultCompilerConfig deterministicBodies

-- | 'corpusConstructs' under a config, over the bodies @which@ picks.
corpusConstructsWith :: CompilerConfig -> (IREnv -> [IRExpr]) -> [CorpusEntry] -> IO [(String, [String])]
corpusConstructsWith conf which entries =
  fmap concat $ forM entries $ \e -> do
      let p = ceProgram e
      r <- timeout (30 * 1000 * 1000) $ try (evaluate (forceList (either (const []) (irEnvConstructs which) (compile conf p))))
      return $ case r of
        Just (Right cs) -> [(ceName e, cs)]
        Just (Left (_ :: SomeException)) -> []
        Nothing -> []
  where
    forceList :: [String] -> [String]
    forceList xs = length (concat xs) `seq` xs

-- | The fixed-seed sample's compared cases.
sampleCases :: IO [AgreementCase]
sampleCases = do
  let draws = unGen (vectorOf coverageDraws ((,) <$> resize agreementFuzzSize genAgreementProgram <*> arbitrary))
                    (mkQCGen coverageSeed) agreementFuzzSize
  rights <$> mapM prepareAgreementCase draws

-- | The constructs of each batched-compared program in the fixed-seed sample:
-- the compared cases batched mode takes, over their batched compile's
-- inference bodies ('batchedComparedBodies').
batchedFuzzConstructs :: IO [AgreementCase] -> IO [[String]]
batchedFuzzConstructs sample = do
  cases <- sample
  batchedCases <- rights <$> mapM prepareAgreementBatched cases
  forM batchedCases $ \c -> do
    r <- try (evaluate (forceList (sort (nub (concatMap irConstructs (batchedComparedBodies c)))))) :: IO (Either SomeException [String])
    return (either (const []) id r)
  where
    forceList xs = length (concat xs) `seq` xs

-- | The constructs of each compared program in the fixed-seed sample.
fuzzConstructs :: IO [AgreementCase] -> IO [[String]]
fuzzConstructs sample = do
  cases <- sample
  forM cases $ \c -> do
    r <- try (evaluate (forceList (sort (nub (concatMap irConstructs (comparedBodies c)))))) :: IO (Either SomeException [String])
    return (either (const []) id r)
  where
    forceList xs = length (concat xs) `seq` xs
