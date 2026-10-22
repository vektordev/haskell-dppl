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
-- 'fuzzCoverageExceptions', the generator's to-do
-- (@typed-program-generator-expansion@). M2 itself certifies by the IR fuzz
-- generator's reach ('CertifiedCensus.certifiedConstructs', held exact by
-- 'irGeneratorCoverageTests'), which covers every construct listed here.
-- Equality, not inclusion, so the list cannot rot in either direction: a
-- construct the generator starts reaching must leave it, and one the corpus
-- starts using must be added (and so be seen).
--
-- Generate bodies are left out on both sides of this census: the typed
-- fuzzer checks a sample only for support, by the interpreter's probability
-- function (task @backend-agreement-generate-support@). The IR fuzz
-- generator's census ('irGeneratorCoverageTests') does count them: since its
-- M4 it compares generate bodies on both backends by replaying each backend's
-- draws through the interpreter.
module BackendCoverage (backendCoverageTests, irGeneratorCoverageTests, fuzzCoverageExceptions, batchedFuzzCoverageExceptions, irGeneratorDeferred) where

import Control.Exception (SomeException, try, evaluate)
import Control.Monad (forM)
import Data.Either (rights)
import Data.List (sort, nub, (\\), intercalate)
import Data.Maybe (fromMaybe, catMaybes)
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
import BackendAgreement (AgreementCase, comparedBodies, maskedConstruct, batchedComparedBodies)
import CertifiedCensus (irConstructs, irEnvConstructs, deterministicBodies, inferenceBodies,
                        certifiedConstructs, allBodies, batchedCertifiedConstructs, batchedReachedNotCompared)
import CorpusSweep
import TestCaseParser (Backend(Batched))
import IRFuzz (irGeneratorConstructs, irGeneratorBatchedConstructs)
import TestFuzz (prepareAgreementCase, prepareAgreementNeighbour, prepareAgreementBatched, genAgreementProgram, agreementFuzzSize)

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

-- | The batched arms' counterpart of 'fuzzCoverageExceptions' (tasks
-- @backend-agreement-batched-arm@, @batched-backend-reference-compliance@):
-- constructs of the probability and integrate bodies of the corpus programs
-- that declare @batched@, compiled for batched mode, that neither batched arm
-- (the typed fuzzer's, the IR generator's) puts through the batched backend.
-- Exact, like the scalar list. The programs using one are the ones that keep
-- their @batched-vs-expected@ check ('CertifiedCensus.batchedCertifiedConstructs').
-- Only the value check: the corpus's batched gradient, generate-density,
-- dense and topK checks are not compared by either arm at all.
batchedFuzzCoverageExceptions :: [(String, String)]
batchedFuzzCoverageExceptions =
  -- Measured 2026-10-09 (the same 1000-draw sample: 337 of its 548 compared
  -- programs are batched-eligible; 233 non-slow corpus programs declare
  -- `batched`): the corpus uses 56 constructs, the sample reaches 54.
  --
  -- BMapList and BZip OpMult since 2026-10-22, when the batched list map
  -- (merge e9e5759) and categoricalProductFusion's batched declaration
  -- (merge 6287798, batched-refuses-unit-constant) brought them into the batched census. The scalar list carries both for
  -- the typed fuzzer's reasons; the IR generator's batched arm does not
  -- reach them either: its admitted cases hold a list map only inside a
  -- helper body (which the arm does not count), and the interpreter answers
  -- none of its three zipped products at any point. Removed by docs-repo
  -- task batched-fuzz-arms-never-compare-list-map-or-zip-product.
  [ ("Accessor:AcSubtree", "theta trees: the generator emits no ThetaI/Subtree (thetaTree, subtree)")
  , ("Accessor:AcTheta",   "theta trees: the generator emits no ThetaI (gaussianTrajectory4, theta)")
  , ("Builtin:BMapList",   "list map: the typed generator has no higher-order map over a list, and the IR generator's batched cases map a list only in helper bodies (mapMultList)")
  , ("Builtin:BZip OpMult", "agreement fusion: the typed generator never builds two independent categoricals compared with ==, and the interpreter answers none of the IR generator's batched zipped products (categoricalProductFusion)")
  ]

-- | Constructs some corpus config compiles to that the IR fuzz generator has
-- no production for yet, each with the milestone that owns it. Exact, like
-- 'fuzzCoverageExceptions': a construct the generator starts reaching must
-- leave the list.
irGeneratorDeferred :: [(String, String)]
irGeneratorDeferred =
  -- Empty since M4 (generate bodies). Measured 2026-10-13 at M2 (567
  -- programs x 8 configs): the corpus used 68 constructs in its
  -- deterministic bodies, the generator reached all but BIndex, BListIndex,
  -- BMapList, BZip (given productions in M3), IRSample and Sample:IRNormal
  -- (M4). Since M4 the corpus side counts generate bodies too.
  []

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
  -- The batched arm's constructs, shared the same way by the two batched cases.
  bcache <- newMVar Nothing
  let batchedSample = modifyMVar bcache $ \c -> case c of
        Just cs -> return (c, cs)
        Nothing -> do
          cs <- batchedFuzzConstructs sample
          return (Just cs, cs)
  return $ testGroup "BackendAgreementCoverage"
    [ testCase "corpus constructs the agreement fuzzer misses are exactly fuzzCoverageExceptions" $ do
        corpus <- corpusConstructs es
        fuzz <- fuzzConstructs sample
        checkExceptions "scalar" "fuzzCoverageExceptions" "deterministic bodies" Nothing maskedConstruct corpus fuzz fuzzCoverageExceptions
    , testCase "batched corpus constructs the agreement fuzzers miss are exactly batchedFuzzCoverageExceptions" $ do
        corpus <- corpusConstructsWith (defaultCompilerConfig { batched = True }) inferenceBodies
                    [ e | e <- es, Batched `elem` ceBackends e ]
        fuzz <- batchedSample
        ir <- irGeneratorBatchedConstructs
        checkExceptions "batched" "batchedFuzzCoverageExceptions" "the batched-compiled inference bodies of `batched`-declaring programs," Nothing maskedConstruct corpus (ir : fuzz) batchedFuzzCoverageExceptions
    , testCase "batchedCertifiedConstructs is exactly what the two batched arms reach" $ do
        -- Batched reference compliance (CertifiedCensus): a `batched`
        -- corpus program whose batched census lies in this list has no
        -- batched-vs-expected check.
        fuzz <- batchedSample
        ir <- irGeneratorBatchedConstructs
        -- A construct reached only by cases failing as a filed family is
        -- listed in batchedReachedNotCompared instead.
        let reached = sort (filter (not . maskedConstruct) (nub (concat (ir : fuzz))))
            notCompared = map fst batchedReachedNotCompared
            listed = sort (nub (batchedCertifiedConstructs ++ notCompared))
            missing = reached \\ listed
            stale = listed \\ reached
            both = filter (`elem` notCompared) batchedCertifiedConstructs
        hPutStrLn stderr ("batched arms: the typed fuzzer's sample reaches " ++ show (length (nub (concat fuzz)))
                          ++ " constructs, the IR generator's " ++ show (length ir) ++ ", together " ++ show (length reached))
        if null missing && null stale && null both then return () else assertFailure $ unlines $
          [ "batchedCertifiedConstructs (with batchedReachedNotCompared) is out of date." ]
          ++ (if null missing then [] else "Reached by a batched arm, not listed (add them):" : map ("  " ++) missing)
          ++ (if null stale then [] else "Listed, but no batched arm reaches them any more (remove them):" : map ("  " ++) stale)
          ++ (if null both then [] else "In both lists (a certified construct is compared):" : map ("  " ++) both)
    ]

-- | The compiler configs the corpus checks a program under (default, log
-- space, the plan engine at materialization budget 0 in both spaces, branch
-- counting, topK in both spaces, the unoptimized pipeline). Each emits
-- different IR. Not part of the certified census (IR fuzz generator M5); the
-- guard that the IR generator reaches everything the compiler emits under any
-- of them, so that no config can emit an uncertifiable construct.
generatorGuardConfigs :: [(String, CompilerConfig)]
generatorGuardConfigs =
  [ ("default", defaultCompilerConfig)
  , ("log space", defaultCompilerConfig { logSpace = True })
  , ("budget 0", defaultCompilerConfig { materializationCardinality = 0 })
  , ("budget 0, log space", defaultCompilerConfig { materializationCardinality = 0, logSpace = True })
  , ("branch counts", defaultCompilerConfig { countBranches = True })
  , ("topK", defaultCompilerConfig { topKThreshold = Just 0.05 })
  , ("topK, log space", defaultCompilerConfig { topKThreshold = Just 0.05, logSpace = True })
  , ("-O0", defaultCompilerConfig { optimizerLevel = 0 })
  ]

-- | The IR fuzz generator's census (docs-repo design @ir-fuzz-generator@):
-- the constructs every body (generate included, since M4) of the whole corpus (bar the
-- programs slow for their own compile cost) compile to under any of
-- 'generatorGuardConfigs', that the generator's fixed-seed sample
-- ('IRFuzz.irGeneratorConstructs') does not reach, are exactly
-- 'irGeneratorDeferred'.
irGeneratorCoverageTests :: Corpus -> IO TestTree
irGeneratorCoverageTests corpusIn = corpusSweepAll corpusIn SweepSpec
  { sweepName = "Slow.IRGeneratorCoverage", sweepTier = Slow, sweepSlow = IgnoreSlow
  , sweepSelect = notSlowForCompileCost
  , sweepNote = "the constructs the corpus compiles to under any corpus config and the IR fuzz generator never draws are listed" } $ \es ->
  return $ testGroup "IRGeneratorCoverage" $
  [ testCase "certifiedConstructs is exactly what the IR generator reaches" $ do
      -- M2 of impact analysis (CertifiedCensus): a corpus program whose
      -- census lies in this list has no per-program Python or Julia check.
      let reached = sort (nub irGeneratorConstructs)
          listed = sort (nub certifiedConstructs)
          missing = reached \\ listed
          stale = listed \\ reached
      if null missing && null stale then return () else assertFailure $ unlines $
        [ "certifiedConstructs is out of date." ]
        ++ (if null missing then [] else "Reached by the IR generator, not listed (add them):" : map ("  " ++) missing)
        ++ (if null stale then [] else "Listed, but the IR generator no longer reaches them (remove them):" : map ("  " ++) stale)
  , testCase "corpus constructs under every corpus config the IR generator misses are exactly irGeneratorDeferred" $ do
      perConfig <- forM generatorGuardConfigs $ \(cname, conf) -> do
        cs <- corpusConstructsWith conf allBodies es
        return [ (n ++ " [" ++ cname ++ "]", c) | (n, c) <- cs ]
      -- No construct is masked here: the IR generator compares its draws
      -- (generate bodies, by replay), where the typed fuzzer does not.
      checkExceptions "IR generator" "irGeneratorDeferred" "every body under every corpus config"
        (Just "IRFuzz's fixed-seed sample") (const False) (concat perConfig) [irGeneratorConstructs] irGeneratorDeferred
  ]

-- | The census verdict: the constructs the corpus uses and the fuzz sample
-- does not must be exactly @listed@.
checkExceptions :: String -> String -> String -> Maybe String -> (String -> Bool) -> [(String, [String])] -> [[String]] -> [(String, String)] -> IO ()
checkExceptions arm listName what sampleDesc masked corpus fuzz exceptions = do
  let fuzzSet = filter (not . masked) (nub (concat fuzz))
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
                    ++ " programs; the fuzz sample ("
                    ++ fromMaybe (show (length fuzz) ++ " compared of " ++ show coverageDraws ++ " drawn") sampleDesc
                    ++ ") covers " ++ show (length (used \\ uncovered))
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
  primary <- rights <$> mapM prepareAgreementCase draws
  -- As 'prop_Fuzz_BackendsAgree' does: a parameterised main is also compared
  -- at an off-support neighbour of its argument.
  neighbours <- rights . catMaybes <$> mapM prepareAgreementNeighbour draws
  return (primary ++ neighbours)

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
