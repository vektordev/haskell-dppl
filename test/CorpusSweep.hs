{-# LANGUAGE ScopedTypeVariables #-}
-- | The registry of whole-corpus sweeps (docs-repo task corpus-sweep-registry):
-- every check that iterates over the programs of @test/cases/@ is built here,
-- through 'corpusSweep' or 'corpusSweepAll', from a 'SweepSpec' that names it,
-- tiers it and selects its programs.
--
-- The suite costs roughly (corpus programs) x (sweeps), and a sweep written as
-- a hand-rolled loop looks as cheap as a unit test. Routing every sweep
-- through one combinator buys three things:
--
-- * Tiering in one place. A sweep's 'Tier' decides which environment variable
--   it needs; a sweep whose tier is off builds an empty group. The @.tst@
--   @slow@ header is applied here too, by each spec's 'SlowHeader' policy.
-- * Cost reporting. Every test of a sweep runs under a clock, and
--   'reportSweeps' prints one line per sweep after the run: tier, programs,
--   tests run, build time (the 'IO' that built the tree, e.g. batched
--   eligibility) and the summed run time of its tests.
-- * Visibility. A new sweep is a new @SweepSpec {@ value, and the bypass
--   check in "TestInternals" fails if a corpus loader ('getAllTestFiles',
--   'TestCaseParser.listCorpusPplFiles') is called anywhere else.
--
-- The corpus is loaded once per test binary ('loadCorpus') and shared by every
-- sweep. It holds the parsed programs and the raw @.tst@ rows; what a sweep
-- derives from them (compiles, mock-shaped rows) is the sweep's own business.
module CorpusSweep
  ( Tier(..)
  , SlowHeader(..)
  , SweepSpec(..)
  , CorpusEntry(..)
  , Corpus
  , corpusEntries
  , loadCorpus
  , corpusSweep
  , corpusSweepAll
  , timeWholeRun
  , reportSweeps
  , sweepLoaderNames
  ) where

import Control.Exception (evaluate, finally)
import Control.Monad (forM, when)
import Data.IORef
import Data.List (intercalate, sortOn)
import Data.Maybe (fromJust, isJust)
import Data.Tagged (Tagged, retag)
import GHC.Clock (getMonotonicTime)
import System.Environment (lookupEnv)
import System.FilePath (stripExtension, takeBaseName)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Options (OptionDescription)
import Test.Tasty.Providers (IsTest(..))
import Test.Tasty.Runners (TestTree(..))
import Text.Printf (printf)

import SPLL.Lang.Types (Program)
import TestCaseParser (Backend, ExpectFailure, TestCase, parseProgram, parseTestCases, listCorpusPplFiles)

-- | Which run a sweep belongs to (docs/testing.md, "Slow and Aspirational
-- tests"). 'Default' always builds; 'Slow' needs @NEST_SLOW_TESTS@ and
-- 'Aspirational' @NEST_ASPIRATIONAL_TESTS@.
data Tier = Default | Slow | Aspirational
  deriving (Eq, Show)

-- | How a sweep treats a program whose @.tst@ carries the @slow@ header.
-- 'SkipSlow' leaves it out (the usual policy: those programs are slow to
-- compile or run); 'OnlySlow' takes nothing else (the slow twins of the
-- End2End groups); 'IgnoreSlow' takes it like any other, for static checks that
-- neither compile nor run the program.
data SlowHeader = SkipSlow | OnlySlow | IgnoreSlow
  deriving (Eq, Show)

data SweepSpec = SweepSpec
  { sweepName   :: String
    -- ^ The sweep's path as @--ta '-l'@ prints it, without the main binary's
    -- @Tests.@ root (e.g. @End2End.Interpreter@, @Corpus.ValidPrograms@). Its
    -- last component is the tasty name of the sweep's node, group or single
    -- test, so no component may contain a @.@.
  , sweepTier   :: Tier
  , sweepSlow   :: SlowHeader
  , sweepSelect :: CorpusEntry -> Bool
    -- ^ Routing and eligibility, applied after 'sweepSlow'.
  , sweepNote   :: String
    -- ^ One line: what it checks, and why per program.
  }

-- | One corpus program: its @.ppl@ parsed, its @.tst@ parsed but unshaped
-- (End2EndTesting's 'End2EndTesting.shapeNeuralTestCase' is per sweep).
data CorpusEntry = CorpusEntry
  { ceName          :: String      -- ^ base name, unique across the corpus
  , cePpl           :: FilePath
  , ceTst           :: FilePath
  , ceProgram       :: Program
  , ceBackends      :: [Backend]
  , ceSlow          :: Bool
  , ceExpectFailure :: Maybe ExpectFailure
  , ceCases         :: [TestCase]
  }

-- | Time and count accumulated by the tests under one clock.
type Clock = IORef (Int, Double)

data SweepRecord = SweepRecord
  { srSpec     :: SweepSpec
  , srEnabled  :: Bool
  , srPrograms :: Int
  , srBuild    :: Double
  , srClock    :: Clock
  }

data Corpus = Corpus
  { corpusEntries  :: [CorpusEntry]
  , corpusRegistry :: IORef [SweepRecord]
  , corpusTotal    :: Clock
  }

-- | The loader names the bypass check looks for outside this module (and
-- outside "TestCaseParser", which defines 'listCorpusPplFiles' and resolves
-- single programs by name with it).
sweepLoaderNames :: [String]
sweepLoaderNames = ["getAllTestFiles", "listCorpusPplFiles", "loadEnd2EndCases"]

-- | Every ordinary corpus @.ppl@ with its @.tst@ sibling, in directory-walk
-- order (which the Julia shards' round robin depends on).
getAllTestFiles :: IO [(FilePath, FilePath)]
getAllTestFiles = do
  pplFullPath <- listCorpusPplFiles
  let testCaseFiles = map ((++ ".tst") . (fromJust . stripExtension ".ppl")) pplFullPath
  return (zip pplFullPath testCaseFiles)

-- | Parse the whole corpus, once per test binary.
loadCorpus :: IO Corpus
loadCorpus = do
  files <- getAllTestFiles
  entries <- forM files $ \(ppl, tst) -> do
    prog <- parseProgram ppl
    (bs, slow, ef, tcs) <- parseTestCases tst
    return (CorpusEntry (takeBaseName ppl) ppl tst prog bs slow ef tcs)
  reg <- newIORef []
  total <- newIORef (0, 0)
  return (Corpus entries reg total)

tierEnabled :: Tier -> IO Bool
tierEnabled Default = return True
tierEnabled Slow = isJust <$> lookupEnv "NEST_SLOW_TESTS"
tierEnabled Aspirational = isJust <$> lookupEnv "NEST_ASPIRATIONAL_TESTS"

nodeName :: SweepSpec -> String
nodeName = reverse . takeWhile (/= '.') . reverse . sweepName

selectFor :: SweepSpec -> [CorpusEntry] -> [CorpusEntry]
selectFor spec = filter (\e -> slowOk (ceSlow e) && sweepSelect spec e)
  where
    slowOk slow = case sweepSlow spec of
      SkipSlow   -> not slow
      OnlySlow   -> slow
      IgnoreSlow -> True

-- | A sweep with one tasty node per selected program, grouped under the
-- sweep's node name.
corpusSweep :: Corpus -> SweepSpec -> (CorpusEntry -> TestTree) -> IO TestTree
corpusSweep c spec perProgram =
  corpusSweepAll c spec (return . testGroup (nodeName spec) . map perProgram)

-- | A sweep that builds its node from the whole selected slice at once (a
-- batch, a few aggregate properties, a single test looping over it). The
-- builder's node must carry the sweep's node name.
corpusSweepAll :: Corpus -> SweepSpec -> ([CorpusEntry] -> IO TestTree) -> IO TestTree
corpusSweepAll c spec build = do
  enabled <- tierEnabled (sweepTier spec)
  clock <- newIORef (0, 0)
  if not enabled
    then do
      register (SweepRecord spec False 0 0 clock)
      return (testGroup (nodeName spec) [])
    else do
      t0 <- getMonotonicTime
      let selected = selectFor spec (corpusEntries c)
      n <- evaluate (length selected)
      tree <- build selected
      t1 <- getMonotonicTime
      case rootName tree of
        Just r | r /= nodeName spec ->
          error ("corpusSweepAll: sweep " ++ sweepName spec ++ " built a node named " ++ show r)
        _ -> return ()
      register (SweepRecord spec True n (t1 - t0) clock)
      return (timeTree clock tree)
  where
    register r = atomicModifyIORef' (corpusRegistry c) (\rs -> (r : rs, ()))

rootName :: TestTree -> Maybe String
rootName t = case t of
  SingleTest n _       -> Just n
  TestGroup n _        -> Just n
  PlusTestOptions _ t' -> rootName t'
  _                    -> Nothing

-- | A test that adds its run time to a clock.
data Timed t = Timed Clock t

instance IsTest t => IsTest (Timed t) where
  run opts (Timed clock t) progress = do
    t0 <- getMonotonicTime
    run opts t progress `finally` do
      t1 <- getMonotonicTime
      atomicModifyIORef' clock (\(k, s) -> ((k + 1, s + (t1 - t0)), ()))
  testOptions = retag (testOptions :: Tagged t [OptionDescription])

timeTree :: Clock -> TestTree -> TestTree
timeTree clock = go
  where
    go t = case t of
      SingleTest n test   -> SingleTest n (Timed clock test)
      TestGroup n ts      -> TestGroup n (map go ts)
      PlusTestOptions f u -> PlusTestOptions f (go u)
      WithResource r f    -> WithResource r (go . f)
      AskOptions f        -> AskOptions (go . f)
      After d e u         -> After d e (go u)

-- | Clock every test of the binary's whole tree, so the report can say what
-- share of the run the sweeps are.
timeWholeRun :: Corpus -> TestTree -> TestTree
timeWholeRun c = timeTree (corpusTotal c)

-- | One line per sweep that ran a test, after the tree has run. Times are
-- summed over a sweep's tests, which run in parallel, so they add up to more
-- than the wall time.
reportSweeps :: Corpus -> IO ()
reportSweeps c = do
  recs <- reverse <$> readIORef (corpusRegistry c)
  rows <- forM [ r | r <- recs, srEnabled r ] $ \r -> do
    (k, s) <- readIORef (srClock r)
    return (r, k, s)
  (totalK, totalS) <- readIORef (corpusTotal c)
  let ran = [ row | row@(_, k, _) <- rows, k > 0 ]
      off = [ sweepName (srSpec r) | r <- recs, not (srEnabled r) ]
      sweepS = sum [ s | (_, _, s) <- ran ]
      sweepK = sum [ k | (_, k, _) <- ran ]
  when (not (null ran)) $ do
    putStrLn ("Corpus sweeps -- " ++ show (length ran) ++ " ran"
              ++ (if null off then "" else ", " ++ show (length off) ++ " off (tier not enabled)")
              ++ "; test time is summed over each sweep's tests, which run in parallel")
    putStrLn "  tier          progs  tests  build s   test s  sweep"
    mapM_ (\(r, k, s) -> putStrLn (printf "  %-12s %6d %6d %8.1f %8.1f  %s"
                                    (show (sweepTier (srSpec r))) (srPrograms r) k (srBuild r) s
                                    (sweepName (srSpec r))))
          (sortOn (\(_, _, s) -> negate s) ran)
    putStrLn (printf "  all sweeps: %d tests, %.1f s of the %.1f s summed over all %d tests run (%.0f%%)"
                     sweepK sweepS totalS totalK
                     (if totalS > 0 then 100 * sweepS / totalS else 0 :: Double))
    when (not (null off)) $
      putStrLn ("  off: " ++ intercalate ", " off)
