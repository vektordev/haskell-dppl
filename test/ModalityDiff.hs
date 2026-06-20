{-# LANGUAGE ScopedTypeVariables #-}

-- | Milestone 0 of the modality port (design @modality-typesystem-port@): a
-- THROWAWAY diff harness comparing two pType-producing engines node-by-node
-- across every program in @testCases/@.
--
-- == Why this exists
--
-- The cut-over from 'SPLL.Typing.PInfer2' to the new modality engine
-- (milestone 4/5) is a /replacement/, not a parallel run. The go/no-go data is
-- a per-node @pType@ divergence report of the new engine against the current
-- 'PInfer2', built BEFORE 'PInfer2' is deleted. This module is that report's
-- machinery.
--
-- == Status while stubbed (no engine yet)
--
-- The new engine does not exist until milestone 4, so the /candidate/ side is
-- currently wired to 'PInfer2' itself ('candidateEngine' == 'baselineEngine').
-- That makes the self-diff empty by construction — which is exactly the point:
-- it proves the walk / extract / compare / report machinery is sound, so that
-- when milestone 4 repoints 'candidateEngine' at the modality engine the only
-- moving part is the engine. The two plug points are marked PLUG (MILESTONE 4)
-- below.
--
-- == Throwaway
--
-- Delete this module (and its @other-modules@ entry + the @Spec.hs@ wiring) at
-- cut-over, once the divergence report has been reconciled
-- (see @modality-cutover-delete-pinfer2@).
module ModalityDiff (modalityDiffTests) where

import Control.Exception (try, evaluate, SomeException)
import Data.List (intercalate)
import System.IO (writeFile)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool)

import SPLL.Lang.Types (Program(..), Expr, TypeInfo(..), CompilerError)
import SPLL.Lang.Lang (getTypeInfo, getSubExprs)
import SPLL.Typing.PType (PType(..))
import SPLL.Typing.Modality
  ( Mod, outerGround, GroundMod(..), CapabilitySet(..) )

import SPLL.Analysis (annotateEnumsProg)
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Typing.Infer (addTypeInfo)

import TestCaseParser (parseProgram)
import End2EndTesting (getAllTestFiles)

-- ---------------------------------------------------------------------------
-- Node identity
-- ---------------------------------------------------------------------------

-- | A stable, human-readable address for a node: the top-level function name
-- followed by the child-index path from its body (e.g. @"main/0/2"@). Because
-- the baseline and candidate engines type the /same/ structural program, paths
-- align exactly and so can key the comparison.
type Path = String

-- | Pre-order @(path, pType)@ for every node of a typed program.
nodePTypes :: Program -> [(Path, PType)]
nodePTypes prog = concatMap (\(fname, body) -> walk fname body) (functions prog)
  where
    walk :: Path -> Expr -> [(Path, PType)]
    walk path e =
      (path, pType (getTypeInfo e))
        : concat [ walk (path ++ "/" ++ show i) c
                 | (i, c) <- zip [(0 :: Int) ..] (getSubExprs e) ]

-- ---------------------------------------------------------------------------
-- Engines
-- ---------------------------------------------------------------------------

-- | A pType-producing engine: the stages up to (and including) the inference
-- under test, projected to a per-node @pType@ list. 'Left' on a typing error.
type Engine = Program -> Either CompilerError [(Path, PType)]

-- | The pipeline stages that run before the inference under test:
-- enum annotation, forward chaining (chain names), then RType inference.
preInference :: Program -> Program
preInference = annotateProg . annotateEnumsProg

-- | Baseline: the current 'PInfer2' (via 'addTypeInfo', which is RInfer then
-- @addPTypeInfo@), projected to per-node pTypes.
baselineEngine :: Engine
baselineEngine prog = nodePTypes <$> addTypeInfo (preInference prog)

-- | Candidate. PLUG (MILESTONE 4): repoint this at the new modality engine
-- (build a 'Mod' per node, then 'projectMod'). Stubbed to 'baselineEngine' for
-- now so the self-diff is empty and the machinery is exercised.
candidateEngine :: Engine
candidateEngine = baselineEngine

-- | The candidate engine's /internal/ structured 'Mod' per node, used only for
-- the partial-capability-set flag below. PLUG (MILESTONE 4): repoint at the new
-- engine's internal 'Mod' map. Empty while the candidate is the 'PType'-only
-- 'PInfer2' stub (a flat 'PType' carries no 'Mod').
candidateMods :: Program -> [(Path, Mod)]
candidateMods _ = []

-- ---------------------------------------------------------------------------
-- Diff
-- ---------------------------------------------------------------------------

-- | A node where the two engines disagree.
data Divergence = Divergence
  { divPath     :: Path
  , divBaseline :: PType
  , divCandidate :: PType
  } deriving (Eq, Show)

-- | Node-by-node comparison of two engines on one program. Paths are expected
-- to align (identical structure); a path present in only one side is itself a
-- divergence (rendered with 'NotSetYet' for the missing side).
diffEngines :: Engine -> Engine -> Program -> Either CompilerError [Divergence]
diffEngines baseE candE prog = do
  base <- baseE prog
  cand <- candE prog
  let candMap = cand
      lookupCand p = maybe NotSetYet id (lookup p candMap)
      basePaths = map fst base
      -- baseline-keyed comparison
      cmp = [ Divergence p pt (lookupCand p)
            | (p, pt) <- base, lookupCand p /= pt ]
      -- candidate nodes with no baseline counterpart
      orphan = [ Divergence p NotSetYet pt
               | (p, pt) <- cand, p `notElem` basePaths ]
  return (cmp ++ orphan)

-- | Design §6 holds the partial capability sets @{S,D}@ and @{S,I}@ unreachable
-- (they project to 'Bottom'). Their occurrence would falsify that assumption,
-- so the harness flags any candidate node whose internal /outer/ 'GroundMod'
-- lands in one. Inactive (always empty) while 'candidateMods' is the stub.
partialSetFlags :: Program -> [(Path, CapabilitySet)]
partialSetFlags prog =
  [ (p, gCap g)
  | (p, m) <- candidateMods prog
  , let g = outerGround m
  , gCap g `elem` [DensityOnly, IntegralOnly] ]

-- ---------------------------------------------------------------------------
-- Report
-- ---------------------------------------------------------------------------

-- | Outcome of running the harness on one program.
data ProgReport = ProgReport
  { prFile        :: FilePath
  , prNodeCount   :: Int
  , prDivergences :: [Divergence]
  , prPartials    :: [(Path, CapabilitySet)]
  , prError       :: Maybe String   -- ^ typing failed / threw on this program
  }

runOne :: (FilePath, Program) -> IO ProgReport
runOne (file, prog) = do
  res <- try (evaluate (force (diffEngines baselineEngine candidateEngine prog)))
  case res of
    Left (e :: SomeException) ->
      return (ProgReport file 0 [] [] (Just (show e)))
    Right (Left cErr) ->
      return (ProgReport file 0 [] [] (Just (show cErr)))
    Right (Right divs) -> do
      nodes <- countNodes prog
      return (ProgReport file nodes divs (partialSetFlags prog) Nothing)
  where
    -- force the divergence list (and any lazy typing error inside it)
    force x = case x of
      Left cErr   -> cErr `seq` x
      Right divs  -> length (show divs) `seq` x

countNodes :: Program -> IO Int
countNodes prog = do
  r <- try (evaluate (length (baselineSafe prog))) :: IO (Either SomeException Int)
  return (either (const 0) id r)
  where baselineSafe p = either (const []) id (baselineEngine p)

renderReport :: [ProgReport] -> String
renderReport reports = unlines $
  [ "# Modality diff harness report (milestone 0)"
  , "# candidate == PInfer2 stub; self-diff MUST be empty until milestone 4 repoints it."
  , "# programs: " ++ show (length reports)
      ++ "   typed-ok: " ++ show (length ok)
      ++ "   errored: " ++ show (length errored)
  , "# total nodes compared: " ++ show (sum (map prNodeCount ok))
  , "# total divergences: " ++ show (sum (map (length . prDivergences) ok))
  , "# total partial-set {S,D}/{S,I} flags: " ++ show (sum (map (length . prPartials) ok))
  , ""
  , "## Per-program summary"
  ]
  ++ map summaryLine reports
  ++ [ "", "## Divergences (path | baseline | candidate)" ]
  ++ concatMap divBlock ok
  ++ [ "", "## Partial-set flags (path | set) — design §6 unreachable" ]
  ++ concatMap partialBlock ok
  where
    ok      = [ r | r <- reports, prError r == Nothing ]
    errored = [ r | r <- reports, prError r /= Nothing ]
    summaryLine r = case prError r of
      Just e  -> "  ERR   " ++ prFile r ++ "  (" ++ firstLine e ++ ")"
      Nothing -> "  ok    " ++ prFile r
                   ++ "  nodes=" ++ show (prNodeCount r)
                   ++ "  diffs=" ++ show (length (prDivergences r))
                   ++ "  partial=" ++ show (length (prPartials r))
    divBlock r
      | null (prDivergences r) = []
      | otherwise =
          ("  " ++ prFile r ++ ":")
            : [ "    " ++ divPath d ++ " | " ++ show (divBaseline d)
                  ++ " | " ++ show (divCandidate d)
              | d <- prDivergences r ]
    partialBlock r
      | null (prPartials r) = []
      | otherwise =
          ("  " ++ prFile r ++ ":")
            : [ "    " ++ p ++ " | " ++ show s | (p, s) <- prPartials r ]
    firstLine = takeWhile (/= '\n')

reportPath :: FilePath
reportPath = "/tmp/modality-diff.txt"

-- ---------------------------------------------------------------------------
-- Test entry
-- ---------------------------------------------------------------------------

-- | Loads every @testCases/@ program, runs the harness, writes the full
-- per-node report to 'reportPath', and asserts the self-diff is empty (the
-- machinery sanity check while the candidate is the 'PInfer2' stub).
modalityDiffTests :: IO TestTree
modalityDiffTests = do
  files <- getAllTestFiles
  progs <- mapM (\(ppl, _tst) -> (,) ppl <$> parseProgram ppl) files
  reports <- mapM runOne progs
  writeFile reportPath (renderReport reports)
  let totalDivs = sum (map (length . prDivergences) reports)
      offenders = [ prFile r | r <- reports, not (null (prDivergences r)) ]
  return $ testGroup "ModalityDiff"
    [ testCase "self-diff is empty (candidate == PInfer2 stub)" $
        assertBool
          ( "Expected 0 divergences while candidate == baseline, got "
              ++ show totalDivs ++ " across "
              ++ show (length offenders) ++ " programs: "
              ++ intercalate ", " offenders
              ++ ". Full report: " ++ reportPath )
          (totalDivs == 0)
    , testCase "report written" $
        assertBool ("report at " ++ reportPath) True
    ]
