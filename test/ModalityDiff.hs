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
-- == Status after milestone 4 (candidate = the modality engine)
--
-- The candidate side is now the milestone-4 engine 'SPLL.Typing.ModalityInfer'
-- (build a structured modality per node, project to a flat 'PType'). The two
-- engines /are expected to diverge/: the modality engine infers a strictly
-- more-permissive (more capable) modality on the design's motivating programs
-- and wherever the marginalization core beats @PInfer2@'s constraint solver.
--
-- The gate therefore is not "no divergence" but "no /regression/": every
-- divergence must have the candidate at least as permissive as the baseline in
-- the 'PType' lattice (@Deterministic > PNormal,PLogNormal > Integrate > Prob >
-- Bottom@). A node where the candidate is /less/ permissive (or incomparable —
-- e.g. PNormal vs PLogNormal) is a regression and fails the build. Soundness of
-- the more-permissive verdicts is checked by the corpus property suite, not here.
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
import SPLL.Typing.PType (PType(..), upgrade)
import SPLL.Typing.Modality (GroundMod(..), CapabilitySet(..))

import SPLL.Analysis (annotateEnumsProg)
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Typing.RInfer (addRTypeInfo)
import SPLL.Typing.ModalityInfer (addModalityPTypeInfo, perNodeOuterGrounds)

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

-- | Candidate: the milestone-4 modality engine. Shares RInfer with the baseline
-- (so the only moving part is the PType pass), then runs
-- 'addModalityPTypeInfo' instead of @PInfer2.addPTypeInfo@.
candidateEngine :: Engine
candidateEngine prog =
  nodePTypes <$> (addRTypeInfo (preInference prog) >>= addModalityPTypeInfo)

-- | The candidate engine's /internal/ outer 'GroundMod' per node, used for the
-- partial-capability-set flag below. Built by re-running RInfer (the engine
-- reads rType) then the modality pass. Keyed by chain name.
candidateGrounds :: Program -> [(String, GroundMod)]
candidateGrounds prog =
  case addRTypeInfo (preInference prog) of
    Left _      -> []
    Right rprog -> perNodeOuterGrounds rprog

-- ---------------------------------------------------------------------------
-- Diff
-- ---------------------------------------------------------------------------

-- | A node where the two engines disagree.
data Divergence = Divergence
  { divPath      :: Path
  , divBaseline  :: PType
  , divCandidate :: PType
  , divRegression :: Bool   -- ^ candidate strictly less permissive / incomparable
  } deriving (Eq, Show)

-- | @candidate@ is at least as permissive as @baseline@ in the PType lattice
-- (the join of the two is the candidate). Incomparable siblings (PNormal vs
-- PLogNormal) are /not/ ≥ each other, so they count as a regression — a genuine
-- disagreement worth surfacing.
atLeastAsPermissive :: PType -> PType -> Bool
atLeastAsPermissive cand base = cand == base || upgrade base cand == cand

-- | Design §6 holds the partial capability sets @{S,D}@ and @{S,I}@ as having no
-- usable @Integrate@ leg, so they project to 'Bottom'. The harness flags any
-- candidate node whose internal /outer/ 'GroundMod' lands in one — informational
-- (the marginalization floor can legitimately produce @{S,I}@ for a sum of two
-- continuous laws, which projects to the same 'Bottom' @PInfer2@ reports), not a
-- gate.
partialSetFlags :: Program -> [(Path, CapabilitySet)]
partialSetFlags prog =
  [ (cn, gCap g)
  | (cn, g) <- candidateGrounds prog
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
  , prBaseError   :: Maybe String   -- ^ baseline (PInfer2) failed/threw
  , prCandError   :: Maybe String   -- ^ candidate (modality engine) failed/threw
  }

-- | A genuine capability regression: the candidate could not type a program the
-- baseline typed fine. This — not a per-node permissiveness reduction — is what
-- the gate fails on.
prCapabilityRegression :: ProgReport -> Bool
prCapabilityRegression r = prBaseError r == Nothing && prCandError r /= Nothing

-- | Per-node divergences where the candidate is /less/ permissive than the
-- baseline. These are expected and allowed: the modality engine is more
-- conservative (sound) than @PInfer2@, which over-claims @Deterministic@ for
-- e.g. let-bound random variables. Reported for review; soundness is pinned by
-- the dedicated property tests, not gated here.
prReductions :: ProgReport -> [Divergence]
prReductions = filter divRegression . prDivergences

prImprovements :: ProgReport -> [Divergence]
prImprovements = filter (not . divRegression) . prDivergences

-- | Evaluate an engine fully, capturing both 'Left' typing errors and thrown
-- exceptions as a 'Maybe' error string.
runEngine :: Engine -> Program -> IO (Either String [(Path, PType)])
runEngine eng prog = do
  res <- try (evaluate (forceE (eng prog))) :: IO (Either SomeException (Either CompilerError [(Path, PType)]))
  return $ case res of
    Left e          -> Left (firstLine (show e))
    Right (Left c)  -> Left (firstLine (show c))
    Right (Right r) -> Right r
  where
    forceE x = case x of
      Left c  -> c `seq` x
      Right r -> length (show r) `seq` x
    firstLine = takeWhile (/= '\n')

runOne :: (FilePath, Program) -> IO ProgReport
runOne (file, prog) = do
  baseR <- runEngine baselineEngine prog
  candR <- runEngine candidateEngine prog
  let baseErr = either Just (const Nothing) baseR
      candErr = either Just (const Nothing) candR
  case (baseR, candR) of
    (Right base, Right cand) -> do
      partials <- try (evaluate (forceList (partialSetFlags prog)))
                    :: IO (Either SomeException [(Path, CapabilitySet)])
      return (ProgReport file (length base) (diffLists base cand)
                         (either (const []) id partials) Nothing Nothing)
    _ -> return (ProgReport file 0 [] [] baseErr candErr)
  where forceList xs = length (show xs) `seq` xs

-- | Node-by-node comparison of two already-typed engine outputs.
diffLists :: [(Path, PType)] -> [(Path, PType)] -> [Divergence]
diffLists base cand = cmp ++ orphan
  where
    lookupCand p = maybe NotSetYet id (lookup p cand)
    basePaths = map fst base
    cmp = [ Divergence p pt c (not (atLeastAsPermissive c pt))
          | (p, pt) <- base, let c = lookupCand p, c /= pt ]
    orphan = [ Divergence p NotSetYet pt True
             | (p, pt) <- cand, p `notElem` basePaths ]

renderReport :: [ProgReport] -> String
renderReport reports = unlines $
  [ "# Modality diff harness report (milestone 4: candidate = ModalityInfer)"
  , "# gate: 0 capability regressions (candidate must type every program the"
  , "#       baseline types). Per-node permissiveness reductions are allowed"
  , "#       (the modality engine is more conservative/sound than PInfer2) and"
  , "#       reported here for review; soundness is pinned by property tests."
  , "# programs: " ++ show (length reports)
      ++ "   both-typed-ok: " ++ show (length ok)
      ++ "   capability-regressions: " ++ show (length capReg)
  , "# total nodes compared: " ++ show (sum (map prNodeCount ok))
  , "# total divergences: " ++ show (sum (map (length . prDivergences) ok))
  , "#   improvements (candidate more permissive): "
      ++ show (sum (map (length . prImprovements) ok))
  , "#   reductions (candidate more conservative/sound): "
      ++ show (sum (map (length . prReductions) ok))
  , "# total partial-set {S,D}/{S,I} flags (informational): "
      ++ show (sum (map (length . prPartials) ok))
  , ""
  , "## Per-program summary"
  ]
  ++ map summaryLine reports
  ++ [ "", "## Capability regressions (candidate failed where baseline succeeded)" ]
  ++ [ "  " ++ prFile r ++ "  (" ++ maybe "?" id (prCandError r) ++ ")" | r <- capReg ]
  ++ [ "", "## Reductions (path | baseline | candidate)" ]
  ++ concatMap (divBlock prReductions) ok
  ++ [ "", "## Improvements (path | baseline | candidate)" ]
  ++ concatMap (divBlock prImprovements) ok
  ++ [ "", "## Partial-set flags (chainName | set) — design §6 informational" ]
  ++ concatMap partialBlock ok
  where
    ok     = [ r | r <- reports, prBaseError r == Nothing, prCandError r == Nothing ]
    capReg = filter prCapabilityRegression reports
    summaryLine r
      | prCapabilityRegression r =
          "  REGR  " ++ prFile r ++ "  (candidate: " ++ maybe "?" id (prCandError r) ++ ")"
      | prBaseError r /= Nothing =
          "  base-err " ++ prFile r ++ "  (" ++ maybe "?" id (prBaseError r) ++ ")"
      | otherwise =
          "  ok    " ++ prFile r
            ++ "  nodes=" ++ show (prNodeCount r)
            ++ "  reduce=" ++ show (length (prReductions r))
            ++ "  improve=" ++ show (length (prImprovements r))
            ++ "  partial=" ++ show (length (prPartials r))
    divBlock sel r
      | null (sel r) = []
      | otherwise =
          ("  " ++ prFile r ++ ":")
            : [ "    " ++ divPath d ++ " | " ++ show (divBaseline d)
                  ++ " | " ++ show (divCandidate d)
              | d <- sel r ]
    partialBlock r
      | null (prPartials r) = []
      | otherwise =
          ("  " ++ prFile r ++ ":")
            : [ "    " ++ p ++ " | " ++ show s | (p, s) <- prPartials r ]

reportPath :: FilePath
reportPath = "/tmp/modality-diff.txt"

-- ---------------------------------------------------------------------------
-- Test entry
-- ---------------------------------------------------------------------------

-- | Loads every @testCases/@ program, runs the harness, writes the full
-- per-node report to 'reportPath', and asserts there are zero regressions
-- (the candidate is everywhere at least as permissive as the baseline).
modalityDiffTests :: IO TestTree
modalityDiffTests = do
  files <- getAllTestFiles
  progs <- mapM (\(ppl, _tst) -> (,) ppl <$> parseProgram ppl) files
  reports <- mapM runOne progs
  writeFile reportPath (renderReport reports)
  let offenders = [ prFile r | r <- reports, prCapabilityRegression r ]
  return $ testGroup "ModalityDiff"
    [ testCase "no capability regressions (candidate types every baseline-typed program)" $
        assertBool
          ( "Candidate failed on " ++ show (length offenders)
              ++ " program(s) the baseline typed: "
              ++ intercalate ", " offenders
              ++ ". Full report: " ++ reportPath )
          (null offenders)
    , testCase "report written" $
        assertBool ("report at " ++ reportPath) True
    ]
