{-# LANGUAGE PatternSynonyms, ScopedTypeVariables #-}
-- | The rewrite-invariance net (task
-- rewrite-invariance-net-draw-apply-helper-alias; milestone M0 of design
-- law-carrying-modality, M2 of transformation-differential-testing).
--
-- A program and a semantics-preserving rewrite of it ("Rewrites") denote the
-- same distribution, so the compiler owes them the same answers. Each pair is
-- judged by the three-outcome oracle of transformation-differential-testing:
--
-- * both answer: probability and dim must agree -- a hard failure otherwise;
-- * the original answers, the rewrite does not (a graceful refusal, a missing
--   probability function, or a crash): a capability regression, logged, and a
--   hard failure only for a family 'refusalIsHard' has promoted;
-- * the original does not answer, the rewrite does: nothing to compare with,
--   so the answering side is checked against its own forward sampler.
--
-- Log-only outcomes are reported through 'testCaseInfo', so
-- @TASTY_HIDE_SUCCESSES=false@ shows the whole frontier.
--
-- Three groups: @Units@ pins each rewrite's preconditions; @Probes@ runs the
-- ten probe pairs of law-carrying-modality's evidence table, in both
-- directions; @Corpus@ applies every family at every site of every
-- interpreter-routed, non-neural, non-slow corpus program and compares at that
-- program's own @.tst@ query points. A fourth, @OfToggleCompilesIdentically@,
-- toggles neural declarations' @of@ clauses ('ofToggles'; M3 of
-- transformation-differential-testing) and compares the compiles themselves.
module TestRewrites (rewriteTests, rewriteCorpusTests, rewriteSequenceTests, rewriteIntegrationTests, ofToggleCorpusTests) where

import Control.Concurrent (forkIO, getNumCapabilities)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.QSem (newQSem, signalQSem, waitQSem)
import Control.Exception (SomeException, bracket_, evaluate, throwIO, try)
import Control.Monad (forM, replicateM)
import Control.Monad.Random.Lazy (evalRandIO)
import Data.List (intercalate, isInfixOf, isPrefixOf, nub)
import Data.Maybe (isJust, isNothing)
import qualified Data.Set as Set
import System.Timeout (timeout)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, testCaseInfo, assertBool, assertFailure, (@?=))
import Test.QuickCheck (Property, Result(..), Discard(..), stdArgs, quickCheckWithResult, replay, maxSuccess, chatty, maxShrinks,
                        forAllShrinkShow, ioProperty, property, tabulate, counterexample, chooseInt, (==>))
import Test.QuickCheck.Random (mkQCGen)

import SPLL.Lang.Types
import SPLL.Typing.PType (PType(..))
import SPLL.Lang.Lang (freeVarsExpr, getTypeInfo)
import SPLL.IntermediateRepresentation (IREnv, IRValue, pattern VProbDim, pattern VProbDimBC)
import SPLL.CompilerConfig (CompilerConfig(..), defaultCompilerConfig)
import SPLL.Parser (tryParseProgram)
import SPLL.Prelude (compile, compileStages, runProbC, runGenC, rtypedProgram, StageSnapshot(..), StageValue(..))
import TestCaseParser (TestCase(..), Backend(..))
import CorpusSweep
import SPLL.StageDiff (StageDiffOpts(..), StageReport(..), StageRow(Rewrite, Same, Diverges), defaultStageDiffOpts, stageDiff, stageDiffStages, renderStageReport, answersStage)
import TestTolerances (probTolerance, samplingTolerance)
import Rewrites
import ImpactManifest
import End2EndTesting (programRuntimeFields)

-- ---------------------------------------------------------------------------
-- Promotion and known divergences
-- ---------------------------------------------------------------------------

-- | Is "the original answers, the rewrite refuses" a hard failure for this
-- family? All log-only at landing. Each flips in the commit of the
-- law-carrying milestone that claims it, so no milestone can claim a family it
-- does not deliver:
--
-- * 'AliasIntro': was assigned to M1, reinfer-body-under-recovered-bindings,
--   which cut its logged frontier from 75 to 50 but did not close it. What is
--   left is not re-inference's class (a variable's stale type after it is
--   recovered): an alias between a curried function's parameters
--   (@constructEquivalenceClauses@, ~21), tagged or higher-order invocations
--   (~15), an alias of a function parameter handed to the Gaussian catch-all
--   with nothing recovered (2), and a witness seeded through an aliased chain
--   refusing an ANY marginal. Those belong to M2 and M6, so the family stays
--   log-only until the later of the two lands;
-- * 'HelperExtract': M2, binding-resolver-one-application-rule;
-- * 'DrawIntro', 'LinearInline': M6, dispatch-on-law-certificates. Its
--   in-place engine (a binding read once, with no binder on the way, measured
--   at its read) and the set-witness walk's entry into such an inner binding
--   cut the promoted frontier, over the Slow sweep, the probes and the
--   sequences, from 55 failing tests to 35 (at 1a09132). What is left is
--   classified in that task: mostly other milestones' classes (Gaussian
--   rules reading syntax, M7; named callees; point inversion through a
--   deterministic if behind a binding; recursion; ANY-mask runtime refusals;
--   interpreter type errors), so both stay log-only.
refusalIsHard :: Family -> Bool
refusalIsHard AliasIntro = False
refusalIsHard HelperExtract = False
refusalIsHard DrawIntro = False
refusalIsHard LinearInline = False
-- The M3 families of transformation-differential-testing (task
-- transformation-differential-testing-m3-catalog-expansion) enter log-only,
-- as that design's oracle prescribes: no milestone claims their frontier.
refusalIsHard IfFlip = False
refusalIsHard CompareFlip = False
refusalIsHard InjFIdentity = False
refusalIsHard AlphaRename = False
refusalIsHard TupleLaw = False

-- | A divergence where both sides answer and disagree, pinned in
-- @test/cases/known-issues/@ and tracked by the named document. Matched on
-- (program, family, a substring of the site label).
data Known = Known { kProg :: String, kFam :: Family, kSite :: String, kDoc :: String }
  deriving (Eq)

-- | The known divergences. They are reported as log-only; an entry whose
-- program no longer diverges at a matching site fails that program's test, so
-- the list cannot rot. Each tracking document carries the minimal pair.
knownDivergences :: [Known]
knownDivergences =
  -- A structured random value read through a second binder -- an alias, or
  -- a helper's parameter -- loses a field's constraint.
  -- (A helper projecting one field, `h q = fst q` beside `snd e`, is fixed:
  -- task fst-of-pair-wrapper-loses-structured-draw-constraint.) What is left:
  -- an alias, a helper taking the whole tuple (`h e = (fst e, snd e)`), and a
  -- projecting helper behind a second one (`g x = h x`).
  [ Known "drawDestructuredShared" DrawIntro "" structuredReread
  , Known "drawDestructuredShared" AliasIntro "" structuredReread
  , Known "fstOfPairWrapperStructuredDraw" DrawIntro "" structuredReread
  , Known "fstOfPairWrapperStructuredDraw" AliasIntro "" structuredReread
  , Known "fstOfPairWrapperStructuredDraw" HelperExtract "extract (TCons" structuredReread
  , Known "fstOfPairWrapperNestedStructuredDraw" DrawIntro "" structuredReread
  , Known "fstOfPairWrapperNestedStructuredDraw" AliasIntro "" structuredReread
  , Known "fstOfPairWrapperNestedStructuredDraw" HelperExtract "extract (TCons" structuredReread
  , Known "sndOfPairWrapperStructuredDraw" DrawIntro "" structuredReread
  , Known "sndOfPairWrapperStructuredDraw" AliasIntro "" structuredReread
  , Known "sndOfPairWrapperStructuredDraw" HelperExtract "extract (TCons" structuredReread
  , Known "structuredDrawHelperProjectsField" DrawIntro "" structuredReread
  , Known "structuredDrawHelperProjectsField" AliasIntro "" structuredReread
  , Known "structuredDrawHelperProjectsField" HelperExtract "" structuredReread
  -- The swapped wrapper re-read through a second binder: before per-mask
  -- variants the concrete query refused ("binding 'x' is unobserved"); f's
  -- variants now answer the split sub-queries, so p((0.7, 0.6)) is 1.0
  -- instead of impossible.
  , Known "maskSwappedWrapper" DrawIntro "" variantsSilenceReread
  , Known "maskSwappedWrapper" AliasIntro "" variantsSilenceReread
  , Known "maskSwappedWrapper" HelperExtract "" variantsSilenceReread
  -- The M3 families (task transformation-differential-testing-m3-catalog-expansion).
  -- The same impossible (0.7, 0.6) answered 1.0 as the other families above.
  , Known "maskSwappedWrapper" TupleLaw "pair-fst" variantsSilenceReread
  -- `1.0 > NaN` answers p(True) = 1 (the mirrored `NaN < 1.0` is right).
  , Known "nanConstantMixture" CompareFlip "compare-swap" nanComparison
  -- The if-flip's `not` is swapped back into the arms, but a negation behind
  -- a binding, a helper or a projection still reaches the IfThenElse
  -- complement, which drops the equality's density.
  , Known "observeNegatedContinuousEqualsLetfree" DrawIntro "draw-intro (eq Normal 0.5)" hiddenNegation
  , Known "observeNegatedContinuousEqualsLetfree" HelperExtract "extract (not" hiddenNegation
  , Known "observeNegatedContinuousEqualsLetfree" TupleLaw "pair-fst (not" hiddenNegation
  ]
  where
    hiddenNegation = "if-complement-drops-hidden-negation-density"
    nanComparison = "nan-operand-comparison-measured-through-cdf"
    structuredReread = "structured-draw-reread-through-binder-drops-field"
    variantsSilenceReread = "mask-variants-silence-reread-refusal-into-wrong-result"

-- | A divergence only a composition of rewrites reaches, for the sequence
-- property: a sequence on the program whose steps include every family listed
-- is judged known. Each has a known-issues pin and a tracking document, as
-- 'knownDivergences' do. There is no staleness check: a random sequence
-- property cannot show that a divergence is gone.
data KnownSeq = KnownSeq { ksProg :: String, ksFams :: [Family], ksDoc :: String }

knownSequenceDivergences :: [KnownSeq]
knownSequenceDivergences =
  -- `x` read as `1.0 * x`, extracted into a helper beside the `x + 1.0` cell
  -- of the same list: p([0.3, 1.3]) is impossible. Pinned by
  -- known-issues/listHelperReadBesideAffineSibling; reached by seed 20261016
  -- once the null-set-negation corpus additions moved what it draws.
  [ KnownSeq "witnessThroughDetIfNamed" [InjFIdentity, HelperExtract] "list-parameter-helper-read-beside-affine-sibling-impossible"
  -- The parameter aliased, the noise drawn into a binding and `+ 0.0` added:
  -- the (x, ANY) marginal loses the Uniform's dimension. Pinned by
  -- known-issues/aliasedParameterPlusZeroMarginalDim; reached by seed
  -- 20261017 after the same corpus additions.
  , KnownSeq "rewriteProbeHelperScaledNoise" [DrawIntro, InjFIdentity, AliasIntro] "aliased-parameter-plus-zero-marginal-loses-dim"
  -- The same marginal with the parameter aliased twice and no `+ 0.0`.
  -- Pinned by known-issues/aliasedParameterTwiceMarginalDim; reached by seed
  -- 20261015 once the set-witness-walk-stops-at-identity-injf-wrapper corpus
  -- additions moved what it draws.
  , KnownSeq "rewriteProbeHelperScaledNoise" [AliasIntro] "aliased-parameter-plus-zero-marginal-loses-dim" ]

knownDivergence :: String -> Family -> String -> Maybe Known
knownDivergence prog fam site =
  case [k | k <- knownDivergences, kProg k == prog, kFam k == fam, kSite k `isInfixOf` site] of
    (k : _) -> Just k
    [] -> Nothing

-- ---------------------------------------------------------------------------
-- Running a program
-- ---------------------------------------------------------------------------

-- | A query row: the sample and the parameters.
type Query = (IRValue, [IRValue])

-- | What a program did at a list of query points.
data Outcome = Answered [(Double, Int)] | Refused String

-- | Compile at the default config and answer every query. Any failure --
-- a 'Left', a missing probability function, a crash or a timeout -- is
-- 'Refused' with its message; the whole run is one outcome.
runQueries :: Program -> [Query] -> IO Outcome
runQueries p qs = compileTimed p >>= \c -> runCompiled p c qs

-- | A program's default compile, evaluated as far as refusing or not, under a
-- 20 s timeout. 'Left' is the message 'runQueries' reports for a refusal, a
-- crash or a timeout. The environment itself stays lazy, as the queries
-- force it: forcing all of it could crash on a part no query reads.
compileTimed :: Program -> IO (Either String IREnv)
compileTimed = compileTimedWith defaultCompilerConfig

-- | 'compileTimed' under another config.
compileTimedWith :: CompilerConfig -> Program -> IO (Either String IREnv)
compileTimedWith conf p = do
  r <- timedTry (20 * 1000000) (evaluate (compile conf p))
  return $ case r of
    Nothing -> Left "timeout (20s)"
    Just (Left ex) -> Left ("crash: " ++ firstLine (show (ex :: SomeException)))
    Just (Right (Left err)) -> Left ("refused: " ++ shorten (takeWhile (/= '\n') err))
    Just (Right (Right env)) -> Right env

-- | Answer every query on a compile from 'compileTimed', under a 20 s timeout.
runCompiled :: Program -> Either String IREnv -> [Query] -> IO Outcome
runCompiled _ (Left why) _ = return (Refused why)
runCompiled p (Right env) qs = do
  r <- timedTry (20 * 1000000) (evaluate (forceOutcome (answer p env qs)))
  return $ case r of
    Nothing -> Refused "timeout (20s)"
    Just (Left ex) -> Refused ("crash: " ++ firstLine (show (ex :: SomeException)))
    Just (Right o) -> o

-- | 'timeout' around 'try', the other way round: an action run as
-- @timeout n (try act)@ catches 'timeout''s own exception, so a timeout came
-- back as @Just (Left <<timeout>>)@, a crash, and was keyed and judged as one.
-- 'Nothing' is a timeout; 'Just' the action's result or its exception.
timedTry :: Int -> IO a -> IO (Maybe (Either SomeException a))
timedTry n act = do
  r <- try (timeout n act)
  return $ case r of
    Left ex -> Just (Left ex)
    Right Nothing -> Nothing
    Right (Just x) -> Just (Right x)

firstLine :: String -> String
firstLine = shorten . takeWhile (/= '\n')

-- | Crash messages can carry a whole annotated AST; a log line needs the
-- diagnostic, not the dump.
shorten :: String -> String
shorten m = if length m > 160 then take 160 m ++ "..." else m

answer :: Program -> IREnv -> [Query] -> Outcome
answer p env qs = either (Refused . ("refused: " ++) . shorten . takeWhile (/= '\n')) Answered
                    (mapM (\(s, params) -> runProbC p env params s >>= probDim) qs)
  where
    probDim (VProbDim pr d) = Right (pr, d)
    probDim v = Left ("not a probability result: " ++ show v)

forceOutcome :: Outcome -> Outcome
forceOutcome o@(Answered xs) = sum (map (\(a, b) -> a + fromIntegral b) xs) `seq` o
forceOutcome o@(Refused m) = length m `seq` o

-- | Do two answers agree? Probability within 'probTolerance' (relative above
-- 1, since densities can be large), dim exactly -- unless both are zero, where
-- the dim carries no information. Two NaNs agree with each other only.
agrees :: (Double, Int) -> (Double, Int) -> Bool
agrees (p1, d1) (p2, d2)
  | isNaN p1 || isNaN p2 = isNaN p1 && isNaN p2 && d1 == d2
  | p1 == 0 && p2 == 0 = True
  | otherwise = abs (p1 - p2) <= probTolerance * max 1 (abs p1) && d1 == d2

-- ---------------------------------------------------------------------------
-- The oracle
-- ---------------------------------------------------------------------------

data Verdict
  = Agree
  | HardMismatch String
  | KnownMismatch Known String
  | LoggedRefusal String
  | HardRefusal String
  | BothRefuse
  | SampledOk
  | SampleUnchecked String
  | SampleMismatch String

isHard :: Verdict -> Bool
isHard HardMismatch{} = True
isHard HardRefusal{} = True
isHard SampleMismatch{} = True
isHard _ = False

-- | Judge one (original, rewritten) pair of the program named @prog@.
judge :: String -> Family -> String -> Outcome -> Program -> [Query] -> IO Verdict
judge prog fam site origOut rewritten qs = do
  c <- compileTimed rewritten
  judgeCompiled prog fam site origOut rewritten c qs

-- | 'judge' on the rewritten program's compile from 'compileTimed'.
judgeCompiled :: String -> Family -> String -> Outcome -> Program -> Either String IREnv -> [Query] -> IO Verdict
judgeCompiled prog fam site = judgeWith (refusalIsHard fam) (knownDivergence prog fam site) site

-- | The oracle, given whether a refusal is hard and the known divergence the
-- pair is, if any. A mismatch carries where the stage-diff driver
-- ("SPLL.StageDiff") places it: the whole stage report for a new one, the
-- first diverging stage for a known one.
judgeWith :: Bool -> Maybe Known -> String -> Outcome -> Program -> Either String IREnv -> [Query] -> IO Verdict
judgeWith hardRefusal known site origOut rewritten compiled qs = do
  out <- runCompiled rewritten compiled qs
  case (origOut, out) of
    (Answered as, Answered bs)
      | and (zipWith agrees as bs) -> return Agree
      | otherwise -> do
          let msg = site ++ "\n      original " ++ show as ++ "\n      rewritten " ++ show bs
          return $ maybe (HardMismatch msg) (\k -> KnownMismatch k (msg ++ " [" ++ kDoc k ++ "]")) known
    (Answered _, Refused why)
      | hardRefusal -> return (HardRefusal (site ++ ": " ++ why))
      | otherwise -> return (LoggedRefusal (site ++ ": " ++ why))
    (Refused _, Refused _) -> return BothRefuse
    (Refused _, Answered bs) -> case compiled of
      Right env -> samplingCheck rewritten env (zip qs bs)
      Left err -> return (SampleUnchecked err)

-- | The refused -> answers transition: there is no second derivation, so the
-- answering program is checked against its own forward sampler, at every
-- query point where a window estimate is meaningful (a scalar or a tuple of
-- scalars, with dim 0 or dim equal to the continuous coordinate count, and at
-- most 1 -- a higher-dimensional estimate needs prohibitively many draws).
samplingCheck :: Program -> IREnv -> [(Query, (Double, Int))] -> IO Verdict
samplingCheck p env rows = do
    results <- forM rows $ \((s, params), (pr, d)) ->
      if not (estimable s d) then return Nothing
      else Just <$> estimateAgrees (runGenC p env params) s pr d (2000 :: Int) (3 :: Int)
    return $ case [r | Just r <- results] of
      [] -> SampleUnchecked "no query point with a sampleable shape"
      rs | all fst rs -> SampledOk
         | otherwise -> SampleMismatch (intercalate "; " [m | (False, m) <- rs])
  where
    estimable s d = sampleable s && (d == 0 || (d == 1 && floatCoords s == 1))
    estimateAgrees gen s pr d n retries = do
      drawn <- evalRandIO (replicateM n gen)
      let eps = if d == 0 then 1e-9 else 0.05
          inside = length (filter (within eps s) drawn)
          est = fromIntegral inside / fromIntegral n / (eps ^ d)
      if abs (est - pr) <= samplingTolerance then return (True, "")
      else if retries > 0 then estimateAgrees gen s pr d (2 * n) (retries - 1 :: Int)
      else return (False, "sampled " ++ show est ++ ", compiled " ++ show pr ++ " at " ++ show s)

sampleable :: IRValue -> Bool
sampleable (VFloat _) = True
sampleable (VInt _) = True
sampleable (VTuple a b) = sampleable a && sampleable b
sampleable _ = False

floatCoords :: IRValue -> Int
floatCoords (VFloat _) = 1
floatCoords (VTuple a b) = floatCoords a + floatCoords b
floatCoords _ = 0

within :: Double -> IRValue -> IRValue -> Bool
within eps (VFloat e) (VFloat a) = abs (a - e) <= eps / 2
within _ (VInt e) (VInt a) = e == a
within eps (VTuple e1 e2) (VTuple a1 a2) = within eps e1 a1 && within eps e2 a2
within _ _ _ = False

-- | Every variant of every family of one program, judged.
sweep :: String -> Program -> [Query] -> IO [(Family, Verdict)]
sweep prog p qs = do
  (orig, vs) <- compileSweep p
  sweepCompiled prog p qs orig vs

-- | The default compile ('compileTimed') of a program and of every variant of
-- every family of it, the variants concurrently.
compileSweep :: Program -> IO (Either String IREnv, [(Variant, Either String IREnv)])
compileSweep p = do
  orig <- compileTimed p
  vs <- concurrently [ (,) v <$> compileTimed (variantProgram v) | fam <- allFamilies, v <- variants fam p ]
  return (orig, vs)

-- | 'sweep' on the compiles from 'compileSweep'.
sweepCompiled :: String -> Program -> [Query] -> Either String IREnv -> [(Variant, Either String IREnv)] -> IO [(Family, Verdict)]
sweepCompiled prog p qs orig vs = do
  origOut <- runCompiled p orig qs
  concurrently [ (,) (variantFamily v) <$> (judgeCompiled prog (variantFamily v) (variantSite v) origOut (variantProgram v) c qs
                                              >>= isolated p (variantProgram v) qs)
               | (v, c) <- vs ]

-- ---------------------------------------------------------------------------
-- Isolation: the stage-diff driver on a mismatching pair
-- ---------------------------------------------------------------------------

-- | The stage-diff report ("SPLL.StageDiff") of a pair at the program's query
-- rows, under a 60 s timeout.
stageReport :: Program -> Program -> [Query] -> IO (Either String StageReport)
stageReport a b qs = do
  t <- timedTry (60 * 1000000) $ do
    r <- stageDiff (defaultStageDiffOpts defaultCompilerConfig) { sdQueries = qs, sdTolerance = probTolerance } a b
    evaluate (length (renderStageReport r) `seq` r)
  return $ case t of
    Nothing -> Left "stage diff timed out (60s)"
    Just (Left ex) -> Left ("stage diff crashed: " ++ firstLine (show (ex :: SomeException)))
    Just (Right x) -> Right x

-- | Where the driver places a mismatch: a new one gets the whole report, a
-- known one the first diverging stage only. Other verdicts are unchanged.
isolated :: Program -> Program -> [Query] -> Verdict -> IO Verdict
isolated a b qs v = case v of
  HardMismatch m -> HardMismatch . (m ++) . either (("\n      " ++)) (indentReport . renderStageReport) <$> stageReport a b qs
  KnownMismatch k m -> KnownMismatch k . (m ++) . either (\e -> " (" ++ e ++ ")") ((" -- first divergence: " ++) . firstStage) <$> stageReport a b qs
  _ -> return v
  where
    indentReport = concatMap ("\n      " ++) . lines

firstStage :: StageReport -> String
firstStage r = maybe "none" fst (firstDivergence r)

-- | Run the actions concurrently, at most one per capability, and return
-- their results in order (rethrowing the first exception). A program's
-- variants are independent compiles; run one after another, a program with
-- many sites (gaussianTrajectory8: 136 variants) was a single ~35 s test on
-- one core, the longest in the suite. The cap keeps 'runQueries'' timeout
-- measuring a variant's own work rather than oversubscription.
concurrently :: [IO a] -> IO [a]
concurrently acts = do
  sem <- newQSem =<< getNumCapabilities
  vars <- forM acts $ \act -> do
    v <- newEmptyMVar
    _ <- forkIO (bracket_ (waitQSem sem) (signalQSem sem) (try act) >>= putMVar v)
    return v
  forM vars $ \v -> takeMVar v >>= either (\e -> throwIO (e :: SomeException)) return

-- | Turn one program's verdicts into a test: hard verdicts fail it, and so
-- does a 'knownDivergences' entry for it that nothing matched any more. The
-- rest is the test's info line.
report :: String -> [(Family, Verdict)] -> IO String
report prog verdicts = do
  let hard = [(f, v) | (f, v) <- verdicts, isHard v]
      matched = [k | (_, KnownMismatch k _) <- verdicts]
      stale = [k | k <- knownDivergences, kProg k == prog, k `notElem` matched]
  if not (null hard)
    then assertFailure (unlines (map line hard)) >> return ""
    else if not (null stale)
    then assertFailure (unlines [ "known divergence no longer observed -- fixed? remove its entry and \
                                  \its known-issues pin: " ++ familyName (kFam k) ++ " at \"" ++ kSite k
                                  ++ "\" [" ++ kDoc k ++ "]" | k <- stale ]) >> return ""
    else return $ show (length verdicts) ++ " variants, " ++ show (length [() | (_, Agree) <- verdicts]) ++ " agree"
           ++ concatMap (("\n    " ++) . line) [(f, v) | (f, v) <- verdicts, logged v]
  where
    logged Agree = False
    logged BothRefuse = False
    logged SampledOk = False
    logged _ = True
    line (f, v) = familyName f ++ ": " ++ verdictLine v

-- ---------------------------------------------------------------------------
-- Probe pairs
-- ---------------------------------------------------------------------------

-- | The evidence table of design law-carrying-modality: (row, the family the
-- pair belongs to, the working spelling, its rewrite, a query point). Rows
-- 1-6 are helper extraction (followed by inlining the now-single use), 7, 9
-- and 10 draw introduction, 8 alias introduction.
probePairs :: [(Int, Family, String, String, IRValue)]
probePairs =
  [ (1, HelperExtract, "main = draw x = Normal in (x, x + 1.0)", "f x = (x, x + 1.0)\nmain = f Normal", VTuple (VFloat 0.3) (VFloat 1.3))
  , (2, HelperExtract, "main = draw x = Uniform in (x, x)", "f x = (x, x)\nmain = f Uniform", VTuple (VFloat 0.3) (VFloat 0.3))
  , (3, HelperExtract, "main = draw x = Normal in (x, Normal)", "f x = (x, Normal)\nmain = f Normal", VTuple (VFloat 0.3) (VFloat 0.2))
  , (4, HelperExtract, "main = draw x = Uniform in if x < 0.5 then x else x * 3.0", "f x = if x < 0.5 then x else x * 3.0\nmain = f Uniform", VFloat 0.3)
  , (5, HelperExtract, "main = draw x = Uniform in (x, x * Normal)", "f x = (x, x * Normal)\nmain = f Uniform", VTuple (VFloat 0.5) (VFloat 0.2))
  , (6, HelperExtract, "main = draw x = Uniform in draw y = Uniform in (x, x + y)", "pair a b = (a, a + b)\nmain = pair Uniform Uniform", VTuple (VFloat 0.3) (VFloat 0.7))
  , (7, DrawIntro, "main = draw x = Normal in x * 2.0 + 1.0", "main = draw x = Normal in draw y = x * 2.0 in y + 1.0", VFloat 1.4)
  , (8, AliasIntro, "main = draw x = Normal in (x, x + Normal)", "main = draw x = Normal in draw y = x in (y, y + Normal)", VTuple (VFloat 0.3) (VFloat 0.5))
  , (9, DrawIntro, "main = draw x = Uniform in (x, x * 2.0 + Normal)", "main = draw x = Uniform in draw y = x * 2.0 in (x, y + Normal)", VTuple (VFloat 0.3) (VFloat 1.0))
  , (10, DrawIntro, "main = 0.0 * Normal", "main = draw z = 0.0 in z * Normal", VFloat 0.0)
  ]

parseSrc :: String -> String -> Program
parseSrc lbl src = either (error . ((lbl ++ ": ") ++) . show) id (tryParseProgram lbl src)

-- | One test per probe pair: the hand-written pair judged in both directions
-- (the working spelling as original, and the rewritten one as original), then
-- the working spelling's own rewrite sweep.
probeTests :: TestTree
probeTests = testGroup "Probes"
  [ testCaseInfo ("row " ++ show row ++ ": " ++ works) $ do
      let name = "probe" ++ show row
          pw = parseSrc (name ++ "w") works
          pr = parseSrc (name ++ "r") rewritten
          qs = [(q, [])]
      ow <- runQueries pw qs
      orr <- runQueries pr qs
      forward <- judge name fam "hand-written rewrite" ow pr qs >>= isolated pw pr qs
      backward <- judge name fam "hand-written rewrite, reversed" orr pw qs >>= isolated pr pw qs
      swept <- sweep name pw qs
      report name ((fam, forward) : (fam, backward) : swept)
  | (row, fam, works, rewritten, q) <- probePairs ]

-- ---------------------------------------------------------------------------
-- Unit tests for the rewrites' preconditions
-- ---------------------------------------------------------------------------

mainOf :: String -> Expr
mainOf src = case lookup "main" (functions (parseSrc "unit" src)) of
  Just e -> e
  Nothing -> error "no main"

-- | The rendered site labels of one family over a one-line program.
sitesOf :: Family -> String -> [String]
sitesOf fam src = map variantSite (variants fam (parseSrc "unit" src))

unitTests :: TestTree
unitTests = testGroup "Units"
  [ -- The integration sweep's PType metric reads main's root PType off the
    -- modality snapshot; a Nothing on both sides would compare equal and
    -- check nothing.
    testCase "mainPTypeOf reads main's root PType" $ do
      mainPTypeOf (parseSrc "a" "main = 1.0") @?= Just Deterministic
      assertBool "a random main is not Deterministic"
        (maybe False (/= Deterministic) (mainPTypeOf (parseSrc "b" "main = Normal + 1.0")))
  , testCase "draw and literal application parse to the same AST" $
      assertBool "draw x = e in b and (\\x -> b) e should be one AST"
        (parseSrc "a" "main = draw x = Normal in x + 1.0" ~= parseSrc "b" "main = (\\x -> x + 1.0) Normal")
  -- Linearity: exactly one free occurrence, not under a function body.
  , testCase "linear inline: one use inlines" $
      isJust (linearInline (mainOf "main = draw x = Normal in x + 1.0")) @?= True
  , testCase "linear inline: two uses refuse" $
      isJust (linearInline (mainOf "main = draw x = Normal in x + x")) @?= False
  , testCase "linear inline: no use refuses" $
      isJust (linearInline (mainOf "main = draw x = Normal in 1.0")) @?= False
  , testCase "linear inline: a use under a function body refuses" $
      isJust (linearInline (mainOf "main = draw x = Normal in (\\y -> x + y)")) @?= False
  , testCase "linear inline: a use inside a nested draw inlines" $
      isJust (linearInline (mainOf "main = draw x = Normal in draw y = x + 1.0 in y")) @?= True
  , testCase "linear inline: a shadowed use does not count" $
      isJust (linearInline (mainOf "main = draw x = Normal in draw x = Uniform in x + x")) @?= False
  , testCase "linear inline: inlining avoids capture" $ do
      -- draw x = y in draw y = Normal in x + y: substituting y for x under the
      -- inner y binder must rename that binder, not capture.
      let e = either (error . show) id (tryParseProgram "u" "f y = draw x = y in draw y = Normal in x + y\nmain = f 1.0")
          f = maybe (error "no f") id (lookup "f" (functions e))
          body = case node f of Lambda _ b -> b; _ -> f
      case linearInline body of
        Nothing -> assertFailure "should inline"
        Just e' -> Set.member "y" (freeVarsExpr e') @?= True
  -- Helper extraction: the free locals become parameters; top-level names do not.
  , testCase "helper extract: free locals become parameters, in scope order" $ do
      let (call, decl) = extractHelper ["a", "b", "c"] "h" (mainOf "main = b + a")
      freeVarsExpr call @?= Set.fromList ["h", "a", "b"]
      paramsOf decl @?= ["a", "b"]
  , testCase "helper extract: a closed subterm gives a nullary helper" $ do
      let (call, decl) = extractHelper ["x"] "h" (mainOf "main = Normal + 1.0")
      freeVarsExpr call @?= Set.fromList ["h"]
      paramsOf decl @?= []
  , testCase "helper extract: a name bound inside the subterm is not a parameter" $ do
      let (_, decl) = extractHelper ["x"] "h" (mainOf "main = draw x = Normal in x")
      paramsOf decl @?= []
  , testCase "helper extract: the fresh helper name avoids every program name" $ do
      let vs = variants HelperExtract (parseSrc "u" "rwh0 = Normal\nmain = rwh0 + 1.0")
      assertBool "expected a site" (not (null vs))
      mapM_ (\v -> let names = map fst (functions (variantProgram v))
                   in assertBool ("duplicate declaration: " ++ show names) (nub names == names)) vs
  -- Alias introduction: capture avoidance comes from a program-fresh name.
  , testCase "alias intro: the alias name avoids names bound in the body" $ do
      let vs = variants AliasIntro (parseSrc "u" "main = draw x = Normal in draw rwv0 = Uniform in x + rwv0")
      assertBool "alias must not be named rwv0" (not (null vs))
      mapM_ (\v -> assertBool "fresh name reused" (not ("draw rwv0 = x" `isInfixOf` variantSite v))) vs
  , testCase "alias intro: an unused binder has no site" $
      isJust (aliasIntro "y" (mainOf "main = \\x -> 1.0")) @?= False
  -- Draw introduction: never out of an if arm or a function body.
  , testCase "draw intro: an if condition is a site, its arms are not" $
      sitesOf DrawIntro "main = if Uniform < 0.5 then Normal else Uniform"
        @?= ["main: draw-intro (lt Uniform 0.5)", "main: draw-intro Uniform", "main: draw-intro 0.5"]
  , testCase "draw intro: a local variable is left to alias introduction" $
      sitesOf DrawIntro "main = draw x = Normal in x + 1.0"
        @?= ["main: draw-intro Normal", "main: draw-intro 1.0"]
  , testCase "draw intro: the callee of an application is not bound" $
      sitesOf DrawIntro "f x = x\nmain = f 1.0" @?= ["main: draw-intro 1.0"]
  -- If-flip: the condition is negated and the arms swap.
  , testCase "if flip: negates the condition and swaps the arms" $
      sitesOf IfFlip "main = if Uniform < 0.5 then Normal else Uniform"
        @?= ["main: if-flip (if (lt Uniform 0.5) then Normal else Uniform)"]
  , testCase "if flip: the rewritten program is if not c then b else a" $
      map (render' . variantProgram) (variants IfFlip (parseSrc "u" "main = if Uniform < 0.5 then Normal else Uniform"))
        @?= [render' (parseSrc "v" "main = if not (Uniform < 0.5) then Uniform else Normal")]
  -- Comparison rewrites: the negated spelling reads each operand twice, so it
  -- applies to variables and constants only.
  , testCase "compare flip: a random operand is swapped, never duplicated" $
      sitesOf CompareFlip "main = Normal < 0.5" @?= ["main: compare-swap (lt Normal 0.5)"]
  , testCase "compare flip: a top-level name is not duplicated (each read re-runs it)" $
      sitesOf CompareFlip "coin = Uniform\nmain = coin < 0.5" @?= ["main: compare-swap (lt coin 0.5)"]
  , testCase "compare flip: a variable operand is also negated" $
      map (render' . variantProgram) (variants CompareFlip (parseSrc "u" "main = draw x = Normal in x < 0.5"))
        @?= map (render' . parseSrc "v") [ "main = draw x = Normal in 0.5 > x"
                                         , "main = draw x = Normal in not ((0.5 < x) || (0.5 == x))" ]
  , testCase "compare flip: > negates with its operands in order" $
      map (render' . variantProgram) (variants CompareFlip (parseSrc "u" "main = draw x = Normal in x > 0.5"))
        @?= map (render' . parseSrc "v") [ "main = draw x = Normal in 0.5 < x"
                                         , "main = draw x = Normal in not ((x < 0.5) || (x == 0.5))" ]
  -- InjF identities: only at a node inference typed Float or Int.
  , testCase "injf identity: a Float site gets the three identities, a Bool site none" $
      sitesOf InjFIdentity "main = Uniform < 0.5"
        @?= ["main: plus-zero Uniform", "main: one-times Uniform", "main: double-negate Uniform"]
  , testCase "injf identity: an Int site uses the Int operators" $
      map (render' . variantProgram) (take 1 (variants InjFIdentity (parseSrc "u" "f n = n\nmain = f 3")))
        @?= [render' (parseSrc "v" "f n = n ++ 0\nmain = f 3")]
  , testCase "injf identity: a + call's operands commute, a constant is not wrapped" $
      sitesOf InjFIdentity "main = draw x = Normal in x + 1.0"
        @?= [ "main: plus-zero (draw x = Normal in (plus x 1.0))", "main: one-times (draw x = Normal in (plus x 1.0))"
            , "main: double-negate (draw x = Normal in (plus x 1.0))", "main: plus-zero (plus x 1.0)", "main: one-times (plus x 1.0)", "main: double-negate (plus x 1.0)"
            , "main: commute (plus x 1.0)", "main: plus-zero x", "main: one-times x", "main: double-negate x"
            , "main: plus-zero Normal", "main: one-times Normal", "main: double-negate Normal" ]
  , testCase "injf identity: a program that does not type gets only the commutation" $
      sitesOf InjFIdentity "f x = x + 1.0\nmain = f True" @?= ["f: commute (plus x 1.0)"]
  -- Alpha renaming: fresh, and shadowing an enclosing binder the body ignores.
  , testCase "alpha rename: fresh, and reusing another scope's binder name" $
      map (render' . variantProgram) (variants AlphaRename (parseSrc "u" "f a = a + 1.0\nmain = draw b = Uniform in f b"))
        @?= map (render' . parseSrc "v") [ "f rwa0 = rwa0 + 1.0\nmain = draw b = Uniform in f b"
                                         , "f b = b + 1.0\nmain = draw b = Uniform in f b"
                                         , "f a = a + 1.0\nmain = draw rwa0 = Uniform in f rwa0"
                                         , "f a = a + 1.0\nmain = draw a = Uniform in f a" ]
  , testCase "alpha rename: a binder of the same declaration is never reused" $
      sitesOf AlphaRename "main = draw a = Normal in draw b = Uniform in b + 1.0 + (draw c = Normal in c)"
        @?= ["main: alpha-fresh (\\b -> (plus (plus b 1.0) (draw c = Normal in c)))", "main: alpha-fresh (\\c -> c)"]
  , testCase "alpha rename: a name the body reads is not reused" $
      sitesOf AlphaRename "main = draw a = Normal in draw b = Uniform in a + b"
        @?= ["main: alpha-fresh (\\a -> (draw b = Uniform in (plus a b)))", "main: alpha-fresh (\\b -> (plus a b))"]
  , testCase "alpha rename: an unused binder has no site" $
      sitesOf AlphaRename "main = draw a = Normal in 1.0" @?= []
  -- Tuple laws: projection drops a call-free component; pairing wraps a
  -- first-order operand.
  , testCase "tuple law: a call-free pair projects" $
      map (render' . variantProgram) (filter (("fst-pair" `isInfixOf`) . variantSite) (variants TupleLaw (parseSrc "u" "main = fst (Normal, Uniform)")))
        @?= [render' (parseSrc "v" "main = Normal")]
  , testCase "tuple law: a pair whose dropped half calls does not project" $
      filter ("fst-pair" `isInfixOf`) (sitesOf TupleLaw "f x = x\nmain = fst (Normal, f 1.0)") @?= []
  , testCase "tuple law: a constant or a function-valued operand is not paired" $
      sitesOf TupleLaw "main = map (\\v -> v + 1.0) [Normal]" @?= ["main: pair-fst v", "main: pair-fst Normal"]
  -- of-clause toggling: a round-trip in both directions; a narrowing clause has none.
  , testCase "of toggle: a clause equal to its auto-derivation is removed, a missing one written" $ do
      let decl d = "neural n :: (Symbol -> (Bool, Bool))" ++ d ++ "\nmain s = draw x = n s in if fst x then 1 else 0"
          tagOf q = [t | (_, _, t) <- neurals q]
      map (tagOf . snd) (ofToggles (parseSrc "u" (decl " of ([True, False], _)"))) @?= [[Nothing]]
      map (tagOf . snd) (ofToggles (parseSrc "u" (decl ""))) @?= [[Just (MultiTuple (MultiDiscretes [VBool True, VBool False]) (MultiDiscretes [VBool True, VBool False]))]]
      map fst (ofToggles (parseSrc "u" (decl " of ([True], _)"))) @?= []
  -- Rewrite sequences (M4): applied in turn, shrunk from the tail.
  , testCase "steps: a sequence applies each step to the program the last one produced" $ do
      let p = parseSrc "u" "main = draw x = Normal in x + 1.0"
          commute = stepAt InjFIdentity "commute" p
      fmap render' (applySteps p [commute]) @?= Just (render' (parseSrc "v" "main = draw x = Normal in 1.0 + x"))
      fmap render' (applySteps p [commute, commute]) @?= Just (render' p)
  , testCase "steps: a step whose node is not in the program does not apply" $ do
      let p = parseSrc "u" "main = draw x = Normal in x + 1.0"
      fmap render' (applySteps (parseSrc "v" "main = 1.0") [stepAt InjFIdentity "commute" p]) @?= Nothing
  , testCase "steps: every listed step applies, and two rewrites at one node are told apart" $ do
      let p = parseSrc "u" "main = Normal + 1.0"
          ss = stepsOf p
      assertBool "every step applies" (all (isJust . applySteps p . (: [])) ss)
      map stepIndex (filter ((== (InjFIdentity, ("main", []))) . (\s -> (stepFamily s, stepNode s))) ss) @?= [0, 1, 2, 3]
  , testCase "shrink: the last step goes first, an inapplicable or empty sequence never appears" $ do
      let p = parseSrc "u" "main = draw x = Normal in x + 1.0"
          commute = stepAt InjFIdentity "commute" p
          q = maybe (error "no step") id (applySteps p [commute])
          inner = stepAt InjFIdentity "plus-zero (plus 1.0 x)" q
      shrinkSteps p [commute, inner] @?= [[commute], [inner]]
      shrinkSteps (parseSrc "w" "main = 1.0") [stepAt InjFIdentity "plus-zero Normal" (parseSrc "z" "main = Normal")] @?= []
  , testCase "shrink: a failure caused by one step shrinks to that step alone" $ do
      -- A stand-in oracle that fails exactly when the sequence if-flips: the
      -- shrinker has to drop the harmless steps around it, the one before it
      -- having rewritten text inside the if.
      let p = parseSrc "u" "main = draw x = Normal in if x < 0.5 then x + 1.0 else 2.0"
          before = stepAt InjFIdentity "commute (plus x 1.0)" p
          p1 = maybe (error "no step") id (applySteps p [before])
          flipStep = stepAt IfFlip "if-flip" p1
          p2 = maybe (error "no step") id (applySteps p1 [flipStep])
          after = stepAt CompareFlip "compare-swap" p2
          sq = [before, flipStep, after]
      assertBool "the sequence applies" (isJust (applySteps p sq))
      r <- quickCheckWithResult stdArgs { chatty = False, maxSuccess = 1 }
             (forAllShrinkShow (return sq) (shrinkSteps p) (intercalate "; " . map (familyName . stepFamily))
                (\ss -> counterexample "if-flipped" (IfFlip `notElem` map stepFamily ss)))
      case r of
        Failure { failingTestCase = (shrunk : _) } -> shrunk @?= "if-flip"
        _ -> assertFailure ("expected one shrunk counterexample, got: " ++ output r)
  -- The stage-diff driver (M4).
  , testCase "stage diff: a pair that agrees everywhere has no divergence" $ do
      -- Probe row 10, fixed by dispatch-on-law-certificates: both spellings are
      -- a point mass at 0.
      r <- stageDiff (defaultStageDiffOpts defaultCompilerConfig) { sdQueries = [(VFloat 0.0, []), (VFloat 0.5, [])] }
                (parseSrc "a" "main = 0.0 * Normal") (parseSrc "b" "main = draw z = 0.0 in z * Normal")
      assertBool (renderStageReport r) (isNothing (firstDivergence r))
  , testCase "stage diff: the parse stage shows the rewrite, not a divergence" $ do
      r <- stageDiff (defaultStageDiffOpts defaultCompilerConfig)
                (parseSrc "a" "main = if Uniform < 0.5 then 1.0 else 2.0") (parseSrc "b" "main = (if Uniform < 0.5 then 1.0 else 2.0) + 0.0")
      lookup "After Parsing (no annotations)" (stageRows r) @?= Just (Rewrite ["main [if -> plus]"])
      assertBool (renderStageReport r) (isNothing (firstDivergence r))
  , testCase "stage diff: a seeded enum-annotation defect is placed at enum annotation" $ do
      -- The seeded defect: from enum annotation on, a `+ 0.0` node's value
      -- set loses its last value. Only the rewrite has such a node, as with a
      -- real defect the rewrite triggers; every later stage inherits the
      -- wrong set.
      let a = parseSrc "a" "main = if Uniform < 0.5 then 1.0 else 2.0"
          b = parseSrc "b" "main = (if Uniform < 0.5 then 1.0 else 2.0) + 0.0"
          seeded (ss, res) = (seedFrom "After Enum Annotation" truncatePlusZeroTags ss, res)
          r = stageDiffStages (defaultStageDiffOpts defaultCompilerConfig)
                (compileStages defaultCompilerConfig a) (seeded (compileStages defaultCompilerConfig b))
                (Nothing, Nothing) (Nothing, Nothing)
      fmap fst (firstDivergence r) @?= Just "After Enum Annotation"
      lookup "After RType Inference" (stageRows r) @?= Just Same
  , testCase "stage diff: a refusal is placed at the stage that refused" $ do
      r <- stageDiff (defaultStageDiffOpts defaultCompilerConfig)
                (parseSrc "a" "main = 1.0 + 2.0") (parseSrc "b" "main = 1.0 + True")
      fmap fst (firstDivergence r) @?= Just "After RType Inference"
  -- Task arrow-result-main-entry-points: a function-valued main is
  -- eta-expanded after RInfer into the program a user writes by hand, under
  -- `if`, `draw` and `define` alike. The stage diff against the hand-expanded
  -- spelling must show the expansion stage, and no divergence anywhere.
  , testCase "eta expansion: an arrow-result main is its hand-expanded spelling" $
      etaPair "main = if Uniform < 0.5 then (\\x -> x + 1.0) else (\\x -> x * 3.0)"
              "main y = (if Uniform < 0.5 then (\\x -> x + 1.0) else (\\x -> x * 3.0)) y"
              [(VFloat 2.0, [VFloat 1.0]), (VFloat 3.0, [VFloat 1.0]), (VFloat 2.5, [VFloat 1.0])]
  , testCase "eta expansion: under a draw" $
      etaPair "main = draw u = Uniform < 0.3 in if u then (\\x -> x + 1.0) else (\\x -> x * 3.0)"
              "main y = (draw u = Uniform < 0.3 in if u then (\\x -> x + 1.0) else (\\x -> x * 3.0)) y"
              [(VFloat 2.0, [VFloat 1.0]), (VFloat 3.0, [VFloat 1.0])]
  , testCase "eta expansion: under a define" $
      etaPair "main = define u = Uniform in if u < 0.5 then (\\x -> x + u) else (\\x -> x * 2.0)"
              "main y = (define u = Uniform in if u < 0.5 then (\\x -> x + u) else (\\x -> x * 2.0)) y"
              [(VFloat 2.2, [VFloat 2.0]), (VFloat 4.0, [VFloat 2.0])]
  -- The other side of the decision: a helper whose function value is bound
  -- once and applied twice shares one draw between the calls, which an
  -- expanded helper would turn into two. It must stay as written, while the
  -- same helper called with its argument is expanded.
  , testCase "eta expansion: a function value applied twice is not expanded" $ do
      let pick = "pick = if Uniform < 0.5 then (\\x -> x + 1.0) else (\\x -> x * 3.0)\n"
          isLam q n = case lookup n (functions q) of
            Just (Expr _ Lambda{}) -> True
            _ -> False
      shared <- either (assertFailure . ("rtypedProgram: " ++)) return
                  (rtypedProgram (parseSrc "a" (pick ++ "main = draw h = pick in (h 1.0, h 2.0)")))
      assertBool "pick stays a function value" (not (isLam shared "pick"))
      called <- either (assertFailure . ("rtypedProgram: " ++)) return
                  (rtypedProgram (parseSrc "b" (pick ++ "main = pick")))
      assertBool "main is expanded" (isLam called "main")
      assertBool "pick is expanded once main calls it fully" (isLam called "pick")
  ]
  where
    -- An arrow-result program and its hand-expanded spelling: the automatic
    -- expansion ran, and nothing diverges, answers included.
    etaPair a b qs = do
      r <- stageDiff (defaultStageDiffOpts defaultCompilerConfig) { sdQueries = qs, sdTolerance = probTolerance }
                (parseSrc "auto" a) (parseSrc "manual" b)
      assertBool ("the expansion ran:\n" ++ renderStageReport r)
        (isJust (lookup "After Arrow-Result Eta Expansion" (stageRows r)))
      assertBool (renderStageReport r) (isNothing (firstDivergence r))
      assertBool ("both answer:\n" ++ renderStageReport r) (lookup answersStage (stageRows r) == Just Same)
    -- The first step of a family whose site label contains the text.
    stepAt fam txt q = case [ st | st <- stepsOf q, stepFamily st == fam, txt `isInfixOf` stepSite st ] of
      (st : _) -> st
      [] -> error ("no " ++ familyName fam ++ " step at " ++ txt)
    -- Apply a seeded defect to every program stage from the named one on.
    seedFrom l f ss = let (before, from) = break ((== l) . snapLabel) ss in before ++ map (seedSnap f) from
    seedSnap f (StageSnapshot l v) = StageSnapshot l $ case v of
      StageProgram q -> StageProgram (onBodies f q)
      StageTyped q laws -> StageTyped (onBodies f q) laws
      StageIR e -> StageIR e
    onBodies f q = q { functions = [ (n, f b) | (n, b) <- functions q ] }
    truncatePlusZeroTags (Expr t e) =
      let e' = fmap truncatePlusZeroTags e
      in case e' of
           InjF (Named "plus") [_, Expr _ (Constant (VFloat 0))] ->
             Expr t { tags = [ DiscreteValues (MultiDiscretes (init vs)) | DiscreteValues (MultiDiscretes vs) <- tags t, not (null vs) ] } e'
           _ -> Expr t e'
    paramsOf (Expr _ (Lambda v b)) = v : paramsOf b
    paramsOf _ = []
    -- A program's declarations, annotations dropped, to compare a rewrite's
    -- output with the program the rewrite should have produced.
    render' q = show [ (n, stripExpr b) | (n, b) <- functions q ]
    stripExpr (Expr _ f) = Expr makeTypeInfo (fmap stripExpr f)

-- ---------------------------------------------------------------------------
-- Corpus sweep
-- ---------------------------------------------------------------------------

rewriteTests :: TestTree
rewriteTests = testGroup "RewriteInvariance" [unitTests, probeTests]

-- | One test per corpus program: every family at every site, compared at the
-- program's own probability query points (both possible and impossible rows).
--
-- The program and its variants are always compiled; their queries run only
-- when 'rewriteKey' differs from the one recorded at the program's last pass
-- ('ImpactManifest').
rewriteCorpusTests :: Corpus -> Manifest -> IO TestTree
rewriteCorpusTests corpus manifest = corpusSweep corpus SweepSpec
  { sweepName = "Slow.RewriteInvarianceCorpus", sweepTier = Slow, sweepSlow = SkipSlow
  , sweepSelect = rewritePool
  , sweepNote = "every rewrite family at every site agrees with the original at its p() rows" } $ \e ->
    testCaseInfo (ceName e) $ do
      let n = ceName e; p = ceProgram e; qs = queries e
      (orig, vs) <- compileSweep p
      r <- cachedAction manifest "Slow.RewriteInvarianceCorpus" n (rewriteKey manifest p qs orig vs)
             (sweepCompiled n p qs orig vs >>= report n)
      return (either ("skipped: unchanged since " ++) id r)
  where
    queries = corpusQueries

-- | The programs the rewrite sweeps take: interpreter-routed, not neural,
-- with at least one probability row.
rewritePool :: CorpusEntry -> Bool
rewritePool e = Interpreter `elem` ceBackends e && null (neurals (ceProgram e)) && not (null (corpusQueries e))

corpusQueries :: CorpusEntry -> [Query]
corpusQueries e = [(s, params) | ProbTestCase _ s params _ <- ceCases e]

-- ---------------------------------------------------------------------------
-- Rewrite sequences (M4)
-- ---------------------------------------------------------------------------

-- | The sequence property (milestone M4 of transformation-differential-testing):
-- a base program and one to three rewrite steps, of any families, applied in
-- turn ('applySteps'), judged against the base by the same three-outcome
-- oracle. A hard verdict is shrunk by QuickCheck over the sequence, not the
-- program ('shrinkSteps': the last step first), and the minimal pair is handed
-- to the stage-diff driver, whose report is the counterexample.
--
-- A single step is what 'rewriteCorpusTests' already checks at every site, so
-- what this adds is composition: two rewrites, each harmless alone, that
-- together reach a shape neither does. The pool is the sweep's (the same
-- corpus programs) plus the probe pairs' working spellings.
--
-- Deterministic: each test runs a fixed number of cases from a fixed seed,
-- so a run is reproducible and a new failure is a finding, not noise. A
-- sequence with a step at a 'knownDivergences' site is judged known.
rewriteSequenceTests :: Corpus -> IO TestTree
rewriteSequenceTests corpus = corpusSweepAll corpus SweepSpec
  { sweepName = "Slow.RewriteSequences", sweepTier = Slow, sweepSlow = SkipSlow
  , sweepSelect = rewritePool
  , sweepNote = "random rewrite sequences agree with the original; a failure shrinks over the sequence and is stage-diffed" } $ \entries -> do
    let pool = [ (ceName e, ceProgram e, corpusQueries e) | e <- entries ]
            ++ [ ("probe" ++ show row, parseSrc ("probe" ++ show row) works, [(q, [])]) | (row, _, works, _, q) <- probePairs ]
    return $ testGroup "RewriteSequences"
      [ testCaseInfo ("seed " ++ show sd) (sequenceProperty pool sd sequenceCasesPerSeed) | sd <- sequenceSeeds ]

sequenceSeeds :: [Int]
sequenceSeeds = [20261014, 20261015, 20261016, 20261017]

sequenceCasesPerSeed :: Int
sequenceCasesPerSeed = 200

type Base = (String, Program, [Query])

-- | Run the sequence property over a pool from one seed: 'Right' the summary,
-- or the shrunk counterexample as a test failure.
sequenceProperty :: [Base] -> Int -> Int -> IO String
sequenceProperty pool seed cases = do
  r <- quickCheckWithResult stdArgs { replay = Just (mkQCGen seed, 0), maxSuccess = cases, chatty = False, maxShrinks = 30 }
         (sequenceProp pool)
  case r of
    Success { output = o } -> return o
    _ -> assertFailure (output r) >> return ""

sequenceProp :: [Base] -> Property
sequenceProp pool = forAllShrinkShow gen shrinker shown $ \(i, steps) -> not (null steps) ==> ioProperty (check i steps)
  where
    gen = do
      i <- chooseInt (0, length pool - 1)
      let (_, p, _) = pool !! i
      steps <- genSteps 3 p
      return (i, steps)
    shrinker (i, steps) = let (_, p, _) = pool !! i in [ (i, ss) | ss <- shrinkSteps p steps ]
    shown (i, steps) = let (n, p, _) = pool !! i
                       in n ++ ": " ++ intercalate "; " (map renderStep (maybe steps snd (applyStepsLabelled p steps)))
    check i steps0 = do
      let (name, p, qs) = pool !! i
      case applyStepsLabelled p steps0 of
        Nothing -> return (property Discard)
        Just (rewritten, steps) -> do
          v <- judgeSequence name p qs steps rewritten
          frontier <- case v of
            LoggedRefusal m -> do
              r <- stageReport p rewritten qs
              return [either id (\rep -> firstStage rep ++ maybe "" (" -- " ++) (frontierClass rep m)) r]
            _ -> return []
          return $ tabulate "transition" [transition v] $ tabulate "compiled -> refuses: first divergence" frontier
                 $ counterexample (verdictLine v) (not (isHard v))
    transition v = case v of
      Agree -> "both answer, agree"
      KnownMismatch{} -> "known mismatch"
      HardMismatch{} -> "MISMATCH"
      LoggedRefusal{} -> "compiled -> refuses"
      HardRefusal{} -> "compiled -> refuses (promoted)"
      BothRefuse -> "both refuse"
      SampledOk -> "refused -> compiles, sampling agrees"
      SampleUnchecked{} -> "refused -> compiles, unchecked"
      SampleMismatch{} -> "SAMPLING MISMATCH"

-- | Judge a rewrite sequence against its base, with the stage diff of a
-- mismatch. A refusal is hard only if every step's family promotes it; the
-- pair is known if any step's site is a 'knownDivergences' entry.
judgeSequence :: String -> Program -> [Query] -> [Step] -> Program -> IO Verdict
judgeSequence name p qs steps rewritten = do
  origOut <- runQueries p qs
  c <- compileTimed rewritten
  let fams = map stepFamily steps
      known = case [ k | s <- steps, Just k <- [knownDivergence name (stepFamily s) (stepSite s)] ]
                   ++ [ Known name (last fams) "" (ksDoc k) | k <- knownSequenceDivergences, ksProg k == name, all (`elem` fams) (ksFams k) ] of
        (k : _) -> Just k
        [] -> Nothing
  v <- judgeWith (all (refusalIsHard . stepFamily) steps) known (intercalate "; " (map renderStep steps)) origOut rewritten c qs
  isolated p rewritten qs v

-- | Which of the refusal classes of task dispatch-on-law-certificates (M6 of
-- law-carrying-modality, "The draw-introduction frontier") a compiled ->
-- refuses transition looks like, from its stage report and its message.
-- Classes A-C are the let rule flooring a binding no engine measures, which
-- the stage diff shows as the modality stage typing a node Bottom; D is
-- enumeration meeting a density at run time; E a VAnyExcept witness reaching
-- a runtime test. F (gaussianTrajectory4's tuple-shaped tail) has no
-- signature of its own. A guide for reading the frontier, not a verdict.
frontierClass :: StageReport -> String -> Maybe String
frontierClass rep msg
  | "continuous density" `isInfixOf` msg = Just "M6 class D (enumeration over a density body)"
  | "VAnyExcept" `isInfixOf` msg = Just "M6 class E (a VAnyExcept witness reaches a runtime test)"
  | Just (_, Diverges ds) <- firstDivergence rep, any ("vs Bottom" `isInfixOf`) ds = Just "M6 classes A-C (a binding floored to Bottom)"
  | otherwise = Nothing

verdictLine :: Verdict -> String
verdictLine v = case v of
  HardMismatch m -> "MISMATCH " ++ m
  KnownMismatch _ m -> "known mismatch " ++ m
  LoggedRefusal m -> "compiled -> refuses (log-only) " ++ m
  HardRefusal m -> "compiled -> refuses (promoted) " ++ m
  SampleMismatch m -> "refused -> compiles, SAMPLING MISMATCH " ++ m
  SampleUnchecked m -> "refused -> compiles, unchecked by sampling: " ++ m
  SampledOk -> "refused -> compiles, sampling agrees"
  Agree -> "agree"
  BothRefuse -> "both refuse"

-- ---------------------------------------------------------------------------
-- Integration: config pairs crossed with rewritten variants, and the
-- assertion metrics (umbrella pass of transformation-differential-testing)
-- ---------------------------------------------------------------------------

-- | The config axes of milestone M1 (task
-- transformation-differential-testing-m1-config-differencing), each the
-- non-default side of its pair. On an unchanged program the corpus sweeps
-- check them; here they run on every rewritten variant. The branch-count
-- compile also supplies the variant's branch counts.
integrationConfigs :: [(String, CompilerConfig)]
integrationConfigs =
  [ ("-O0", defaultCompilerConfig { optimizerLevel = 0 })
  , ("topK 0", defaultCompilerConfig { topKThreshold = Just 0 })
  , (branchCountLabel, branchCountConfig) ]

branchCountLabel :: String
branchCountLabel = "branch counts"

branchCountConfig :: CompilerConfig
branchCountConfig = defaultCompilerConfig { countBranches = True }

-- | A variant whose default compile agrees with the original but whose
-- compile under one 'integrationConfigs' entry does not (a refusal, a crash,
-- or other numbers). Matched on (program, family, a substring of the site
-- label, the config's label); logged, and an entry nothing matches any more
-- fails its program's test. Each tracking document carries the minimal
-- program.
data KnownConfig = KnownConfig { kcProg :: String, kcFam :: Family, kcSite :: String, kcConfig :: String, kcDoc :: String }
  deriving (Eq)

knownConfigDivergences :: [KnownConfig]
knownConfigDivergences =
  -- A set-witness residue factor fixes the bound variable at a wildcard
  -- witness, and where the spine reaches it through a draw or a call the
  -- factor evaluates the variable's arithmetic (x + 0.0, log x) on the
  -- wildcard at -O0; -O2 folds the comparison against the ANY slot first.
  [ KnownConfig "anySlotThroughPlusInverse" DrawIntro "draw-intro (plus x 0.0)" "-O0" "residue-factor-at-wildcard-witness-evaluates-arithmetic"
  , KnownConfig "anySlotThroughPlusInverse" DrawIntro "draw-intro 1.0" "-O0" "residue-factor-at-wildcard-witness-evaluates-arithmetic"
  , KnownConfig "anySlotThroughPlusInverse" HelperExtract "extract (TCons (plus x 0.0) 1.0)" "-O0" "residue-factor-at-wildcard-witness-evaluates-arithmetic"
  , KnownConfig "anySlotThroughPlusInverseTupleSplit" DrawIntro "draw-intro (plus h 0.0)" "-O0" "residue-factor-at-wildcard-witness-evaluates-arithmetic"
  , KnownConfig "anySlotThroughInverseNested" DrawIntro "draw-intro (log x)" "-O0" "residue-factor-at-wildcard-witness-evaluates-arithmetic"
  , KnownConfig "anySlotThroughInverseNested" DrawIntro "draw-intro 2.0" "-O0" "residue-factor-at-wildcard-witness-evaluates-arithmetic" ]

knownConfigDivergence :: String -> Family -> String -> String -> Maybe KnownConfig
knownConfigDivergence prog fam site cfg =
  case [ k | k <- knownConfigDivergences, kcProg k == prog, kcFam k == fam, kcConfig k == cfg, kcSite k `isInfixOf` site ] of
    (k : _) -> Just k
    [] -> Nothing

-- | One test per pool program: the integration check of the umbrella pass of
-- transformation-differential-testing. For every variant (of every family,
-- at every site) whose default compile agrees with the original's:
--
-- * hard: each 'integrationConfigs' compile of the variant answers its rows
--   as the variant's default compile does. A refusal there is hard too: a
--   config is not supposed to change capability. 'knownConfigDivergences'
--   are logged.
-- * hard: the variant's forward sampler matches its own densities
--   ('samplingCheck'), so every transformed variant enters the
--   sampling-vs-PDF pool, not only the refused -> compiles ones.
-- * hard: the 'PType' of @main@ is the original's, by strict equality (the
--   design's "Assertion metrics").
-- * logged: the branch count at each row against the original's. Branch
--   counts measure the path a compile takes, and rewrites change that path
--   (see the design's dated note), so they are not an invariant.
rewriteIntegrationTests :: Corpus -> IO TestTree
rewriteIntegrationTests corpus = corpusSweep corpus SweepSpec
  { sweepName = "Slow.RewriteIntegration", sweepTier = Slow, sweepSlow = SkipSlow
  , sweepSelect = rewritePool
  , sweepNote = "agreeing rewritten variants keep agreeing under -O0, topK 0 and branch counting, sample as they measure, and keep main's PType" } $ \e ->
    testCaseInfo (ceName e) $ do
      let n = ceName e; p = ceProgram e; qs = corpusQueries e
      (orig, vs) <- compileSweep p
      origOut <- runCompiled p orig qs
      origBC <- compileTimedWith branchCountConfig p >>= \c -> branchCounts p c qs
      let origPT = mainPTypeOf p
      checked <- concurrently [ integrate n origOut origBC origPT qs v c | (v, c) <- vs ]
      let hard = concat [ h | (h, _, _, _) <- checked ]
          logs = concat [ l | (_, l, _, _) <- checked ]
          matched = concat [ k | (_, _, k, _) <- checked ]
          crossed = length [ () | (_, _, _, True) <- checked ]
          stale = [ k | k <- knownConfigDivergences, kcProg k == n, k `notElem` matched ]
      if not (null hard) then assertFailure (unlines hard) >> return ""
      else if not (null stale)
      then assertFailure (unlines [ "known config divergence no longer observed -- fixed? remove its entry: "
                                    ++ familyName (kcFam k) ++ " at \"" ++ kcSite k ++ "\" under " ++ kcConfig k
                                    ++ " [" ++ kcDoc k ++ "]" | k <- stale ]) >> return ""
      else return $ show (length vs) ++ " variants, " ++ show crossed ++ " agreeing ones crossed"
             ++ concatMap ("\n    " ++) logs

-- | Cross one variant: (hard failures, log lines, the known config
-- divergences it matched, whether it was crossed at all).
integrate :: String -> Outcome -> Maybe [Double] -> Maybe PType -> [Query] -> Variant -> Either String IREnv
          -> IO ([String], [String], [KnownConfig], Bool)
integrate prog origOut origBC origPT qs v c = do
  out <- runCompiled rp c qs
  case (origOut, out, c) of
    (Answered as, Answered bs, Right env) | and (zipWith agrees as bs), isNothing (knownDivergence prog fam site) -> do
      cfgs <- forM integrationConfigs $ \(lbl, conf) -> do
        c' <- compileTimedWith conf rp
        o <- runCompiled rp c' qs
        bc <- if lbl == branchCountLabel then branchCounts rp c' qs else return Nothing
        let problem = case o of
              Answered cs | and (zipWith agrees bs cs) -> Nothing
                          | otherwise -> Just (tag ++ " under " ++ lbl ++ ": " ++ show bs ++ " vs " ++ show cs)
              Refused why -> Just (tag ++ " refuses under " ++ lbl ++ ": " ++ why)
        return (lbl, problem, bc)
      sampled <- samplingCheck rp env (zip qs bs)
      let vBC = case [ bc | (lbl, _, bc) <- cfgs, lbl == branchCountLabel ] of
            (bc : _) -> bc
            [] -> Nothing
          vPT = mainPTypeOf rp
          known = [ (k, m) | (lbl, Just m, _) <- cfgs, Just k <- [knownConfigDivergence prog fam site lbl] ]
          newCfg = [ m | (lbl, Just m, _) <- cfgs, isNothing (knownConfigDivergence prog fam site lbl) ]
          samplingFail = case sampled of
            SampleMismatch m -> [tag ++ ": SAMPLING MISMATCH " ++ m]
            _ -> []
          ptFail = [ tag ++ ": PType of main " ++ show origPT ++ " -> " ++ show vPT | origPT /= vPT ]
          bcLog = [ tag ++ ": branch counts " ++ show origBC ++ " -> " ++ show vBC | origBC /= vBC ]
          knownLog = [ "known: " ++ m ++ " [" ++ kcDoc k ++ "]" | (k, m) <- known ]
      return (newCfg ++ samplingFail ++ ptFail, knownLog ++ bcLog, map fst known, True)
    _ -> return ([], [], [], False)
  where
    fam = variantFamily v
    site = variantSite v
    rp = variantProgram v
    tag = familyName fam ++ " at " ++ site

-- | The branch count at each row, on a 'branchCountConfig' compile, if it
-- answers them all.
branchCounts :: Program -> Either String IREnv -> [Query] -> IO (Maybe [Double])
branchCounts _ (Left _) _ = return Nothing
branchCounts p (Right env) qs = do
  r <- timedTry (20 * 1000000) (evaluate (forceBCs (mapM (\(s, params) -> either (const Nothing) bcOf (runProbC p env params s)) qs)))
  return $ case r of
    Just (Right x) -> x
    _ -> Nothing
  where
    bcOf (VProbDimBC _ _ bc) = Just bc
    bcOf _ = Nothing
    forceBCs m = maybe () (\xs -> sum xs `seq` ()) m `seq` m

-- | The 'PType' at the root of @main@ after the modality stage, if the front
-- end gets that far. Takes the first such snapshot, so the IR stages are not
-- forced.
mainPTypeOf :: Program -> Maybe PType
mainPTypeOf p = case [ q | StageSnapshot _ (StageTyped q _) <- fst (compileStages defaultCompilerConfig p) ] of
  [] -> Nothing
  (q : _) -> pType . getTypeInfo <$> lookup "main" (functions q)

-- | Bump when the rewrite oracle's logic changes.
rewriteCheckVersion :: String
rewriteCheckVersion = "rewrite-invariance-v1"

-- | Key of one program's rewrite sweep: the query rows, and for the original
-- and every variant (by family and site) its runtime fields and its compile
-- as shown, a refusal's message included, with the interpreter fingerprint.
-- This module's and "Rewrites"' sources join the harness. A crash is keyed by
-- its message, as it is deterministic. A compile that timed out, or whose
-- environment crashes or runs out of time while shown, leaves the program
-- without a key, so the sweep runs.
rewriteKey :: Manifest -> Program -> [Query] -> Either String IREnv -> [(Variant, Either String IREnv)] -> IO (Maybe String)
rewriteKey m p qs orig vs
  | any timedOut (orig : map snd vs) = return Nothing
  | otherwise = do
      shown <- mapM renderTimed (orig : map snd vs)
      case sequence shown of
        Nothing -> return Nothing
        Just (o : cs) -> do
          h <- harnessFingerprint m
          src <- sourcesFingerprint m ["test/TestRewrites.hs", "test/Rewrites.hs"]
          i <- interpreterFingerprint m
          return $ Just $ hashKey $
            [rewriteCheckVersion, h, src, i, show qs, programRuntimeFields p, o]
            ++ concat [ [familyName (variantFamily v), variantSite v, programRuntimeFields (variantProgram v), c]
                      | ((v, _), c) <- zip vs cs ]
        Just [] -> return Nothing
  where
    timedOut c = case c of
      Left why -> "timeout" `isPrefixOf` why
      Right _ -> False
    renderTimed c = do
      r <- timedTry (20 * 1000000) (evaluate (let str = show c in length str `seq` str))
      return $ case r of
        Just (Right str) -> Just str
        Just (Left (_ :: SomeException)) -> Nothing
        Nothing -> Nothing

-- ---------------------------------------------------------------------------
-- of-clause toggling
-- ---------------------------------------------------------------------------

-- | Toggling a neural declaration's @of@ clause ('ofToggles') must not change
-- the compile at all: no @of@, @of _@ and the written clause resolve to one
-- annotation before anything reads it (task
-- of-annotation-and-auto-derived-enumeration-divergence), so the oracle here
-- is stricter than the three outcomes: the two 'IREnv's, or the two
-- refusals, must 'show' identically. One test per corpus program with a
-- neural declaration that round-trips. Compile-only, so uncached; a compile
-- that runs out of time is logged.
ofToggleCorpusTests :: Corpus -> IO TestTree
ofToggleCorpusTests corpus = corpusSweep corpus SweepSpec
  { sweepName = "Slow.OfToggleCompilesIdentically", sweepTier = Slow, sweepSlow = SkipSlow
  , sweepSelect = \e -> not (null (ofToggles (ceProgram e)))
  , sweepNote = "removing or writing out a round-tripping of clause compiles to the same IREnv" } $ \e ->
    testCaseInfo (ceName e) $ do
      let p = ceProgram e
      orig <- shownCompile p
      results <- forM (ofToggles p) $ \(lbl, p') -> do
        toggled <- shownCompile p'
        return $ case (orig, toggled) of
          (Just a, Just b) | a == b -> Right Nothing
                           | otherwise -> Left (lbl ++ ": the compile changed")
          _ -> Right (Just (lbl ++ ": timed out (60s), not compared"))
      case [m | Left m <- results] of
        [] -> return (show (length results) ++ " toggles, identical"
                       ++ concatMap ("\n    " ++) [m | Right (Just m) <- results])
        bad -> assertFailure (unlines bad) >> return ""
  where
    shownCompile q = do
      r <- timedTry (60 * 1000000) (evaluate (let s = show (compile defaultCompilerConfig q) in length s `seq` s))
      return $ case r of
        Nothing -> Nothing
        Just (Left (ex :: SomeException)) -> Just ("crash: " ++ show ex)
        Just (Right s) -> Just s
