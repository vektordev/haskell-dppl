{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Fuzz-ish QuickCheck properties over randomly generated SPLL programs.
--
-- Two generators feed these properties (see ArbitrarySPLL.hs):
--
--   * 'genRawFuzzProgram' -- the full Expr/Program AST space (every 'ExprF'
--     constructor, wide Constant leaves, arbitrary identifiers). Almost
--     every draw is ill-typed or otherwise invalid.
--
--   * 'genTypedProgram' -- a narrower, well-typed-by-construction generator
--     (scalar Float/Int/Bool programs built from the same combinators
--     SPLL.Examples hand-writes with) with a low discard rate, used to
--     exercise the actual inference invariants already checked over the
--     hand-written corpus in Spec.hs's Corpus group: P(ANY)=1, topK
--     threshold-0 reproduces exact inference, topK never inflates
--     probability, branch counting doesn't change the probability value, and
--     probability/density is never negative.
--
-- "Compile/generate/probability never crashes" (raises a Haskell exception
-- instead of returning `Left CompilerError`) is checked directly for both
-- generators: for the raw generator, almost every draw is expected to be
-- rejected, so crash-freedom is the *only* invariant that makes sense; for
-- the typed generator it is additionally meaningful on its own (a genuinely
-- well-typed program should never crash the compiler, whether or not that
-- particular shape is supported), which is why it is a separate, unguarded
-- property there rather than folded into the invariant checks below (those
-- swallow a compile-time crash as a discard via 'compileSafe', since
-- crash-freedom on well-typed input is already this module's job, not
-- theirs -- conflating the two would make a topK/branch-counting regression
-- indistinguishable from an unrelated crash in an unsupported IR shape).
--
-- Slow: each well-typed property compiles its drawn program under 2-3
-- CompilerConfigs, so this module lives in the opt-in Slow test group
-- (NEST_SLOW_TESTS=1) rather than the default `stack test` run.
--
-- A further property, 'fuzzSamplingMatchesPDF' (exported via
-- 'superSlowFuzzTests' under the test name "prop_Fuzz_SamplingMatchesPDF"),
-- is central enough to be worth its own even-slower
-- opt-in tier (NEST_SUPERSLOW_TESTS=1): it is the only property here that
-- cross-checks `generate` against `probability` (every other property only
-- cross-checks different CompilerConfigs against each other on the *same*
-- prob function), but doing so needs many forward samples per case, chosen
-- dynamically from the density at the query point (see its docs).
module TestFuzz (fuzzTests, shrinkerTests, superSlowFuzzTests, errorChannelTests,
                 neuralGeneratorTests, fuzzScalingTests, injFCatalogTests) where

import Test.QuickCheck hiding (sample)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperties, testProperty)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool, assertFailure)
import Control.Exception (try, evaluate, throwIO, fromException, SomeException, SomeAsyncException(..))
import Control.Monad (replicateM)
import Control.Monad.Random (evalRandIO)
import System.Timeout (timeout)
import System.Environment (lookupEnv)
import System.IO.Unsafe (unsafePerformIO)
import Text.Read (readMaybe)
import Data.Maybe (isJust)
import Data.List (sort, nub, intersect)
import Data.Number.Erf (erf)

import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.IRCompiler (generateBackedSites)
import SPLL.Prelude
import SPLL.Validator (validateProgram)
import PredefinedFunctions (globalFEnv, parameterCount, FPair(..), applicability)
import SPLL.Lang.Lang (toStub, getTypeInfo)
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Analysis (annotateEnumsProg)
import SPLL.Typing.Infer (addTypeInfo)
import ArbitrarySPLL (genRawFuzzProgram, genTypedProgram, genTypedExpr, Ty(..),
                      InjFSig(..), injFCatalog, injFExcluded, InjFExclusion(..),
                      injFNamesOf, injFLeafApp, tyOfTypedExpr,
                      shrinkTypedProgram, shrinkTypedExpr,
                      tyGeneralizes,
                      typedExprSize, typedExprDepth,
                      LetShape(..), letShapeOf, uniquifyBindersFrom,
                      genNeuralProgram, genNeuralTwinProgram, neuralTwin,
                      typedMainCoreExpr, typedMainCoreTy, hasNeural)

-- | `show`ing a value forces every field, catching lazily-hidden crashes
-- (partial functions/undefined) that a bare WHNF `seq` would miss.
forceShow :: Show a => a -> a
forceShow x = length (show x) `seq` x

-- | Catch only *synchronous* exceptions, re-throwing anything asynchronous
-- (in particular the internal exception 'System.Timeout.timeout' uses to
-- cancel an action it's wrapping). Every use of 'try'/'catch' below runs
-- inside 'withinBudget'/'withinSuperSlowBudget', so a bare
-- 'try :: IO (Either SomeException a)' here would silently swallow the
-- timeout's own cancellation signal -- the action would treat "I was just
-- cancelled" as "the compiler crashed", report 'Nothing', and *keep running
-- the rest of the do-block* instead of actually aborting, defeating the
-- per-case time budget for exactly the slow cases it exists to bound (this
-- was empirically the cause of a single property run taking 529s instead of
-- its ~161-case*1s budget: a handful of topK-configured and/or-heavy
-- programs are genuinely slow to compile, each one running to completion
-- instead of being cut off at 1s).
trySync :: IO a -> IO (Either SomeException a)
trySync act = do
  r <- try act
  case r of
    Left e | Just (SomeAsyncException _) <- fromException e -> throwIO e
    _ -> return r

-- | Compile, catching any synchronous exception rather than letting it
-- propagate as a test failure -- used by the invariant properties below,
-- which care about topK/branch-counting/normalization behaviour on programs
-- that *did* compile, not about crash-freedom (that's
-- 'prop_Fuzz_TypedCompileNeverCrashes'’s job).
compileSafe :: CompilerConfig -> Program -> IO (Maybe IREnv)
compileSafe conf p = do
  r <- trySync (evaluate (forceShow (compile conf p))) :: IO (Either SomeException (Either CompilerError IREnv))
  return $ case r of
    Right (Right irEnv) -> Just irEnv
    _ -> Nothing

-- | The arguments @main@ needs to be run.
--
-- Empty for every draw except a milestone-M3 neural one, whose @main@ takes
-- the symbol its declared network reads. The interpreter substitutes
-- 'MockNN.evaluateMockNN' for the network, whose @(0, seed)@ form produces a
-- random logit vector of exactly the partition plan's width -- so this needs
-- to know nothing about the plan, which is the point: a literal @(2, [...])@
-- vector would have to be sized against a plan this module would then have to
-- recompute for every draw.
--
-- The seed is derived from the declaration rather than drawn. Deriving it
-- keeps a draw's network output fixed under shrinking -- the declaration is
-- the one part of a neural draw the shrinker never touches -- which matters
-- more here than logit variety does: a seed that moved as the program
-- minimized would let the failing behaviour evaporate mid-shrink, which is
-- precisely the "re-run until it reproduces" workflow the shrinker exists to
-- retire. Variety across draws still comes for free, since different target
-- types hash differently and, having different plans, would consume the
-- generator differently regardless.
fuzzArgs :: Program -> [IRValue]
fuzzArgs p = case neurals p of
  []              -> []
  decls@((_, rt, _) : _) -> [VTuple (VInt 0) (VInt (mockSeed (show rt ++ show (length decls))))]

-- | A small deterministic string hash. Any spread will do -- this only has to
-- give different declarations different mock networks.
mockSeed :: String -> Int
mockSeed = foldl (\acc c -> (acc * 33 + fromEnum c) `mod` 100003) 7

drawSample :: Program -> IREnv -> IO IRValue
drawSample p compiled = evalRandIO (runGenC p compiled (fuzzArgs p))

-- 'runProbC'/'runProbNamedC' irrefutably pattern-match on `probFun` being
-- `Just` (SPLL.Prelude:401) -- calling them on a compiled-but-generate-only
-- program (e.g. an If condition built from a non-invertible comparison
-- chain, which is a legitimate program shape, not a malformed one) throws
-- instead of returning `Left`. That's a real gap in the public API, but not
-- what these invariant properties are about, so check for a probability
-- function up front and discard (property True) rather than let it surface
-- as an unrelated crash in every prob-based invariant below.
hasProbFun :: IREnv -> Bool
hasProbFun compiled = isJust (probFun (lookupIREnv "main" compiled))

irProb :: Program -> IREnv -> IRValue -> Maybe IRValue
irProb p compiled sample
  | not (hasProbFun compiled) = Nothing
  | otherwise = either (const Nothing) Just (runProbC p compiled (fuzzArgs p) sample)

hasIntegFun :: IREnv -> Bool
hasIntegFun compiled = isJust (integFun (lookupIREnv "main" compiled))

-- | The CDF at a point, i.e. P(X <= x), used by 'windowP0' below to compute
-- an exact window-hit probability instead of a density*width approximation.
irInteg :: Program -> IREnv -> IRValue -> Maybe Double
irInteg p compiled x
  | not (hasIntegFun compiled) = Nothing
  | otherwise = case runIntegC p compiled (fuzzArgs p) x of
      Right (VProbDim c _) -> Just c
      _ -> Nothing

-- | A properly-discarded QuickCheck test case (via the standard '==>'
-- mechanism, same idiom as 'testSamplingProb' in Spec.hs), for the "this
-- draw had nothing to check" branches below (a crash swallowed by
-- 'compileSafe', a generate-only program with no probFun, ...). Earlier
-- these branches returned a bare 'property True', which silently counts as
-- a real pass; measured empirically (see memory: project_fuzz_quickcheck),
-- ~68% of 'genTypedProgram' draws hit one of these branches, so a bare
-- 'property True' there was inflating the reported success count with
-- vacuous passes instead of surfacing (via QuickCheck's own discard-ratio
-- accounting, visible as "N successes; M discarded" or a "gave up" failure
-- if the ratio gets too extreme) how much of the nominal sample size is
-- actually exercising the invariant.
discardVacuous :: Property
discardVacuous = False ==> True

-- Pulls (prob, dim) out of the standard IRValue result shape, tolerating the
-- countBranches variant's extra third tuple component.
probDim :: IRValue -> Maybe (Double, Double)
probDim (VProbDim pr d) = Just (pr, d)
probDim _ = Nothing

-- | The compiler is not (yet) known to terminate on arbitrary/ill-typed
-- input -- e.g. unification over a self-referential Var/Apply/Lambda soup
-- can loop -- so the crash-freedom properties below bound each draw's
-- wall-clock budget rather than risk hanging the whole Slow group. A timeout
-- is reported as a failure (with its quickcheck-replay seed), same as a
-- crash: a compiler that never terminates on some input is exactly the kind
-- of robustness gap this module exists to surface.
--
-- Was 1s (task fuzz-qc-compiler-bugs, 2026-09-02 review: re-evaluate it,
-- since Slow can afford more than a tight per-case bound). At 1s, a
-- legitimately-terminating topK-guarded and\/or-heavy Int compile (the
-- residual this module's own history already documents -- see
-- IRCompiler's topK-guarded IfThenElse notes) was routinely timing out and
-- being misreported as a hang, which is a false failure, not a finding.
-- Measured directly: replaying the two \'TopKZeroMatchesExact\'\/
-- \'TopKNeverInflates\' seeds recorded against a 1s budget, both completed
-- in 4.2-4.6s once given the room. 5s covers that with margin while keeping
-- a Slow run's aggregate wall-clock bounded (this module has one property,
-- \'MixtureFollowsCombinationRules\', already scaled 10x above this
-- constant). It does not make the timeout vacuous: replaying past-1s
-- failures at a 30s\/300s-scaled budget still produced a genuine
-- non-terminating draw (filed as its own item, not fixed here) rather than
-- merely a slow one, which is exactly the "never terminates" signal this
-- comment already commits to treating as a real failure.
-- ---------------------------------------------------------------------------
-- The depth knob (design typed-program-generator-expansion, Axis 4).
--
-- Structural size and case count are the two dials that decide how much
-- program space a run actually visits, and before this they moved
-- independently: 'fuzzSize' was a source constant (an edit, a rebuild) while
-- the count was a command-line flag ('stack test --ta \'--quickcheck-tests
-- N\''). "Same code, shallow in CI, deep nightly" needed both turned
-- together, so a cron could not express it in one switch.
--
-- 'NEST_FUZZ_SCALE' is that switch: a positive multiplier, default 1,
-- applied to the structural size, to every property's success count, and
-- (upwards only, see 'perCaseBudgetMicros') to the per-case wall-clock
-- budget. It reads the environment once through 'unsafePerformIO' because
-- the things it feeds -- 'resize', 'withMaxSuccess' -- are pure and are
-- evaluated while tasty builds the tree, before any property runs.
--
-- It deliberately scales *down* as well as up, which is not what Axis 4
-- originally asked for. The Slow \'Fuzz\' group does not currently complete on
-- this machine (see docs\/fuzz-testing.md): the draws that hang are the large
-- structured ones, so @NEST_FUZZ_SCALE=0.5@ is the mechanism for getting a
-- verdict out of the already-written oracles while the underlying bugs are
-- drained, rather than having no run at all.
fuzzScaleEnvVar :: String
fuzzScaleEnvVar = "NEST_FUZZ_SCALE"

-- | The unscaled structural size. See 'fuzzSize'.
defaultFuzzSize :: Int
defaultFuzzSize = 12

-- | The unscaled per-case budget. See 'perCaseBudgetMicros'.
defaultPerCaseBudgetMicros :: Int
defaultPerCaseBudgetMicros = 5 * 1000 * 1000

-- | The scaling law, factored out so the default suite can pin it without an
-- environment. Never returns less than 1: a scale small enough to round a
-- count or a size to zero must still run one case at the smallest size, since
-- a silently empty property is indistinguishable from a passing one.
scaleFuzz :: Double -> Int -> Int
scaleFuzz s n = max 1 (round (fromIntegral n * s))

-- | Reading of 'fuzzScaleEnvVar'. Anything that is not a positive, finite
-- number -- unset, empty, unparseable, zero, negative, NaN, infinity --
-- falls back to 1 rather than failing the run: this is a convenience dial on
-- a test suite, and a typo in a cron line should leave the suite doing its
-- ordinary job, not report a fake regression.
parseFuzzScale :: Maybe String -> Double
parseFuzzScale ms = case ms >>= readMaybe of
  Just d | d > 0, not (isNaN d), not (isInfinite d) -> d
  _                                                 -> 1

{-# NOINLINE fuzzScale #-}
fuzzScale :: Double
fuzzScale = parseFuzzScale (unsafePerformIO (lookupEnv fuzzScaleEnvVar))

-- | Scale a property's success count. Every @withMaxSuccess@ in this module
-- goes through this, so one switch moves the whole module's case budget.
fuzzCases :: Int -> Int
fuzzCases = scaleFuzz fuzzScale

-- | The knob's effective setting, for the coverage property's own output.
fuzzScaleLabel :: String
fuzzScaleLabel = show fuzzScale ++ " (size " ++ show fuzzSize ++ ")"

-- The constant itself is 'defaultPerCaseBudgetMicros'; the knob scales it
-- *upwards only*. A deeper run draws bigger programs and needs the room, but
-- a shallower one must not have its budget shrunk with it: the budget exists
-- to tell a hang from a slow draw, and a scaled-down budget would start
-- reporting ordinary draws as hangs, which is the false failure the 1s-to-5s
-- history above already paid for once.
perCaseBudgetMicros :: Int
perCaseBudgetMicros = scaleFuzz (max 1 fuzzScale) defaultPerCaseBudgetMicros

-- | QuickCheck's default size schedule grows 0..~99 across a property's
-- successes; left unbounded, later draws produce deeply nested expressions
-- that can take a long time in RInfer/ModalityInfer/IROptimizer (a couple of
-- genuinely exponential passes have already needed fixing here before, see
-- memory: parser paren backtracking, IROptimizer CSE) even without hitting an
-- actual non-termination bug. 'withinBudget' is the safety net for real
-- hangs; capping structural size keeps ordinary draws fast so a whole
-- property doesn't spend its entire run on a handful of huge programs.
-- Scaled by 'fuzzScaleEnvVar'; the unscaled value is 'defaultFuzzSize'.
fuzzSize :: Int
fuzzSize = scaleFuzz fuzzScale defaultFuzzSize

withinBudget :: IO Property -> IO Property
withinBudget = withinBudgetScaled 1

-- | 'withinBudget' for properties that do more than one compile per draw, so
-- that a slow-but-terminating draw is not reported as a hang.
withinBudgetScaled :: Int -> IO Property -> IO Property
withinBudgetScaled factor act = do
  let budget = factor * perCaseBudgetMicros
  result <- timeout budget act
  return $ case result of
    Just prop -> prop
    Nothing -> counterexample ("did not terminate within " ++ show budget ++ "us") False

-- ---------------------------------------------------------------------------
-- Crash-freedom: the compiler must never throw a Haskell exception, only
-- ever return `Left CompilerError`. `ioProperty` catches exceptions raised
-- inside its IO action and reports them as ordinary test failures, so these
-- properties don't need their own explicit exception handling.

-- | Raw AST space: almost every draw is invalid, so this is the only
-- meaningful invariant. Compiling successfully additionally draws one sample
-- and queries its own probability, exercising the generate/probability code
-- paths too, not just the compile pipeline itself.
prop_Fuzz_CompileNeverCrashes :: Property
prop_Fuzz_CompileNeverCrashes = withMaxSuccess (fuzzCases 40) $ forAll (resize fuzzSize genRawFuzzProgram) $ \p -> ioProperty $ withinBudget $ do
  compiled <- evaluate (forceShow (compile defaultCompilerConfig p))
  case compiled of
    Left _ -> return $ property True
    Right irEnv -> do
      sample <- drawSample p irEnv
      _ <- evaluate (fmap forceShow (runProbC p irEnv (fuzzArgs p) sample))
      return $ property True

-- | Well-typed scalar programs: a stronger, unguarded crash-freedom check
-- (see module header for why this differs from the invariant properties).
prop_Fuzz_TypedCompileNeverCrashes :: Property
prop_Fuzz_TypedCompileNeverCrashes = withMaxSuccess (fuzzCases 40) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudget $ do
  compiled <- evaluate (forceShow (compile defaultCompilerConfig p))
  case compiled of
    Left _ -> return $ property True
    Right irEnv -> do
      sample <- drawSample p irEnv
      _ <- evaluate (fmap forceShow (runProbC p irEnv (fuzzArgs p) sample))
      return $ property True

-- | 'compile' never hands back an 'IREnv' whose probability/integrate/
-- normal/writeLogits bodies draw randomness (task
-- central-generate-backed-prob-body-guard) -- checked here by recomputing
-- 'generateBackedSites' independently of the central guard wired into
-- 'SPLL.IRCompiler.envToIRUnoptimized', which already refuses to *return*
-- such an env by throwing instead. Structurally that makes the "bad" branch
-- below unreachable through the guard as currently wired: this property's
-- real job is as a regression backstop against the guard's wiring coming
-- unstuck (e.g. a future refactor that starts calling the unwrapped
-- 'envToIRUnoptimized'' or otherwise bypasses 'requireNoGenerateBacked')
-- rather than the guard itself, which -- if the wiring ever did slip --
-- would surface as a silently wrong-but-crash-free probability function
-- instead of the loud, targeted counterexample this gives.
--
-- Close to vacuous today, deliberately: 'genTypedProgram' has no 'Apply',
-- 'Lambda', 'let', tuples, ADTs, neural declarations or recursion, and every
-- known generate-backed instance needs at least one of those. It earns its
-- keep once 'typed-program-generator-expansion' lands (tuples + fst/snd is
-- the cheapest addition that reaches instance 4's minimal witness,
-- @fst (Uniform, Uniform * Uniform)@). Cheap in the meantime: unlike the
-- properties below it never draws a sample or calls 'runProbC', so 3000
-- draws is affordable at this module's per-case budget.
prop_Fuzz_ProbNeverGenerateBacked :: Property
prop_Fuzz_ProbNeverGenerateBacked = withMaxSuccess (fuzzCases 3000) $
  forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudget $ do
    r <- trySync (evaluate (forceShow (compile defaultCompilerConfig p)))
    return $ case r of
      Right (Right irEnv) -> case generateBackedSites irEnv of
        []  -> property True
        bad -> counterexample ("GENERATE-BACKED: " ++ show bad ++ "\nPROGRAM: " ++ show p) False
      _ -> property True

-- ---------------------------------------------------------------------------
-- Well-typed scalar fuzzing: the inference invariants.

-- | Every well-typed generated program must pass the validator -- if it
-- doesn't, either the generator or the validator disagrees with the type
-- system about what's well-typed.
prop_Fuzz_TypedProgramsValidate :: Property
prop_Fuzz_TypedProgramsValidate = withMaxSuccess (fuzzCases 200) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p ->
  case validateProgram p of
    Right _ -> property True
    Left err -> counterexample ("well-typed generated program failed validation: " ++ err) False

-- | P(ANY) = 1 for every well-typed generated program that has a probability
-- function at all (some scalar shapes -- e.g. an If condition built from a
-- non-invertible comparison chain -- are legitimately generate-only, and
-- some currently hit unsupported IR shapes, caught by
-- 'prop_Fuzz_TypedCompileNeverCrashes' instead -- both are discarded here).
prop_Fuzz_MarginalAnyIsOne :: Property
prop_Fuzz_MarginalAnyIsOne = withMaxSuccess (fuzzCases 40) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudget $ do
  compiled <- compileSafe defaultCompilerConfig p
  case compiled >>= \irEnv -> irProb p irEnv VAny of
    Nothing -> return discardVacuous
    Just result -> return $ case probDim result of
      Just (pr, _) -> counterexample ("P(ANY) = " ++ show pr ++ ", expected ~1") (abs (pr - 1) < 1e-6)
      Nothing -> counterexample ("unexpected result shape: " ++ show result) False

-- | A probability/density value must never be negative, at a sample point
-- drawn from the program itself (a real distribution assigns non-negative
-- mass/density everywhere; a negative result means the change-of-variables
-- or mixture-combination arithmetic somewhere in IRCompiler has a sign bug).
prop_Fuzz_ProbabilityNeverNegative :: Property
prop_Fuzz_ProbabilityNeverNegative = withMaxSuccess (fuzzCases 40) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudget $ do
  compiled <- compileSafe defaultCompilerConfig p
  case compiled of
    Nothing -> return discardVacuous
    Just irEnv -> do
      sample <- drawSample p irEnv
      return $ case irProb p irEnv sample of
        Nothing -> discardVacuous
        Just result -> case probDim result of
          Just (pr, _) -> counterexample ("P(" ++ show sample ++ ") = " ++ show pr ++ ", expected >= 0") (pr >= -1e-9)
          Nothing -> counterexample ("unexpected result shape: " ++ show result) False

-- | topK with threshold 0 prunes nothing, so it must reproduce exact
-- inference exactly, at a sample point drawn from the program itself.
prop_Fuzz_TopKZeroMatchesExact :: Property
prop_Fuzz_TopKZeroMatchesExact = withMaxSuccess (fuzzCases 40) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudget $ do
  exact <- compileSafe defaultCompilerConfig p
  topK <- compileSafe (defaultCompilerConfig { topKThreshold = Just 0.0 }) p
  case (exact, topK) of
    (Just exactEnv, Just topKEnv) -> do
      sample <- drawSample p exactEnv
      return $ case (irProb p exactEnv sample, irProb p topKEnv sample) of
        (Just exactR, Just topKR) -> case (probDim exactR, probDim topKR) of
          (Just (pe, de), Just (pt, dt)) ->
            counterexample ("exact=" ++ show (pe, de) ++ " topK0=" ++ show (pt, dt))
              (abs (pe - pt) < 1e-6 && abs (de - dt) < 1e-6)
          _ -> counterexample "unexpected result shapes" False
        _ -> discardVacuous  -- one side lacks a prob function: not this property's concern
    _ -> return discardVacuous

-- | Pruning can only zero out branches, never inflate probability above the
-- exact value, at a sample point drawn from the program itself.
prop_Fuzz_TopKNeverInflates :: Property
prop_Fuzz_TopKNeverInflates = withMaxSuccess (fuzzCases 40) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudget $ do
  exact <- compileSafe defaultCompilerConfig p
  topK <- compileSafe (defaultCompilerConfig { topKThreshold = Just 0.1 }) p
  case (exact, topK) of
    (Just exactEnv, Just topKEnv) -> do
      sample <- drawSample p exactEnv
      return $ case (irProb p exactEnv sample, irProb p topKEnv sample) of
        (Just exactR, Just topKR) -> case (probDim exactR, probDim topKR) of
          -- Same rule as Spec's corpus 'topKNeverInflates': values compare
          -- only at equal dim; pruning drops mixture alternatives and the
          -- lowest dim wins, so an unequal pruned dim must be the higher one
          -- (a pruned point mass leaving a sibling density behind).
          (Just (pe, de), Just (pt, dt))
            | dt == de  -> counterexample (show pt ++ " > " ++ show pe ++ " at dim " ++ show de) (pt <= pe + 1e-9)
            | otherwise -> counterexample ("pruned dim " ++ show dt ++ " below exact dim " ++ show de) (dt > de)
          _ -> counterexample "unexpected result shapes" False
        _ -> discardVacuous
    _ -> return discardVacuous

-- | Enabling branch counting must not alter the probability value, only add
-- a third result component, at a sample point drawn from the program itself.
prop_Fuzz_BranchCountingDoesNotChangeProbability :: Property
prop_Fuzz_BranchCountingDoesNotChangeProbability = withMaxSuccess (fuzzCases 40) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudget $ do
  def <- compileSafe defaultCompilerConfig p
  bc <- compileSafe (defaultCompilerConfig { countBranches = True }) p
  case (def, bc) of
    (Just defEnv, Just bcEnv) -> do
      sample <- drawSample p defEnv
      return $ case (irProb p defEnv sample, irProb p bcEnv sample) of
        (Just defR, Just bcR) -> case (probDim defR, probDim bcR) of
          (Just (pd, _), Just (pb, _)) ->
            counterexample ("default=" ++ show pd ++ " bc=" ++ show pb) (abs (pd - pb) < 1e-9)
          _ -> counterexample "unexpected result shapes" False
        _ -> discardVacuous
    _ -> return discardVacuous

-- | The mixture combination rules, checked on pairs of independently generated
-- programs of the SAME type (design inference-result-side-channels; the rules
-- themselves live in 'mixWith').
--
-- For arms A and B and a condition of probability q, the compiled mixture
-- @if bernoulli q then A else B@ must, at any query point x, report exactly:
--
-- >  A impossible at x   ->  ((1-q)*pB, dB)
-- >  B impossible at x   ->  (q*pA,     dA)
-- >  dA < dB             ->  (q*pA,     dA)      -- the lower dimension wins
-- >  dB < dA             ->  ((1-q)*pB, dB)
-- >  otherwise           ->  (q*pA + (1-q)*pB, dA)
--
-- This is the property the old value-based zero test could not state: it had
-- to *guess* "impossible" from a zero probability, which is neither necessary
-- (a structural zero can be any value once guards multiply through) nor
-- sufficient (an underflowed tail density is zero and possible). Reading each
-- arm's own flag makes the rule checkable, and q is kept away from 0 and 1 so
-- that neither arm is impossible merely because its condition cannot hold.
prop_Fuzz_MixtureFollowsCombinationRules :: Property
prop_Fuzz_MixtureFollowsCombinationRules =
  -- Three compiles per draw (both arms and the mixture, which is larger than
  -- either), and the mixture of two if-heavy arms is exactly the shape that
  -- compiles slowly -- hence the generous budget and the reduced draw count.
  -- Occasional draws still exceed it and are reported as failures per this
  -- module's convention; observed failures here have been budget overruns, not
  -- rule violations, so read the counterexample before believing the latter.
  withMaxSuccess (fuzzCases 25) $ forAll genMixturePair $ \(exprA, exprB, q) -> ioProperty $ withinBudgetScaled 10 $ do
    let progA = Program [("main", exprA)] [] [] []
        progB = Program [("main", exprB)] [] [] []
        progM = Program [("main", ifThenElse (bernoulli q) exprA exprB)] [] [] []
    envs <- mapM (compileSafe defaultCompilerConfig) [progA, progB, progM]
    case envs of
      [Just envA, Just envB, Just envM]
        | all hasProbFun [envA, envB, envM] -> do
            x <- drawSample progM envM
            return $ case (runProbC progA envA [] x, runProbC progB envB [] x, runProbC progM envM [] x) of
              (Right resA, Right resB, Right resM)
                | Just (pA, dA) <- probDim resA
                , Just (pB, dB) <- probDim resB
                , Just (pM, dM) <- probDim resM
                , Just impA <- resultImpossible resA
                , Just impB <- resultImpossible resB ->
                    let (expectedP, expectedD)
                          | impA      = ((1 - q) * pB, dB)
                          | impB      = (q * pA,       dA)
                          | dA < dB   = (q * pA,       dA)
                          | dB < dA   = ((1 - q) * pB, dB)
                          | otherwise = (q * pA + (1 - q) * pB, dA)
                    in counterexample
                         ("arms: A=(" ++ show pA ++ ", dim " ++ show dA ++ ", imposs " ++ show impA
                          ++ ") B=(" ++ show pB ++ ", dim " ++ show dB ++ ", imposs " ++ show impB
                          ++ ") q=" ++ show q ++ " at x=" ++ show x
                          ++ "; mixture=(" ++ show pM ++ ", dim " ++ show dM
                          ++ ") expected (" ++ show expectedP ++ ", dim " ++ show expectedD ++ ")")
                         (closeEnough pM expectedP && dM == expectedD)
              _ -> discardVacuous
      _ -> return discardVacuous
  where
    -- Relative tolerance: arm probabilities span many orders of magnitude
    -- (that being the whole point), so an absolute epsilon is meaningless.
    closeEnough got want = abs (got - want) <= 1e-9 * max 1 (abs want)

-- | Two independently generated programs of the same type, plus a mixing
-- probability bounded away from 0 and 1.
genMixturePair :: Gen (Expr, Expr, Double)
genMixturePair = do
  ty <- elements [TyFloat, TyInt, TyBool]
  -- Re-prefixed apart: each arm's own binders are already distinct, but both
  -- draws start numbering at v0, and the mixture program below puts them in
  -- one expression where the validator refuses the collision.
  a  <- uniquifyBindersFrom "va" <$> resize mixtureArmSize (sized (genTypedExpr ty))
  b  <- uniquifyBindersFrom "vb" <$> resize mixtureArmSize (sized (genTypedExpr ty))
  q  <- choose (0.1, 0.9)
  return (a, b, q)

-- | Arms are drawn smaller than 'fuzzSize': the mixture program is larger than
-- both arms combined and gets compiled alongside them, and what this property
-- exercises (how two results combine) does not get more thorough with deeper
-- arms -- it just makes every draw a slow compile.
mixtureArmSize :: Int
mixtureArmSize = 6

-- | Milestone M3's differential oracle, and the only property here whose two
-- sides are different *compilation strategies* rather than different
-- 'CompilerConfig's.
--
-- A neural declaration over a purely discrete target compiles two ways. With
-- no @of@ clause the reads go through plan-guided lazy enumeration, which
-- never builds the joint support -- that is the whole point of it, the corpus'
-- @planEnumInlineWide@ having a 3^12 support. With @of _@ the same declaration
-- gets a 'DiscreteValues' tag and the support is materialized into an
-- @IREnumSum@ instead. The two are the same distribution computed by two
-- engines, so they must agree exactly; the corpus pins this with hand-written
-- @planEnumRec*@/@*Materialized@ file pairs, and here each draw supplies its
-- own pair for free.
--
-- Both sides get the same mock network, because 'fuzzArgs' derives its seed
-- from the declaration and the twin's declaration differs only in the
-- annotation -- which 'mockSeed' does not read. A sample is drawn from the
-- lazy side and both are queried at it, rather than each being sampled: the
-- point is agreement at a point, and two independent samples would compare
-- nothing.
--
-- Discarded rather than failed when only one side compiles: which shapes each
-- engine supports is not this property's subject, and a one-sided refusal is
-- already 'prop_Fuzz_TypedCompileNeverCrashes'' business.
-- | Shrink the pair by shrinking the *lazy* side and re-deriving the twin from
-- it, never the two independently. Shrinking them apart would let the two
-- sides drift into different programs, at which point a disagreement says
-- nothing -- and the twin is a pure function of the lazy side anyway.
--
-- A candidate whose twin no longer exists is dropped rather than paired with
-- itself. 'neuralTwin' returns 'Nothing' exactly when the @of@ flip would stop
-- changing the compilation path, and a pair like that is vacuous.
-- | Twin draws are smaller than 'fuzzSize', for the same reason
-- 'mixtureArmSize' is: what this property exercises -- that two engines agree
-- on one distribution -- does not get more thorough with a deeper program, and
-- every draw costs two compiles. Size matters here more than it does elsewhere
-- because the property *discards* whenever either side fails to reach a
-- probability function, which at milestone M3's measured 73% neural crash rate
-- is most draws; a big draw is both likelier to be discarded and more
-- expensive to discard.
twinSize :: Int
twinSize = 6

shrinkNeuralTwin :: (Program, Program) -> [(Program, Program)]
shrinkNeuralTwin (lazyP, _) =
  [ (l, m) | l <- shrinkTypedProgram lazyP, Just m <- [neuralTwin l] ]

prop_Fuzz_NeuralMaterializedTwinAgrees :: Property
prop_Fuzz_NeuralMaterializedTwinAgrees = withMaxSuccess (fuzzCases 20) $
  forAllShrink (resize twinSize genNeuralTwinProgram) shrinkNeuralTwin $ \(lazyP, matP) -> ioProperty $ withinBudget $ do
    lazyE <- compileSafe defaultCompilerConfig lazyP
    matE  <- compileSafe defaultCompilerConfig matP
    case (lazyE, matE) of
      (Just le, Just me) | hasProbFun le && hasProbFun me -> do
        -- Sampling is guarded, and discards rather than fails, for the same
        -- reason 'compileSafe' swallows a compile crash: whether the IR
        -- interpreter survives a draw is not this property's subject. It is
        -- 'prop_Fuzz_TypedCompileNeverCrashes'' subject, and the specific crash
        -- that reaches here today -- @head@ on an empty list -- is already
        -- filed as item 1 of @fuzz-structured-type-bugs@. Left unguarded, that
        -- one bug masks the oracle entirely: the property died on it after
        -- eight draws without ever comparing the two engines.
        drawn <- trySync $ do
          sample <- drawSample lazyP le
          -- Forced here, inside the guard, and not left to the pure `case`
          -- below: 'irProb' only converts a `Left` into `Nothing`, so an
          -- *exception* raised while evaluating either side would otherwise
          -- escape the guard and fail the property from outside it.
          evaluate (forceShow (sample, irProb lazyP le sample, irProb matP me sample))
        return $ case drawn of
         Left _ -> discardVacuous
         Right (sample, lazyR, matR) -> case (lazyR, matR) of
          (Just lr, Just mr) -> case (probDim lr, probDim mr) of
            (Just (pl, dl), Just (pm, dm)) ->
              counterexample
                ("at x=" ++ show sample
                 ++ ": lazy plan=(" ++ show pl ++ ", dim " ++ show dl
                 ++ ") materialized=(" ++ show pm ++ ", dim " ++ show dm ++ ")")
                (abs (pl - pm) <= 1e-9 * max 1 (abs pm) && dl == dm)
            _ -> counterexample "unexpected result shapes" False
          _ -> discardVacuous
      _ -> return discardVacuous

-- ---------------------------------------------------------------------------
-- Generator coverage instrumentation.
--
-- Design: typed-program-generator-expansion, Axis 3 / milestone M-I.
--
-- Without this, a generator that silently collapses to a single shape after a
-- refactor still produces a full green run: every invariant above holds
-- vacuously on `Normal` alone. The ad-hoc "~55% compile, ~32% have a
-- probability function" figures that motivated the design were a one-time
-- measurement; this makes them a per-run artifact, printed by tasty-quickcheck
-- alongside the property's result.
--
-- Per the design's open question 3 (decided 2026-09-16: "observe first, but do
-- some very conservative bounds that at least spot out a warning"), the
-- thresholds are 'cover' *without* 'checkCoverage': QuickCheck prints
-- "Only N% ..., but expected M%" when one is missed and the property still
-- passes. They are set well under the measured rates, so a miss means the
-- generator really has narrowed, not that a bound was optimistic.

-- | What became of one generated draw. Ordered worst-to-best so the 'cover'
-- bounds below can be stated as ">= this rung".
data DrawOutcome
  = ValidateFailed     -- ^ 'validateProgram' rejected it (should not happen)
  | CompileTimedOut    -- ^ the compiler did not finish inside the per-case budget
  | CompileCrashed     -- ^ the compiler threw instead of returning 'Left'
  | CompileRejected    -- ^ an honest 'Left CompilerError'
  | CompiledNoProbFun  -- ^ compiled, but generate-only
  | CompiledWithProbFun
  deriving (Show, Eq, Ord)

-- | Force a value under both guards this property needs: a synchronous
-- exception or an overrun of the per-case budget yields @fallback@ instead of
-- propagating.
--
-- The timeout half matters as much as the exception half, and for the same
-- reason. A draw that does not terminate is a finding -- but it is
-- 'prop_Fuzz_TypedCompileNeverCrashes'' finding, reported there as a failure
-- with a shrunk counterexample. Here it used to abort the whole run, losing
-- every tabulated row gathered up to that point; a property whose entire
-- purpose is to report a distribution cannot be the one that dies of a single
-- draw. There is at least one such draw in the current generator's range (the
-- structured-shape compile blowup tracked as @fuzz-structured-type-bugs@), so
-- this is not a hypothetical.
guardedBy :: Show a => a -> a -> IO a
guardedBy fallback x = do
  r <- timeout perCaseBudgetMicros (trySync (evaluate (forceShow x)))
  return $ case r of
    Just (Right v) -> v
    _              -> fallback

classifyDraw :: Program -> IO DrawOutcome
classifyDraw p = do
  -- 'validateProgram' is guarded too: it walks the same AST, so "the validator
  -- itself threw" is still a crashing draw, and classifying it is this
  -- function's whole job.
  v <- timeout perCaseBudgetMicros (trySync (evaluate (forceShow (validateProgram p))))
  case v of
    Nothing               -> return CompileTimedOut
    Just (Left _)         -> return CompileCrashed
    Just (Right (Left _)) -> return ValidateFailed
    Just (Right (Right _)) -> do
      r <- timeout perCaseBudgetMicros
             (trySync (evaluate (forceShow (compile defaultCompilerConfig p))))
      return $ case r of
        Nothing                -> CompileTimedOut
        Just (Left _)          -> CompileCrashed
        Just (Right (Left _))  -> CompileRejected
        Just (Right (Right e)) | hasProbFun e -> CompiledWithProbFun
                               | otherwise    -> CompiledNoProbFun

-- | Force one tabulate axis inside an exception guard, substituting @fallback@
-- if it throws.
--
-- 'prop_Fuzz_GeneratorCoverage' used to evaluate its axes outside any guard,
-- and one of them -- 'realizedPTypeLabel', via @addTypeInfo (annotateProg ...)@
-- -- reaches the compile-time constant folding in
-- 'PredefinedFunctions.propagateValues'. A draw whose *compilation* was
-- correctly classified as 'CompileCrashed' could therefore still kill the
-- whole property while being labelled. The property's contract is to classify
-- every draw, so a crash in an axis has to become a label
-- (task compiler-throws-instead-of-returning-left, defect 3).
guardAxis :: Show a => a -> a -> IO a
guardAxis = guardedBy

-- | The label 'guardAxis' substitutes for an axis that threw. It is a visible
-- row in the tabulation rather than a silent fallback: a run where these show
-- up is telling you something.
crashedAxis :: String
crashedAxis = "<crashed>"

-- | Everything 'prop_Fuzz_GeneratorCoverage' tabulates about a single draw,
-- with every axis already forced under 'guardAxis'. Separated from the
-- property so that "a crashing draw is still fully classified and tabulated"
-- is directly testable (see 'coverageGuardTests') rather than only observable
-- as the property not blowing up.
data DrawSummary = DrawSummary
  { dsOutcome        :: DrawOutcome
  , dsPTypeLabel     :: String
  , dsShapeLabel     :: String
  , dsTargetTyLabel  :: String
  , dsTopConstructor :: String
  , dsSize           :: Int
  , dsDepth          :: Int
  , dsStructured     :: Bool
  , dsLetShape       :: LetShape
  , dsNeuralLabel    :: String
  } deriving (Show, Eq)

summarizeDraw :: Program -> IO DrawSummary
summarizeDraw p = do
  outcome <- classifyDraw p
  let body = mainBodyOf p
  DrawSummary outcome
    <$> guardAxis crashedAxis (realizedPTypeLabel p)
    <*> guardAxis crashedAxis (tyShapeLabel p)
    <*> guardAxis crashedAxis (targetTyLabel p)
    <*> guardAxis crashedAxis (maybe "<no main>" (show . toStub) body)
    <*> guardAxis 0 (maybe 0 typedExprSize body)
    <*> guardAxis 0 (maybe 0 typedExprDepth body)
    <*> guardAxis False (isStructured p)
    <*> guardAxis NoLet (maybe NoLet letShapeOf body)
    <*> guardAxis crashedAxis (neuralLabel p)

-- | The modality pass's verdict on @main@, as a label. This is the axis that
-- catches a collapse into a single inference regime, which the outcome split
-- alone would not: every draw can compile and still all be 'Deterministic'.
realizedPTypeLabel :: Program -> String
realizedPTypeLabel p =
  case addTypeInfo (annotateProg (annotateEnumsProg p)) of
    Left _ -> "<not typed>"
    Right (typed, _) -> case lookup "main" (functions typed) of
      Nothing   -> "<no main>"
      Just body -> show (pType (getTypeInfo body))

-- | The part of @main@ the typed generator owns, and the scope it sits in.
--
-- Not @lookup "main"@: a milestone-M3 neural draw wraps its generated core in
-- a @sym@ lambda and a @let@ binding the network read, neither of which
-- 'tyOfTypedExpr' recovers a type for (the target type lives in the 'Program',
-- not on the node). Reading @main@ directly would report every neural draw as
-- @\<unrecognised\>@ on four separate axes at once.
mainBodyOf :: Program -> Maybe Expr
mainBodyOf = typedMainCoreExpr

-- | Bucketed rather than exact: the point is to see the distribution move, and
-- a hundred singleton rows in the tabulate output would show nothing.
bucket :: Int -> String
bucket n
  | n <= 2    = "1-2"
  | n <= 5    = "3-5"
  | n <= 10   = "6-10"
  | n <= 20   = "11-20"
  | otherwise = ">20"

-- | The generated program's *target type*, as a shape label. This is the axis
-- milestone M1 exists to move: before it, every draw was one of the three
-- scalars. 'tyOfTypedExpr' recovers only what the node itself pins down, so
-- components it leaves free print as @?@ -- that is information, not noise
-- (a draw reported as @Either Float ?@ never observed its right side).
targetTyLabel :: Program -> String
targetTyLabel p
  | isJust (mainBodyOf p) = maybe "<unrecognised>" showTy (typedMainCoreTy p)
  | otherwise             = "<no main>"

showTy :: Ty -> String
showTy TyFloat         = "Float"
showTy TyInt           = "Int"
showTy TyBool          = "Bool"
showTy TyAny           = "?"
showTy (TyTuple a b)   = "(" ++ showTy a ++ ", " ++ showTy b ++ ")"
showTy (TyEither a b)  = "Either " ++ showTy a ++ " " ++ showTy b
showTy (TyList a)      = "[" ++ showTy a ++ "]"

-- | Coarser than 'showTy': just which outer shape the draw landed on, so the
-- scalar/structured split is one readable row rather than a long tail.
tyShapeLabel :: Program -> String
tyShapeLabel p = case typedMainCoreTy p of
  Nothing             -> "<unrecognised>"
  Just TyTuple{}      -> "tuple"
  Just TyEither{}     -> "either"
  Just TyList{}       -> "list"
  Just _              -> "scalar"

-- | Which neural declaration the draw carries, if any, as a label.
--
-- The annotation is the interesting half, not the mere presence of a network:
-- it is what decides whether the reads compile through plan-guided lazy
-- enumeration (@lazy@) or by materializing the support into an @IREnumSum@
-- (@materialized@ / @explicit@). A run where @materialized@ never appears is
-- a run where the milestone-M3 differential oracle never fired.
neuralLabel :: Program -> String
neuralLabel p = case neurals p of
  []                              -> "none"
  [(_, _, Nothing)]               -> "lazy"
  [(_, _, Just MultiAuto)]        -> "materialized (of _)"
  [(_, _, Just MultiDiscretes{})] -> "explicit (of [..])"
  _                               -> "other"

isStructured :: Program -> Bool
isStructured p = tyShapeLabel p `elem` ["tuple", "either", "list"]

prop_Fuzz_GeneratorCoverage :: Property
prop_Fuzz_GeneratorCoverage = withMaxSuccess (fuzzCases 200) $
  -- Four times the per-case budget, because the guards inside 'summarizeDraw'
  -- are per-step: classification may spend one budget in the validator and
  -- another in 'compile', and the realized-pType axis re-runs inference for a
  -- third. The outer bound has to sit above their sum or it would pre-empt
  -- them and lose the labelling they exist to produce.
  forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudgetScaled 4 $ do
    s <- summarizeDraw p
    let outcome = dsOutcome s
        depth   = dsDepth s
    return
      -- What the knob was actually set to. Without this row a nightly run
      -- deep enough to be worth reading cannot be told apart from a default
      -- one in its own output, and the distribution rows below mean
      -- different things at different sizes.
      $ tabulate "fuzz scale"       [fuzzScaleLabel]
      $ tabulate "outcome"          [show outcome]
      $ tabulate "realized pType"   [dsPTypeLabel s]
      $ tabulate "target shape"     [dsShapeLabel s]
      $ tabulate "target type"      [dsTargetTyLabel s]
      $ tabulate "top constructor"  [dsTopConstructor s]
      $ tabulate "let shape"        [show (dsLetShape s)]
      $ tabulate "neural"           [dsNeuralLabel s]
      -- Cross-tabulated, and only over the neural draws. At one draw in five
      -- the neural surface's own outcome split is invisible in the aggregate
      -- "outcome" row above, and that split is the thing M3 is actually about:
      -- whether a generated plan-enumeration program reaches a probability
      -- function or is refused.
      $ tabulate "neural outcome"
          [ dsNeuralLabel s ++ " -> " ++ show outcome | dsNeuralLabel s /= "none" ]
      $ tabulate "node count"       [bucket (dsSize s)]
      $ tabulate "depth"            [bucket depth]
      -- Recorded rates at the time of writing: ~35% reach a probability
      -- function, 100% compile. Both bounds sit far below that.
      $ cover 25 (outcome >= CompiledNoProbFun)   "compiles"
      $ cover 10 (outcome == CompiledWithProbFun) "has a probability function"
      $ cover 10 (depth >= 3)                     "non-trivial structure"
      -- M1's acceptance criterion, standing rather than one-off: the generator
      -- must keep reaching the structured shapes. 'genTy' draws a structured
      -- target ~40% of the time (a 6:2:2:2 split at the top level); 15% is a
      -- deliberately slack floor, per the design's observe-first decision on
      -- thresholds -- it fires on a collapse back to scalars, not on drift.
      $ cover 15 (dsStructured s)                 "structured target type"
      -- M2's acceptance criterion. 'letShapeOf' is a *syntactic* classifier --
      -- it reports which shape was generated, not which engine ran, there
      -- being no hook on 'setWitnessApply' to read. It is a sound proxy for
      -- the second bound nonetheless: a 'WitnessLet' reaches its bound
      -- variable only through a comparison and an @if@, which is exactly the
      -- shape forward chaining cannot point-invert, so a witness-shaped draw
      -- that ends up with a probability function got it from the set-witness
      -- engine and from nowhere else.
      $ cover 10 (dsLetShape s /= NoLet)          "contains a let"
      $ cover 1  (dsLetShape s == WitnessLet
                  && outcome == CompiledWithProbFun)
                 "witness-shaped let reaches a probability function"
      -- M3's acceptance criterion, same observe-first shape as the two above.
      -- 'genTypedProgram' draws a neural program one time in five, and the two
      -- materializing annotations are 4/7 of those, so both bounds are set
      -- well under the nominal rate. A miss means the neural production has
      -- stopped firing, which no other axis would show.
      $ cover 8  (dsNeuralLabel s /= "none")     "declares a neural network"
      $ cover 3  (dsNeuralLabel s == "materialized (of _)"
                  || dsNeuralLabel s == "explicit (of [..])")
                 "neural draw that materializes its support"
      $ property True

return []

fuzzTests :: TestTree
fuzzTests = testGroup "Fuzz" [testProperties "properties" $(allProperties)]

-- ---------------------------------------------------------------------------
-- Shrinker contract (design typed-program-generator-expansion, milestone M-S).
--
-- These are pure and fast -- no compile, no sampling -- so unlike everything
-- else in this module they belong in the default suite rather than in `Slow`,
-- and Spec.hs wires them there. That matters: the shrinker is what makes every
-- other property in here debuggable, so a break in it must not hide behind an
-- opt-in tier (and `Slow` is documented as known-red, which would hide it).
--
-- Named without the `prop_` prefix so the `$(allProperties)` splice above does
-- not also collect them into the Slow group -- the same mechanism
-- 'fuzzSamplingMatchesPDF' below uses.

-- | Does this expression contain a @Normal@ leaf? Stands in for "this draw
-- exhibits the bug" in the minimization test below.
containsNormal :: Expr -> Bool
containsNormal e = case node e of
  Var "Normal"     -> True
  IfThenElse c t f -> any containsNormal [c, t, f]
  InjF _ args      -> any containsNormal args
  _                -> False

-- | The greedy loop QuickCheck itself runs: repeatedly take the first shrink
-- that still exhibits the failure, until none does.
minimizeBy :: (Expr -> Bool) -> Expr -> Expr
minimizeBy p e = case filter p (shrinkTypedExpr e) of
  (e' : _) -> minimizeBy p e'
  []       -> e

mainBody :: Program -> Maybe Expr
mainBody p = lookup "main" (functions p)

-- | A deliberately bulky well-typed draw with a single @Normal@ buried four
-- levels down. Minimizing it under "still contains a Normal" must reach the
-- bare leaf -- this is the design's M-S acceptance criterion ("minimizes to a
-- <5-node program automatically") pinned deterministically, rather than by
-- reverting a fix in a sandbox.
buriedNormal :: Expr
buriedNormal =
  ifThenElse (uniform #<# constF 0.5)
    (((normal #+# constF 1.0) #*# (uniform #-# constF 2.0)) #+# expF (constF 3.0))
    (negF (uniform #*# constF 4.0))

-- | The type-preservation contract, stated over *recovered* types.
--
-- Before M1 this was equality, which is what it still amounts to for the
-- scalar fragment. Structured types made recovery partial: a @left x@ node
-- fixes only the left component of its Either and says nothing about the
-- right, so the recovered type carries 'TyAny' there. Replacing an
-- @Either (Bool,Float) (Either Float Float)@ node (a type only pinned by
-- *both* arms of an enclosing if) with @left (False, 0.0)@ is a perfectly
-- well-typed shrink whose recovered type is strictly more general.
--
-- So the contract is directional: the shrink's type must be at least as
-- *general* as the original's. It was stated as symmetric joinability until
-- M2, which is weaker than intended and let a genuinely type-changing
-- reduction through -- see 'tyGeneralizes'.
compatibleTys :: Maybe Ty -> Maybe Ty -> Bool
compatibleTys (Just a) (Just b) = a `tyGeneralizes` b
compatibleTys Nothing  Nothing  = True
compatibleTys _        _        = False

-- ---------------------------------------------------------------------------
-- The neural generator's contract (milestone M3).
--
-- Pure and fast -- these validate and inspect, they never compile -- so like
-- the shrinker contract above they live in the default suite. What they pin is
-- the machinery the M3 properties depend on being *correct* about, as distinct
-- from what those properties measure: that a neural draw is a program the
-- validator accepts, that its generated core is still recoverable and so still
-- shrinks, and that shrinking never quietly turns a neural draw into an
-- ordinary one -- which would minimize a plan-enumeration counterexample into
-- a program that no longer reaches the engine, and report it as the same bug.

-- | The node count of the part of a draw the generator owns, which is what the
-- shrinker actually reduces. Zero for a program with no recognisable core.
coreSize :: Program -> Int
coreSize = maybe 0 typedExprSize . typedMainCoreExpr

neuralGeneratorTests :: TestTree
neuralGeneratorTests = testGroup "Neural generator"
  [ testProperty "a neural draw validates" $
      forAll (resize fuzzSize genNeuralProgram) $ \p ->
        counterexample (show p) (validateProgram p === Right ())
  , testProperty "a neural draw declares exactly one network, read by main" $
      forAll (resize fuzzSize genNeuralProgram) $ \p ->
        counterexample (show p) (length (neurals p) === 1 .&&. property (hasNeural p))
  , testProperty "a neural draw's core type is recoverable" $
      -- This is the M1/M2 invariant restated for the new shape, and it is
      -- load-bearing rather than cosmetic: an unrecoverable core does not
      -- shrink at all, so a regression here would show up only as
      -- counterexamples quietly getting bigger.
      forAll (resize fuzzSize genNeuralProgram) $ \p ->
        counterexample (show p) (property (isJust (typedMainCoreTy p)))
  , testProperty "shrinking a neural draw keeps it neural and valid" $
      forAll (resize fuzzSize genNeuralProgram) $ \p -> conjoin
        [ counterexample (show p')
            (property (hasNeural p')
             .&&. neurals p' === neurals p
             .&&. validateProgram p' === Right ())
        | p' <- shrinkTypedProgram p ]
  , testProperty "the materializing twin differs only in the of clause" $
      forAll genNeuralTwinProgram $ \(lazyP, matP) ->
        counterexample (show (lazyP, matP)) $
              functions lazyP === functions matP
         .&&. map annOf (neurals lazyP) === [Nothing]
         .&&. map annOf (neurals matP)  === [Just MultiAuto]
  ]
  where annOf (_, _, a) = a

-- ---------------------------------------------------------------------------
-- The depth knob's contract (design typed-program-generator-expansion, Axis 4).
--
-- ---------------------------------------------------------------------------
-- The InjF catalog (design typed-program-generator-expansion, Axis 1).
--
-- Default suite, beside 'Shrinker', 'Error channels' and 'Fuzz scaling', and
-- for the same reason: pure, instant, and upstream of everything else in this
-- module. The whole point of deriving the generator's InjF productions from
-- 'globalFEnv' is that the two cannot drift apart; these tests are what turns
-- "cannot" into "does not", by pinning the partition of 'globalFEnv' into
-- generated and deliberately-excluded. A predefined function added to the
-- compiler lands in one bucket or the other, changes a pinned list, and goes
-- red until someone has decided which it should have been. Without that, the
-- silent outcome is the old one: a new function that is simply never
-- generated, with a full green run.
injFCatalogTests :: TestTree
injFCatalogTests = testGroup "InjF catalog"
  [ testCase "the catalog and the exclusions partition globalFEnv" $ do
      let names    = map fst (globalFEnv [])
          included = nub (map injFName injFCatalog)
          excluded = map fst injFExcluded
      assertEqual "no name is both generated and excluded"
        [] (included `intersect` excluded)
      assertEqual "every predefined function is accounted for"
        (sort names) (sort (included ++ excluded))

  , testCase "the generated scalar fragment is what we think it is" $
      -- Pinned by name. The list is not a specification of what *should* be
      -- generatable -- 'injFCatalog' derives that -- it is a tripwire on
      -- 'PredefinedFunctions' changing under the generator.
      assertEqual "generated InjF names"
        [ "and", "double", "eq", "exp", "gt", "lt", "max", "mult", "multI"
        , "neg", "negI", "not", "or", "plus", "plusI", "recip", "sq" ]
        (sort (nub (map injFName injFCatalog)))

  , testCase "the exclusions are what we think they are, with reasons" $
      -- 'InjFGuarded' is the one that matters for correctness: @log@ and
      -- @sqrt@ are partial on their argument type, and generating them
      -- unguarded would manufacture NaN densities that say nothing about the
      -- compiler. The rest are shape, not safety -- 'genTypedRec' owns the
      -- container productions because they need a target type to drive them.
      assertEqual "excluded InjF names and reasons"
        [ ("Cons", InjFNotScalar), ("TCons", InjFPolyArity)
        , ("apply", InjFPolyArity)
        , ("fromLeft", InjFPolyArity), ("fromLeftPartial", InjFGuarded)
        , ("fromRight", InjFPolyArity), ("fromRightPartial", InjFGuarded)
        , ("fst", InjFPolyArity)
        , ("head", InjFNotScalar)
        , ("isLeft", InjFPolyArity), ("isNull", InjFNotScalar)
        , ("isRight", InjFPolyArity)
        , ("left", InjFPolyArity), ("log", InjFGuarded)
        , ("map", InjFPolyArity), ("mapEither", InjFPolyArity)
        , ("mapLeft", InjFPolyArity)
        , ("right", InjFPolyArity)
        , ("snd", InjFPolyArity), ("sqrt", InjFGuarded)
        , ("tail", InjFNotScalar) ]
        (sort injFExcluded)

  , testCase "every catalog entry is scalar, non-nullary and unconditional" $
      -- The last of these is the safety condition restated as a check on the
      -- result rather than on the derivation, so that loosening
      -- 'injFUnconditional' by accident cannot pass quietly.
      mapM_ (\sig -> do
        let nm = injFName sig
        assertBool (nm ++ " has no arguments") (not (null (injFArgs sig)))
        assertBool (nm ++ " is not scalar")
          (all isScalar (injFArgs sig) && isScalar (injFResult sig))
        assertBool (nm ++ " is guarded and must not be generated")
          (unconditionalFwd nm)) injFCatalog

  , testCase "catalog arity agrees with the compiler's own parameterCount" $
      -- Two independent readings of the same declaration. A disagreement
      -- means 'arrowParts' has misread a contract, which would show up as
      -- generated programs the validator rejects rather than as anything
      -- obviously wrong here.
      mapM_ (\sig ->
        assertEqual ("arity of " ++ injFName sig)
          (parameterCount [] (injFName sig)) (length (injFArgs sig)))
        injFCatalog

  , testCase "type recovery agrees with the catalog on every entry" $
      -- The generation table and the recovery table are the same data read in
      -- two directions (M-S's design note). If they disagree,
      -- 'tyOfTypedExpr' returns 'Nothing' for that shape, the shrinker
      -- declines to shrink it, and every counterexample containing it comes
      -- out full-size -- with nothing failing to say so.
      mapM_ (\sig -> case injFLeafApp sig of
        Nothing -> assertFailure ("no leaf application for " ++ injFName sig)
        Just e  -> assertEqual ("recovered type of " ++ injFName sig)
                     (Just (injFResult sig)) (tyOfTypedExpr e)) injFCatalog

  , testProperty "the generator only ever emits names the compiler defines" $
      withMaxSuccess (fuzzCases 50) $
      forAll (resize fuzzSize genTypedProgram) $ \prog ->
        let defined = map fst (globalFEnv [])
            used    = nub (concatMap injFNamesOf (map snd (functions prog)))
        in counterexample (show (filter (`notElem` defined) used))
             (all (`elem` defined) used)
  ]
  where
    isScalar t = t `elem` [TyFloat, TyInt, TyBool]
    unconditionalFwd nm = case lookup nm (globalFEnv []) of
      Just (FPair fwd _) -> applicability fwd == IRConst (VBool True)
      Nothing            -> False

-- Default suite, beside 'Shrinker' and 'Error channels', and for the same
-- reason: these are pure and instant, and the knob is upstream of every other
-- property in this module. A knob that silently reads as 1 would turn a
-- nightly deep run into an ordinary one and nothing would go red -- the run
-- would simply pass, shallowly, and the whole point of having the switch would
-- be lost without a symptom. 'parseFuzzScale' and 'scaleFuzz' are split out of
-- 'fuzzScale' precisely so they can be pinned here without an environment.
fuzzScalingTests :: TestTree
fuzzScalingTests = testGroup "Fuzz scaling"
  [ testProperty "an absent, empty or unparseable setting reads as 1" $ once $
      conjoin [ counterexample (show inp) (parseFuzzScale inp === 1)
              | inp <- [Nothing, Just "", Just "  ", Just "abc", Just "2x"] ]
  , testProperty "a non-positive or non-finite setting reads as 1" $ once $
      -- Zero and negatives would scale every count to the 'scaleFuzz' floor,
      -- which is a silently near-empty suite; "1e400" parses as Infinity and
      -- would make 'round' meaningless. All are typos, so all fall back.
      conjoin [ counterexample (show inp) (parseFuzzScale inp === 1)
              | inp <- [Just "0", Just "-1", Just "-0.5", Just "1e400"] ]
  , testProperty "a positive setting is taken at face value" $ once $
      conjoin [ counterexample inp (parseFuzzScale (Just inp) === want)
              | (inp, want) <- [("1", 1), ("2", 2), ("0.5", 0.5), ("4.0", 4)] ]
  , testProperty "scale 1 is the identity on the defaults" $ once $
           scaleFuzz 1 defaultFuzzSize === defaultFuzzSize
      .&&. scaleFuzz 1 defaultPerCaseBudgetMicros === defaultPerCaseBudgetMicros
  , testProperty "no setting can scale a count away" $
      -- The floor is the whole reason 'scaleFuzz' exists rather than a bare
      -- multiplication: a property that runs zero cases reports as passing.
      forAll (choose (0.001, 100)) $ \sc ->
      forAll (choose (1, 5000)) $ \n ->
        scaleFuzz sc n >= 1
  , testProperty "scaling up never shrinks a count" $
      forAll (choose (0.01, 50)) $ \a ->
      forAll (choose (0.01, 50)) $ \b ->
      forAll (choose (1, 5000)) $ \n ->
        let (lo, hi) = (min a b, max a b)
        in counterexample (show (lo, hi, n)) $ scaleFuzz lo n <= scaleFuzz hi n
  , testProperty "the per-case budget never scales down" $
      -- 'perCaseBudgetMicros' applies @max 1@ to the scale before scaling the
      -- budget, so a shallow run keeps the full budget. Without this a
      -- @NEST_FUZZ_SCALE=0.25@ run would start reporting ordinary draws as
      -- hangs, which is a false failure rather than a finding.
      forAll (choose (0.001, 50)) $ \sc ->
        scaleFuzz (max 1 sc) defaultPerCaseBudgetMicros >= defaultPerCaseBudgetMicros
  ]

-- ---------------------------------------------------------------------------
-- Error-channel regressions (task compiler-throws-instead-of-returning-left).
--
-- Fast and deterministic -- one tiny compile and two hand-built programs -- so
-- these belong in the default suite rather than behind NEST_SLOW_TESTS, next
-- to the shrinker contract above. They pin, by construction, the two things
-- 'prop_Fuzz_TypedCompileNeverCrashes' and 'prop_Fuzz_GeneratorCoverage' can
-- only show statistically: that a compile-time failure travels as a value, and
-- that a draw which *does* crash is still classified rather than propagated.

-- | The draw from the sibling investigation: @tail (tail (Cons (left 0) nul))@.
-- Statically empty, so compile-time constant folding reaches the IR
-- interpreter's @tail@ destructor with an empty list. That destructor used to
-- report by 'error', which walked straight past the 'Either' in
-- 'PredefinedFunctions.propagateValues' and out of the compiler.
--
-- Note what is *not* asserted: which of 'Left' or 'Right' comes back. What
-- @head []@/@tail []@ should mean is the open question owned by
-- 'fuzz-structured-type-bugs'; this test is only about the compiler surviving
-- long enough to have an opinion.
staticallyEmptyTailProgram :: Program
staticallyEmptyTailProgram =
  Program [("main", ltail (ltail (cons (left (constI 0)) nul)))] [] [] []

-- | A draw that crashes the compiler no matter how the error channels are
-- wired: the bottom is inside a constant, so every pass that forces it throws.
-- Stands in for "some future compiler crash" in the coverage test below --
-- 'prop_Fuzz_GeneratorCoverage' must classify such a draw, not die of it.
crashingProgram :: Program
crashingProgram =
  Program [("main", constI (error "deliberate crash: this draw crashes the compiler"))] [] [] []

errorChannelTests :: TestTree
errorChannelTests = testGroup "Error channels"
  [ testProperty "compile returns a value on a statically-empty tail" $ once $ ioProperty $ do
      r <- trySync (evaluate (forceShow (compile defaultCompilerConfig staticallyEmptyTailProgram)))
      return $ counterexample (show r) (either (const False) (const True) r)
  , testProperty "a crashing draw is classified, not propagated" $ once $ ioProperty $ do
      r <- trySync (evaluate . forceShow =<< summarizeDraw crashingProgram)
      return $ counterexample (show r) $ case r of
        Left _  -> property False
        -- Both halves matter: the outcome is the tabulated classification,
        -- and 'dsPTypeLabel' is the axis that used to escape the guard --
        -- @realizedPTypeLabel@ throws on this draw, and the property records
        -- that as a row instead of dying of it (defect 3).
        Right s -> dsOutcome s === CompileCrashed .&&. dsPTypeLabel s === crashedAxis
  , testProperty "a tabulate axis that throws becomes a label" $ once $ ioProperty $ do
      lbl <- guardAxis crashedAxis (error "axis blew up" :: String)
      return (lbl === crashedAxis)
  ]

-- | A @let@ whose body never mentions the binding. The shrinker must be able
-- to drop the whole binding, since removing it strands nothing.
deadLet :: Expr
deadLet = letIn "v0" uniform (constF 1.0)

-- | A @let@ whose body does mention the binding. Collapsing to the body would
-- leave @v0@ unbound -- a different, invalid program rather than a smaller one.
liveLet :: Expr
liveLet = letIn "v0" uniform (Expr makeTypeInfo (Var "v0") #+# constF 1.0)

shrinkerTests :: TestTree
shrinkerTests = testGroup "Shrinker"
  -- Stated over the *program* rather than over @main@'s body, because since
  -- M3 the two differ: a neural draw's body is a lambda around a @let@ around
  -- the generated core, and 'shrinkTypedExpr' pointed at that lambda recovers
  -- nothing and offers nothing. Reading the core out ('typedMainCoreTy',
  -- which recovers it in the scope the network binding creates) keeps these
  -- two contracts biting on every draw rather than silently skipping a fifth
  -- of them.
  [ testProperty "every shrink preserves the expression's type" $
      forAll (resize fuzzSize genTypedProgram) $ \p -> conjoin
        [ counterexample (show p' ++ "\n  shrink ty: " ++ show (typedMainCoreTy p')
                          ++ "\n  orig ty:   " ++ show (typedMainCoreTy p))
                         (property (compatibleTys (typedMainCoreTy p') (typedMainCoreTy p)))
        | p' <- shrinkTypedProgram p ]
  , testProperty "every shrink is strictly smaller" $
      forAll (resize fuzzSize genTypedProgram) $ \p -> conjoin
        [ counterexample (show p') (coreSize p' < coreSize p)
        | p' <- shrinkTypedProgram p ]
  , testProperty "every shrunk program still validates" $
      forAll (resize fuzzSize genTypedProgram) $ \p ->
        conjoin [ counterexample (show p') (validateProgram p' === Right ())
                | p' <- shrinkTypedProgram p ]
  , testProperty "a buried Normal minimizes to the bare leaf" $ once $
      let m = minimizeBy containsNormal buriedNormal
      in counterexample (show m)
           (typedExprSize buriedNormal > 10 .&&. typedExprSize m === 1)
  , testProperty "a dead let shrinks away entirely" $ once $
      counterexample (show (shrinkTypedExpr deadLet))
        (property (constF 1.0 `elem` shrinkTypedExpr deadLet))
  , testProperty "a live let is never collapsed onto its body" $ once $
      -- Every candidate must still be a *valid program*: that is the property
      -- an unbound v0 would break, and validation is what would catch it.
      conjoin [ counterexample (show e')
                  (validateProgram (Program [("main", e')] [] [] []) === Right ())
              | e' <- shrinkTypedExpr liveLet ]
  , testProperty "a constructor stack is not stripped a layer" $ once $
      -- @left (right 0)@ recovers as @Either (Either ? Int) ?@ and its argument
      -- @right 0@ as @Either ? Int@. Those two join, so the original
      -- 'tyJoin'-compatibility test admitted the argument as a shrink of the
      -- node -- stripping the @left@ and changing the expression's type. The
      -- asymmetric 'tyGeneralizes' test refuses it.
      let e = left (right (constI 0))
      in counterexample (show (shrinkTypedExpr e))
           (property (right (constI 0) `notElem` shrinkTypedExpr e))
  , testProperty "minimization keeps the failing feature and never grows" $
      forAll (resize fuzzSize genTypedProgram) $ \p ->
        case mainBody p of
          Nothing -> property True
          Just b  -> containsNormal b ==>
            let m = minimizeBy containsNormal b
            in counterexample (show m)
                 (containsNormal m .&&. typedExprSize m <= typedExprSize b)
  ]

-- ---------------------------------------------------------------------------
-- SuperSlow: sampling-vs-PDF self-consistency. Wired up with a plain
-- 'testProperty' rather than the quickcheck-th '$(allProperties)' splice
-- 'fuzzTests' uses above -- that macro scans the whole module for 'prop_'
-- bindings regardless of where the splice sits, so a second splice here
-- would re-collect (and re-run) every property already in 'fuzzTests' too.

-- | How many independent query points are checked per drawn program, all
-- against one *shared* batch of forward samples (see 'sharedBatchSize' /
-- 'runSamplingCheck'). Sampling is the expensive part (every sample is a
-- full interpreter draw through 'generate'); checking one more query point
-- against an already-drawn batch is just a cheap array scan plus one extra
-- 'probability' call, so batching turns one expensive compile+sample round
-- into 'queryPointCount' checks instead of one.
queryPointCount :: Int
queryPointCount = 5

-- | Target expected number of forward-sample "hits" landing in the
-- acceptance window, used to size the shared sample budget (see
-- 'dynamicSampleCount'). Large enough that the binomial estimate's relative
-- standard error (~1/sqrt(targetHits)) gives the z-test below reasonable power.
targetHits :: Double
targetHits = 30

-- | Forward-sample budget bounds. The lower bound keeps very-high-density
-- points (which would otherwise need only a handful of samples) statistically
-- meaningful; the upper bound keeps very-low-density points from blowing the
-- per-case time budget.
minSamples, maxSamples :: Int
minSamples = 200
maxSamples = 50000

-- | Acceptance window half-width for continuous (dim > 0) outputs. Discrete
-- (dim == 0) outputs are matched exactly instead (see 'sampleHit').
continuousEps :: Double
continuousEps = 0.1

-- | How many forward samples are needed so that, if the query point's
-- window-hit probability 'p0' is correct (samples*p0 hits in expectation --
-- 'p0' already folds in the acceptance window, so this is just 'pr' for a
-- discrete dim-0 output, or 'pr*eps^dim' for a continuous one, see
-- 'drawQueryPoints'), the expected hit count is ~'targetHits'. Solving for
-- samples and clamping to [minSamples, maxSamples] is what makes the sample
-- count "dynamic" per the type of the output -- a Bool/Int program and a
-- Float program (and, within Float, a sharply-peaked vs. near-uniform
-- density) all get a sample budget scaled to what they actually need,
-- instead of one fixed count that is wasteful for common cases and too weak
-- for rare ones. When batching several query points (see 'queryPointCount'),
-- the shared batch is sized to the *largest* of their individual needs, so
-- every point ends up adequately (or over-) sampled.
dynamicSampleCount :: Double -> Int
dynamicSampleCount p0
  | p0 <= 0 = maxSamples
  | otherwise = max minSamples (min maxSamples (ceiling (targetHits / p0)))

-- | Does a forward-sampled draw land in the acceptance window around the
-- query point? Exact equality for the discrete leaf types the typed
-- generator produces (Bool, Int); a symmetric epsilon-wide window for Float.
sampleHit :: Double -> IRValue -> IRValue -> Bool
sampleHit _ (VBool expected) (VBool actual) = expected == actual
sampleHit _ (VInt expected) (VInt actual) = expected == actual
sampleHit eps (VFloat expected) (VFloat actual) = abs (actual - expected) <= eps / 2
sampleHit _ _ _ = False

-- | Well-typed scalar fuzzing takes longer here than elsewhere in this module
-- (up to 'maxSamples' forward draws through the interpreter per case), so it
-- gets its own, larger per-case budget -- but kept far short of 30s+: a
-- pathologically slow *compile* (the same class of bug the Fuzz group's
-- "did not terminate" failures already surface, just not yet triggered by
-- one of those particular draws) given a generous budget doesn't just run
-- slow, it can allocate enough within that time to exhaust memory before
-- ever reaching the timeout check -- observed directly while tuning this
-- budget (a 30s cap OOM-killed the whole test process rather than cleanly
-- failing one case).
-- Scaled upwards only, for the same reason as 'perCaseBudgetMicros'.
perCaseSuperSlowBudgetMicros :: Int
perCaseSuperSlowBudgetMicros = scaleFuzz (max 1 fuzzScale) 8000000

withinSuperSlowBudget :: IO Property -> IO Property
withinSuperSlowBudget act = do
  result <- timeout perCaseSuperSlowBudgetMicros act
  return $ case result of
    Just prop -> prop
    Nothing -> counterexample ("did not terminate within " ++ show perCaseSuperSlowBudgetMicros ++ "us") False

-- ---------------------------------------------------------------------------
-- Statistics: classify an empirical hit rate against the compiler's claimed
-- density as significantly Different, confidently Identical (equivalent
-- within a practical margin), or Unclear (neither -- underpowered).

data DensityVerdict = Different | Identical | Unclear deriving (Show, Eq)

-- | Standard normal CDF via the erf identity, same formula already used
-- elsewhere in this codebase for the Gaussian CDF (see IRInterpreter.hs /
-- IROptimizer.hs), so no new numerics dependency beyond the existing 'erf'
-- package.
normalCDF :: Double -> Double
normalCDF x = 0.5 * (1 + erf (x / sqrt 2))

-- | Standard error of an observed rate under the null hypothesis that the
-- true rate is exactly 'p0' -- i.e. a one-sample Wald test against a known
-- reference value (the compiler's claimed window-hit probability), not a
-- two-sample comparison, so using the null variance (rather than the
-- observed pHat's variance) for every test below is the standard choice.
seUnderNull :: Double -> Int -> Double
seUnderNull p0 samples = sqrt (max 1e-12 (p0 * (1 - p0)) / fromIntegral samples)

-- | Two-sided p-value for H0: true window-hit rate = p0.
twoSidedPValue :: Double -> Int -> Double -> Double
twoSidedPValue p0 samples pHat = 2 * (1 - normalCDF (abs z))
  where z = (pHat - p0) / seUnderNull p0 samples

-- | Bonferroni correction across 'queryPointCount' points checked per draw,
-- so the overall false-"Different" rate per *draw* (not per point) stays at
-- 'alphaDifferent' regardless of how many points are batched together.
alphaDifferent :: Double
alphaDifferent = 0.001 / fromIntegral queryPointCount

-- | Two one-sided tests (TOST), each at this level, for the 'Identical'
-- classification: standard TOST practice runs both legs at the same alpha
-- as a single hypothesis test, since together they bound the overall
-- equivalence claim's confidence at 1-alphaEquivalence.
alphaEquivalence :: Double
alphaEquivalence = 0.05

-- | Relative margin (fraction of the claimed rate) within which the
-- empirical rate is considered practically equivalent, not just
-- "not significantly different" -- e.g. 0.2 accepts a +/-20% relative wobble
-- as still matching, so 'Identical' means "confirmed close", not just
-- "failed to prove different".
equivalenceMargin :: Double
equivalenceMargin = 0.2

-- | TOST equivalence test: both one-sided legs (pHat significantly above the
-- lower bound, and significantly below the upper bound) must clear
-- 'alphaEquivalence' for the rate to be classified 'Identical'.
isEquivalent :: Double -> Int -> Double -> Bool
isEquivalent p0 samples pHat = pLower < alphaEquivalence && pUpper < alphaEquivalence
  where
    se = seUnderNull p0 samples
    lo = p0 * (1 - equivalenceMargin)
    hi = p0 * (1 + equivalenceMargin)
    -- H0: true rate <= lo, vs H1: true rate > lo.
    pLower = 1 - normalCDF ((pHat - lo) / se)
    -- H0: true rate >= hi, vs H1: true rate < hi.
    pUpper = normalCDF ((pHat - hi) / se)

-- | Different takes priority (a significant point-null rejection is strong
-- evidence regardless of the equivalence margin); otherwise Identical if
-- TOST confirms equivalence; otherwise Unclear -- not enough evidence either
-- way, which is exactly when 'runSamplingCheck' doubles the batch and retries.
classifyPoint :: Double -> Int -> Double -> (DensityVerdict, Double)
classifyPoint p0 samples pHat
  | pDiff < alphaDifferent = (Different, pDiff)
  | isEquivalent p0 samples pHat = (Identical, pDiff)
  | otherwise = (Unclear, pDiff)
  where pDiff = twoSidedPValue p0 samples pHat

-- ---------------------------------------------------------------------------

-- | A query point to check, with everything 'classifyPoint' needs cached:
-- the sampled value itself, the compiler's claimed density/dimension, the
-- acceptance window half-width, and 'p0' (the derived window-hit
-- probability: 'pr' directly for a discrete dim-0 output, 'pr*eps^dim' for a
-- continuous one).
data QueryPoint = QueryPoint
  { qpSample :: IRValue
  , qpEps    :: Double
  , qpP0     :: Double
  }

-- | Exact window-hit probability P(x - eps/2 <= X <= x + eps/2) via the
-- compiler's own CDF ('irInteg'), rather than approximating it as
-- density*width. The approximation assumes the density is locally constant
-- across the window, which fails right at a distribution's support boundary
-- -- e.g. a 'Uniform' query point drawn near 0: the window extends into
-- negative territory with zero density, so density*width overstates the
-- true window mass, which (empirically, when this was still an
-- approximation) produced a spurious 'Different' verdict purely from the
-- statistical test's own geometry, not a real compiler bug. Falls back to
-- the approximation only if no integrate function is available at all
-- (shouldn't happen for the continuous shapes 'genTypedProgram' produces,
-- since PNormal/PLogNormal/Integrate all guarantee a closed-form CDF -- see
-- CLAUDE.md's PType section -- but 'drawQueryPoints' filters query points
-- via 'irProb', not 'irInteg', so this stays defensive rather than partial).
windowP0 :: Program -> IREnv -> IRValue -> Double -> Double -> Double -> Double
windowP0 p irEnv (VFloat center) pr dim eps =
  case (irInteg p irEnv (VFloat (center - eps / 2)), irInteg p irEnv (VFloat (center + eps / 2))) of
    (Just lo, Just hi) -> max 0 (hi - lo)
    _ -> pr * eps ** dim
windowP0 _ _ _ pr dim eps = pr * eps ** dim

-- | Draw 'n' independent points from 'generate' and keep only the ones the
-- compiler assigns a well-formed, positive density to (a point with claimed
-- density 0 -- e.g. a query landing exactly on another branch's support --
-- carries no meaningful empirical rate to test against). Drawing the points
-- via 'generate' rather than e.g. a deterministic grid keeps them always
-- in-support, mirroring every other property in this module.
drawQueryPoints :: Program -> IREnv -> Int -> IO [QueryPoint]
drawQueryPoints p irEnv n = do
  samples <- replicateM n (drawSample p irEnv)
  return
    [ QueryPoint s eps p0
    | s <- samples
    , Just result <- [irProb p irEnv s]
    , Just (pr, dim) <- [probDim result]
    , pr > 0
    , let eps = if dim == 0 then 0 else continuousEps
    , let p0 = if dim == 0 then pr else windowP0 p irEnv s pr dim eps
    ]

-- | Draw one shared batch of 'batchSize' forward samples and classify every
-- query point against it (see 'queryPointCount' for why sharing one batch
-- across points is worthwhile). If any point comes back 'Different', fail
-- immediately with a full breakdown. Otherwise, if every point is either
-- 'Identical' or we're out of retries, pass (recording each point's verdict
-- via 'tabulate' so a full property run reports the Identical/Unclear split
-- across all draws -- a persistently high Unclear rate would mean the sample
-- budget or equivalence margin needs revisiting). If some points are still
-- 'Unclear' and retries remain, double the batch and try again -- mirrors
-- the retry-doubling in Spec.hs's 'testSamplingProb'.
runSamplingCheck :: Program -> IREnv -> [QueryPoint] -> Int -> Int -> IO Property
runSamplingCheck p irEnv points batchSize retriesLeft = do
  batch <- replicateM batchSize (drawSample p irEnv)
  let classified =
        [ (qp, verdict, pHat, pDiff)
        | qp <- points
        , let hits = length (filter (sampleHit (qpEps qp) (qpSample qp)) batch)
        , let pHat = fromIntegral hits / fromIntegral batchSize
        , let (verdict, pDiff) = classifyPoint (qpP0 qp) batchSize pHat
        ]
      describe (qp, verdict, pHat, pDiff) =
        "sample=" ++ show (qpSample qp) ++ " claimedRate=" ++ show (qpP0 qp)
          ++ " empiricalRate=" ++ show pHat ++ " verdict=" ++ show verdict ++ " p=" ++ show pDiff
      verdictOf (_, v, _, _) = v
  if any ((== Different) . verdictOf) classified
    then return $ counterexample
      ("batchSize=" ++ show batchSize ++ "\n" ++ unlines (map describe classified))
      False
    else if retriesLeft <= 0 || batchSize >= maxSamples || all ((/= Unclear) . verdictOf) classified
      then return $ tabulate "densityMatch verdict" (map (show . verdictOf) classified) (property True)
      -- Clamped to 'maxSamples': without this, doubling on every retry could
      -- overshoot the intended cap exponentially (batchSize*2^maxRetries),
      -- which is what actually ran a case out of memory during testing.
      else runSamplingCheck p irEnv points (min maxSamples (batchSize * 2)) (retriesLeft - 1)

-- | Bounded retries for 'runSamplingCheck': doubling the batch on an
-- 'Unclear' verdict quadruples statistical power (se shrinks with
-- 1/sqrt(samples)) each round, so this many rounds is enough headroom for
-- borderline cases without risking the per-case time budget.
maxRetries :: Int
maxRetries = 4

-- | The central cross-check: the empirical density estimated by forward
-- sampling ('generate') must agree with the analytic density the compiler's
-- probability function reports at the same points. Every other invariant in
-- this module only cross-checks two different CompilerConfigs against each
-- other on the *same* prob function (topK vs exact, BC vs default); this is
-- the only one that checks prob against generate independently, so a bug
-- that made both sides wrong in the same way (e.g. a shared but incorrect
-- InjF derivative table) would slip past every other property here but not
-- this one.
--
-- 'queryPointCount' points are drawn from the program itself via 'generate'
-- (so they are always in-support), then checked together against one shared
-- batch of forward samples sized to the hardest (lowest-density) point among
-- them (see 'drawQueryPoints' / 'runSamplingCheck').
fuzzSamplingMatchesPDF :: Property
fuzzSamplingMatchesPDF = withMaxSuccess (fuzzCases 20) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinSuperSlowBudget $ do
  compiled <- compileSafe defaultCompilerConfig p
  case compiled of
    Nothing -> return discardVacuous
    Just irEnv
      | not (hasProbFun irEnv) -> return discardVacuous
      | otherwise -> do
          points <- drawQueryPoints p irEnv queryPointCount
          case points of
            [] -> return discardVacuous
            _ -> do
              let initialBatch = maximum [dynamicSampleCount (qpP0 qp) | qp <- points]
              runSamplingCheck p irEnv points initialBatch maxRetries

superSlowFuzzTests :: TestTree
superSlowFuzzTests = testGroup "Fuzz" [testProperty "prop_Fuzz_SamplingMatchesPDF" fuzzSamplingMatchesPDF]
