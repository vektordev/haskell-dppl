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
-- Slow: the well-typed invariant properties compile each drawn program, up
-- to four times (once per CompilerConfig the invariants read; see
-- 'invariantsProperty'), so this module lives in the opt-in Slow test group
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
module TestFuzz (fuzzTests, prepareAgreementCase, genAgreementProgram, agreementFuzzSize, aspirationalFuzzTests, shrinkerTests, superSlowFuzzTests, errorChannelTests,
                 neuralGeneratorTests, arrowGeneratorTests, fuzzScalingTests,
                 injFCatalogTests, adtRecursionGeneratorTests, admissionOracleTests) where

import Test.QuickCheck hiding (sample)
import Test.Tasty (TestTree, testGroup, localOption)
import Test.Tasty.QuickCheck (testProperties, testProperty, QuickCheckMaxRatio(..))
import Test.Tasty.HUnit (testCase, assertEqual, assertBool, assertFailure)
import Control.Exception (try, evaluate, throwIO, fromException, SomeException, SomeAsyncException(..))
import Control.Monad (replicateM, unless, void)
import Control.Monad.Random (evalRandIO)
import System.Timeout (timeout)
import System.Environment (lookupEnv)
import System.IO (hPutStrLn, stderr)
import System.IO.Unsafe (unsafePerformIO)
import Control.Concurrent.MVar (MVar, newMVar, modifyMVar)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import Text.Read (readMaybe)
import Data.Maybe (isJust, fromMaybe)
import Data.Either (rights)
import Control.Monad.Random (evalRand)
import System.Random (mkStdGen)
import BackendAgreement (AgreementCase(..), Query(..), interpreterAnswer, anyHoles, offSupport,
                         runPythonBatch, runJuliaBatch, findJulia, renderDisagreement,
                         irEnvConstructs, inferenceBodies)
import End2EndTesting (resolveNeuralParams, networkNames)
import Data.List (sort, nub, intersect, find, isInfixOf, isPrefixOf)
import PrettyPrint (pPrintProg)
import SPLL.Parser (tryParseProgram)
import SPLL.Typing.PType (PType(Bottom))
import AdmissionOracle (Outcome(..), admissionCheck, AdmissionReport(..), Check(..), Mode(..), admitted, violations, overPromises, outcomeBucket, renderViolation)
import Data.Number.Erf (erf)

import SPLL.Lang.Types
import SPLL.Typing.RType (RType(..))
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
                      tyGeneralizes, tyJoin,
                      typedExprSize, typedExprDepth,
                      LetShape(..), letShapeOf, uniquifyBindersFrom,
                      ArrowShape(..), arrowShapeOf, arrowShapeOfProgram,
                      genHelperProgram, typedLeaves,
                      genNeuralProgram, genNeuralTwinProgram, neuralTwin,
                      typedMainCoreExpr, typedMainCoreTy, hasNeural,
                      RecShape(..), recShapeOfProgram, boundaryConstsOfProgram, divisionOfProgram, genRecursiveProgram,
                      withADTs, adtPool, adtPoolNames, mentionsVar, recursionSafe,
                      unguardedProjections, genADTDecls, adtShapes, adtDeclSize, adtLeaf,
                      genMutualADTPair)

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

-- | A draw on which the sampled program itself failed at run time -- a
-- partial destructor out of its domain, e.g. @head (tail [x])@, which is
-- well-typed and so reachable from the typed generator. The interpreter
-- answers it as a 'VError' value rather than a crash (item 1 of
-- @fuzz-structured-type-bugs@). There is no point to query a probability at,
-- so every property below has nothing to check on such a draw.
isRuntimeFailure :: IRValue -> Bool
isRuntimeFailure (VError _) = True
isRuntimeFailure _ = False

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

-- | Draw a sample from @genEnv@ and force the probability computation @k@ at
-- it, both inside the caller's per-case 'timeout' and behind a
-- synchronous-exception guard. 'Nothing' means "this draw had nothing to
-- check"; the caller discards on it.
--
-- Both halves are load-bearing.
--
-- *Forcing.* 'irProb' is pure, so a property that merely returns
-- @return $ case irProb ... of ...@ hands QuickCheck an unforced thunk.
-- 'withinBudgetScaled' wraps 'timeout' around the 'IO Property', and
-- 'ioProperty''s rose tree is forced by the driver *after* that 'timeout' has
-- already returned -- so the whole IR interpretation would run outside the
-- per-case budget, i.e. unbounded, since the whole-property deadline is only
-- consulted at the entry of the *next* case, which a hang never reaches. Only
-- 'compileSafe' would actually be bounded. Forcing here puts 'runProbC' back
-- under the budget. (The same reasoning is written out at
-- 'prop_Fuzz_NeuralMaterializedTwinAgrees', which had it first.)
--
-- *Discarding.* A draw the program itself failed on ('isRuntimeFailure')
-- has no point to query, and is discarded. So is an exception raised while
-- computing the probability, deliberately and consistently with the twin
-- oracle. Crash-freedom of the compile/sample/probability path is
-- 'prop_Fuzz_TypedCompileNeverCrashes'' subject: it draws from the same
-- generator at the same size and calls 'runProbC' on its own sample, so the
-- bug is already reported, loudly and in one place. The invariants are
-- about what the inference engines *compute* on programs that got that far --
-- which is why they already use 'compileSafe', whose whole job is to swallow
-- a compile-time crash for exactly this reason. Failing here as well would
-- redden every invariant for one bug while hiding the one each exists to
-- check behind it, which is the masking the twin oracle's guard was
-- introduced to undo.
forcedProbAt :: Show a => Program -> IREnv -> (IRValue -> a) -> IO (Maybe (IRValue, a))
forcedProbAt p genEnv k = do
  drawn <- trySync $ do
    sample <- drawSample p genEnv
    if isRuntimeFailure sample
      then return Nothing
      else Just <$> evaluate (forceShow (sample, k sample))
  return $ case drawn of
    Left _  -> Nothing
    Right r -> r

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

-- | The largest setting that is taken at face value; anything above it is
-- clamped to it. Rejecting-to-1 would be wrong here (a deliberate 5000 is a
-- typo for nothing, and silently running shallow is the failure mode the knob
-- exists to avoid), but accepting an arbitrary Double is worse than it looks:
-- 'scaleFuzz' rounds @fromIntegral n * s@ into an 'Int', so
-- @NEST_FUZZ_SCALE=1e30@ overflows, and 'scaleFuzz''s @max 1@ catches a
-- negative result but not a wrapped-positive one. A wrapped-negative
-- 'perCaseBudgetMicros' is the sharp end: @System.Timeout.timeout n@ with
-- @n < 0@ never fires, so the per-case bound would be *disabled* by a typo --
-- exactly the "leave the suite doing its ordinary job" promise inverted.
-- 1000 is far past any run anyone would wait for (120000s of property budget)
-- and keeps every product here inside 'Int'.
maxFuzzScale :: Double
maxFuzzScale = 1000

-- | Reading of 'fuzzScaleEnvVar'. Anything that is not a positive, finite
-- number -- unset, empty, unparseable, zero, negative, NaN, infinity --
-- falls back to 1 rather than failing the run: this is a convenience dial on
-- a test suite, and a typo in a cron line should leave the suite doing its
-- ordinary job, not report a fake regression. An absurdly large finite
-- setting is clamped to 'maxFuzzScale' rather than dropped, for the reasons
-- given there.
parseFuzzScale :: Maybe String -> Double
parseFuzzScale ms = case ms >>= readMaybe of
  Just d | d > 0, not (isNaN d), not (isInfinite d) -> min maxFuzzScale d
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

-- ---------------------------------------------------------------------------
-- Two budgets, and they bound different things.
--
-- 'perCaseBudgetMicros' bounds *one case*. That is what tells a hang from a
-- slow draw, and it works: run at a reduced 'NEST_FUZZ_SCALE', a
-- non-terminating draw is caught, reported as a counterexample and shrunk.
--
-- It does not bound the *property*, and the difference is not academic.
-- QuickCheck keeps drawing until it has 'withMaxSuccess' successes or has
-- discarded 'maxDiscardRatio' times as many, and it re-runs the case for
-- every shrink candidate besides. A property that discards most of its draws
-- (the twin oracle discards ~95%: most generated programs have no probability
-- function to compare) and meets a draw that reliably burns its whole per-case
-- budget therefore multiplies the two together. Measured: at scale 1 the twin
-- oracle was abandoned after 40 minutes against a nominal worst case of 18,
-- and a full 'Fuzz' run stalled for over 25 minutes inside a property nothing
-- had changed. The group stopped completing on this machine, which costs more
-- than any single verdict it might have produced -- a test that does not
-- terminate reports nothing at all, and the two already-written oracles
-- ('prop_Fuzz_NeuralMaterializedTwinAgrees', 'fuzzSamplingMatchesPDF') have
-- still never returned one.
--
-- So each property also gets a whole-property wall-clock budget. Once it is
-- spent, remaining cases are *discarded* rather than failed: a discard costs
-- nothing, so the property drains in milliseconds instead of burning a
-- per-case budget per remaining draw, and QuickCheck's own "Gave up! Passed
-- only N tests" is then the verdict. Failing instead would be worse than
-- useless -- every shrink candidate would also be over budget and fail
-- instantly, so the run would report some arbitrary minimal program as the
-- counterexample for what is really a timekeeping event.
--
-- This is a wall-clock bound on a test, so it is machine-dependent in exactly
-- the way the per-case budget already is; that trade was made deliberately
-- there and is made again here for the same reason. The default is set well
-- above what any property needs when it is behaving (the slowest,
-- 'prop_Fuzz_GeneratorCoverage', takes ~11s at scale 1), so hitting it means
-- something is genuinely wrong rather than that the bound was tight.
defaultPropertyBudgetMicros :: Int
defaultPropertyBudgetMicros = 120 * 1000 * 1000

-- | Scaled *upwards only*, on the same reasoning as 'perCaseBudgetMicros': a
-- shallow run must not have its budget shrunk with it, or ordinary draws start
-- being reported as a stall.
propertyBudgetMicros :: Int
propertyBudgetMicros = scaleFuzz (max 1 fuzzScale) defaultPropertyBudgetMicros

-- | Deadline per property name, in monotonic microseconds. An assoc list
-- rather than a 'Map': there are a dozen properties and this is read once per
-- case.
--
-- Process-global and never reset, which is a real constraint on the harness
-- rather than an oversight: this table (and 'exhaustionAnnounced') assumes the
-- test tree is executed at most *once* per process. Run it twice in one
-- process -- @tasty-rerun@, a second 'defaultMain', a future retry option --
-- and every deadline is already in the past on the second pass, so every case
-- of every fuzz property is discarded and the group reports a uniform "gave
-- up" having executed nothing. Nothing in 'Spec.hs' does that today. Anything
-- that starts to must reset both tables between passes (to @[]@) and should
-- key them by pass rather than by name alone if the passes are meant to be
-- independent.
--
-- Both tables are 'MVar's, updated only through 'claimBudget' and
-- 'noteExhaustion', which evaluate the new table completely before releasing
-- it. They used to be 'IORef's updated with 'atomicModifyIORef'', and that
-- deadlocked the Slow Fuzz group in ~20-28% of runs (GHC 9.6.7 and 9.12.4
-- alike). 'atomicModifyIORef'' installs the *unevaluated* application
-- @f old@ and only then forces it, and every property makes its first update
-- in the same ~100us on its own thread. The dozen updates chain into thunks,
-- each built on the previous one and each comparing property-name strings,
-- that several threads evaluate at once. Stack dumps of hung runs showed every
-- test thread blocked on a black hole inside this bookkeeping, before any
-- per-case 'timeout' could start (docs-repo task
-- fuzz-tier-blackhole-deadlock-at-property-start). Under the lock only one
-- thread ever evaluates a table, and no other thread sees one half-evaluated.
{-# NOINLINE propertyDeadlines #-}
propertyDeadlines :: MVar [(String, Word64)]
propertyDeadlines = unsafePerformIO (newMVar [])

-- | Names whose exhaustion has already been announced, so the note is printed
-- once per property rather than once per drained draw.
{-# NOINLINE exhaustionAnnounced #-}
exhaustionAnnounced :: MVar [String]
exhaustionAnnounced = unsafePerformIO (newMVar [])

-- | Record this case against the property's deadline ('budgetStep') and say
-- whether it may run. The new table is forced -- every name and deadline --
-- while 'propertyDeadlines' is held; see that table for why.
claimBudget :: Int -> String -> IO Bool
claimBudget budget name = do
  now <- nowMicros
  modifyMVar propertyDeadlines $ \table -> do
    let (table', ok) = budgetStep budget name now table
    _ <- evaluate (foldr (\(n, d) acc -> length n `seq` d `seq` acc) () table')
    ok' <- evaluate ok
    return (table', ok')

nowMicros :: IO Word64
nowMicros = (`div` 1000) <$> getMonotonicTimeNSec

-- | The pure core of the deadline bookkeeping, split out of
-- 'withinBudgetScaled' so the default suite can pin it without a clock or an
-- environment -- the same reason 'parseFuzzScale' and 'scaleFuzz' are split
-- out of 'fuzzScale'. A budget that silently never fired would let the stall
-- it exists to bound come back unnoticed.
--
-- The first case of a property establishes the deadline and always runs: a
-- budget of zero must still buy one case, or a property could report "gave up"
-- having executed nothing.
budgetStep :: Int -> String -> Word64 -> [(String, Word64)] -> ([(String, Word64)], Bool)
budgetStep budget name now table = case lookup name table of
  Just deadline -> (table, now < deadline)
  Nothing       -> ((name, now + fromIntegral (max 0 budget)) : table, True)

-- | Printed to stderr rather than carried in the property's own output,
-- because a discarded case's 'label'/'counterexample' does not survive into
-- QuickCheck's give-up report -- and "Gave up! Passed only N tests" without
-- this line would leave a reader unable to tell a genuinely picky precondition
-- from a property that ran out of clock.
noteExhaustion :: String -> Int -> IO ()
noteExhaustion name budget = do
  fresh <- modifyMVar exhaustionAnnounced $ \seen ->
    if name `elem` seen
      then return (seen, False)
      else evaluate (length name) >> return (name : seen, True)
  if fresh
    then hPutStrLn stderr
           (name ++ ": property wall-clock budget of " ++ show budget
              ++ "us exhausted; remaining draws are discarded. Raise it with "
              ++ fuzzScaleEnvVar ++ ".")
    else return ()

withinBudget :: String -> IO Property -> IO Property
withinBudget name = withinBudgetScaled name 1

-- | 'withinBudget' for properties that do more than one compile per draw, so
-- that a slow-but-terminating draw is not reported as a hang.
--
-- The name is passed explicitly rather than derived, so that adding a property
-- is a compile error until it has said which budget it draws against.
withinBudgetScaled :: String -> Int -> IO Property -> IO Property
withinBudgetScaled name factor act = do
  hasBudget <- claimBudget propertyBudgetMicros name
  if not hasBudget
    then noteExhaustion name propertyBudgetMicros >> return discardVacuous
    else do
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
prop_Fuzz_CompileNeverCrashes = withMaxSuccess (fuzzCases 40) $ forAll (resize fuzzSize genRawFuzzProgram) $ \p -> ioProperty $ withinBudget "prop_Fuzz_CompileNeverCrashes" $ do
  compiled <- evaluate (forceShow (compile defaultCompilerConfig p))
  case compiled of
    Left _ -> return $ property True
    Right irEnv -> do
      sample <- drawSample p irEnv
      unless (isRuntimeFailure sample) $
        void (evaluate (fmap forceShow (runProbC p irEnv (fuzzArgs p) sample)))
      return $ property True

-- | Well-typed scalar programs: a stronger, unguarded crash-freedom check
-- (see module header for why this differs from the invariant properties).
prop_Fuzz_TypedCompileNeverCrashes :: Property
prop_Fuzz_TypedCompileNeverCrashes = withMaxSuccess (fuzzCases 40) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudget "prop_Fuzz_TypedCompileNeverCrashes" $ do
  compiled <- evaluate (forceShow (compile defaultCompilerConfig p))
  case compiled of
    Left _ -> return $ property True
    Right irEnv -> do
      sample <- drawSample p irEnv
      unless (isRuntimeFailure sample) $
        void (evaluate (fmap forceShow (runProbC p irEnv (fuzzArgs p) sample)))
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
  forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudget "prop_Fuzz_ProbNeverGenerateBacked" $ do
    r <- trySync (evaluate (forceShow (compile defaultCompilerConfig p)))
    return $ case r of
      Right (Right irEnv) -> case generateBackedSites irEnv of
        []  -> property True
        bad -> counterexample ("GENERATE-BACKED: " ++ show bad ++ "\nPROGRAM: " ++ show p) False
      _ -> property True

-- | The admission contract (task @admission-totality-property@): every
-- top-level function the modality engine admits compiles to probability and
-- integrate functions that evaluate, at a point drawn from its own @generate@,
-- to a value or a refusal through the error channel -- never a crash; every
-- function it refuses still generates. See "AdmissionOracle".
--
-- This differs from 'prop_Fuzz_TypedCompileNeverCrashes' in what it reaches
-- and what it tells you. It exercises every top-level function rather than
-- only @main@ (a helper's parameters are filled with canonical values), the
-- integrate variant as well as the probability one, and the existence of each
-- admitted variant; and a failure names the function, its @pType@ and the mode,
-- which is what says which authority -- lattice or IR compiler -- has to move.
--
-- A crash in a family already filed is not a new finding, so
-- 'knownAdmissionCrashes' lists them by message, each with its tracking doc;
-- a draw whose every violation is one of those passes, labelled. Anything
-- else fails. The tabulation is the three-bucket count the task asks for, over
-- the admitted functions' inference evaluations: the "refusal" share is the
-- precision metric of the lattice (an admitted function the IR compiler then
-- refuses is an over-promise in its graceful form).
--
-- Measured at its introduction (2026-10-02): about 12% of draws violate the
-- contract. Nine of the crash families were unfiled and are now
-- (fuzz-admission-oracle-bugs); with them filed, about one random-seed run in
-- eight at the default 200 draws (~10s) still turns up a new one, which is
-- what a failure of this property means: a family to file. Since
-- static-refusals-become-absent-variants the IR compiler's shape refusals
-- (the catch-all "found no way to convert to IR" among them) are absent
-- variants with a recorded reason, so the crash exception list holds only
-- genuine crash families. Such an absent variant of an *admitted* function is
-- a lattice over-promise, a bug of its own: since
-- admission-oracle-promised-variants-present it is the "promised-absent"
-- bucket and fails the property under its own label (LATTICE OVER-PROMISE)
-- unless its refusal reason is a filed family ('knownOverPromises'). Measured
-- then: about half of the admitted inference evaluations are over-promises.
prop_Fuzz_AdmissionTotality :: Property
prop_Fuzz_AdmissionTotality = withMaxSuccess (fuzzCases 200) $
  forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudgetScaled "prop_Fuzz_AdmissionTotality" 4 $ do
    -- Forced inside the timeout so the whole check runs under the budget (see
    -- 'forcedProbAt' for why an unforced result would escape it).
    checked <- timeout (2 * perCaseBudgetMicros) $ do
      r <- admissionCheck defaultCompilerConfig p (fuzzArgs p)
      _ <- evaluate (length (show r))
      return r
    case checked of
      Just report -> return (judge p report)
      Nothing -> do
        -- A draw whose plain compile does not finish either is the filed
        -- compile-time blowup on structured programs, not this contract's
        -- subject (a non-terminating *admitted variant* would be, and still
        -- fails). Asking costs a second budget, but only on the rare timeout.
        compiles <- timeout perCaseBudgetMicros (trySync (evaluate (forceShow (compile defaultCompilerConfig p))))
        return $ case compiles of
          Nothing -> label "compile did not terminate (structured-accessor-compile-blowup)" True
          Just _  -> counterexample ("admission check did not terminate within " ++ show (2 * perCaseBudgetMicros)
                                     ++ "us, though the program compiles in time\nPROGRAM:\n" ++ pPrintProg p) False
  where
   judge p report =
    let (known, new) = partitionKnownAdmission (violations report)
        (knownOver, newOver) = partitionKnownOverPromises (overPromises report)
        evals = case report of
          NotTyped _ -> []
          Checked _ cs -> [ outcomeBucket (ckOutcome c) | c <- cs, admitted (ckPType c)
                                                        , ckMode c `elem` [ModeProbability, ModeIntegrate] ]
        verdict = case report of
          NotTyped _ -> "not typed"
          Checked vs _
            | any (admitted . snd) vs -> "some function admitted"
            | otherwise               -> "every function refused"
    in tabulate "admitted inference evaluations" evals
     $ tabulate "known violation family" [ fam | (_, fam) <- known ]
     $ tabulate "known over-promise family" [ fam | (_, fam) <- knownOver ]
     $ tabulate "over-promise shape" [ overPromiseShape c | c <- overPromises report ]
     $ label verdict
     $ counterexample (unlines (concat
         [ "ADMISSION CONTRACT VIOLATED:" : map renderViolation new | not (null new) ]
         ++ concat [ "LATTICE OVER-PROMISE (admitted, variant refused):" : map renderViolation newOver | not (null newOver) ]
         ++ ["PROGRAM:", pPrintProg p]))
     $ null new && null newOver

-- | Crash families already filed, matched by a substring of the violation's
-- message, each with the open doc tracking it. Every entry names a doc; one
-- that stops matching anything is harmless but should be pruned when its doc
-- closes, since a fixed family that regresses would then hide behind it.
--
-- Most entries are the probability-mode refusal sites that
-- @static-refusals-become-absent-variants@ (phase P1 of @pipeline-coherence@)
-- converts from a compile-killing @error@ into an absent variant. That task
-- empties this part of the list by construction: after it, those sites are no
-- longer exceptions at all. An admitted function with such an absent variant
-- is an over-promise, listed separately ('knownOverPromises').
knownAdmissionCrashes :: [(String, String)]
knownAdmissionCrashes =
  -- The refusal sites of static-refusals-become-absent-variants (the IR
  -- catch-all, set-valued witnesses, the Bottom-argument Apply arm, the InjF
  -- form checks, the generate-backed enumeration guard, the Normal/LogNormal
  -- parameter extractors) are gone from this list: they are absent variants
  -- with a recorded reason now, which the oracle buckets as refusals.
  -- Found once fuzz-admission-oracle-bugs' item 3 exception was lifted (it had
  -- been hiding this under the same message), and filed rather than fixed in
  -- that task.
  [ ("Comparison not implemented for type: TArrow", "function-value-compared-in-probability-mode")
  ]
  -- bare-equality-of-two-neural-reads-crashes ("More than one probabilistic
  -- argument") and single-prob-param-injf-with-no-probabilistic-operand left
  -- with the AnyExcept arm's one-probabilistic-operand guard.
  -- The nine families of fuzz-admission-oracle-bugs and fuzz-let-witness-bugs
  -- item 4 ("inversions solving for") left this list when they were fixed;
  -- their repros are in the ordinary corpus.

-- | Lattice over-promise families already filed: an admitted function whose
-- inference variant the IR compiler refuses ('PromisedAbsent'), matched by a
-- substring of the recorded refusal reason, each with the doc tracking it (task
-- admission-oracle-promised-variants-present). The same rules as
-- 'knownAdmissionCrashes': every entry names a doc, and an entry is pruned
-- when its doc closes.
--
-- Populated by running the property (2026-10-08): one entry per refusal site
-- the fuzz draws reach, each a numbered item of fuzz-admission-over-promises.
-- That makes the needles as coarse as the sites (the IR catch-all covers many
-- unrelated shapes), so what fails the property is an over-promise refused at
-- a site not listed here; the "over-promise shape" tabulation is the finer
-- view. Over-promises were about half of all admitted inference evaluations
-- at their introduction, so this list cannot be emptied entry by entry
-- without a lattice-side fix per family.
knownOverPromises :: [(String, String)]
knownOverPromises =
  [ ("set-valued witness construction failed for the binding of", "fuzz-admission-over-promises")
  , ("found no way to convert to IR", "fuzz-admission-over-promises")
  , ("which NeST refused to compile", "fuzz-admission-over-promises")
  , ("cannot extract Normal params", "fuzz-admission-over-promises")
  , ("does not resolve to a lambda the compiler can see", "fuzz-admission-over-promises")
  , ("reached a generate-backed fallback", "fuzz-admission-over-promises")
  , ("the argument has pType Bottom (no measurable distribution)", "fuzz-admission-over-promises")
  ]


-- | A one-line classification of an over-promise for tabulation: the
-- recorded reason's first line, cut before anything naming a particular
-- program (a bound variable, a callee, a chain name), plus, for the IR
-- catch-all, the refused expression's outermost node.
overPromiseShape :: Check -> String
overPromiseShape Check{ckOutcome = PromisedAbsent why} =
  case breakOnStr ": Expr {" line of
    Just (pre, rest) -> pre ++ " @ " ++ nodeHead rest
    Nothing -> foldr cut line [" for the binding of", " calls ", " (it resolved to", " and the callee (", ". Result type"]
  where
    line = takeWhile (/= '\n') why
    cut needle acc = maybe acc fst (breakOnStr needle acc)
    nodeHead rest = case breakOnStr "node = " rest of
      Just (_, n)
        | "InjF " `isPrefixOf` n -> takeWhile (/= '[') (take 40 n)
        | otherwise -> takeWhile (/= ' ') n
      Nothing -> "?"
    breakOnStr needle = go ""
      where go acc hay | needle `isPrefixOf` hay = Just (reverse acc, drop (length needle) hay)
                       | null hay = Nothing
                       | otherwise = go (head hay : acc) (tail hay)
overPromiseShape c = show (ckOutcome c)

partitionKnownOverPromises :: [Check] -> ([(Check, String)], [Check])
partitionKnownOverPromises = foldr step ([], [])
  where
    step c@Check{ckOutcome = PromisedAbsent why} (ks, ns)
      | (doc : _) <- [ d | (needle, d) <- knownOverPromises, needle `isInfixOf` why ] = ((c, doc) : ks, ns)
    step c (ks, ns) = (ks, c : ns)

partitionKnownAdmission :: [Check] -> ([(Check, String)], [Check])
partitionKnownAdmission = foldr step ([], [])
  where
    step c (ks, ns) = case [ doc | (needle, doc) <- knownAdmissionCrashes, needle `isInfixOf` show (ckOutcome c) ] of
      (doc : _) -> ((c, doc) : ks, ns)
      []        -> (ks, c : ns)

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

-- ---------------------------------------------------------------------------
-- The inference invariants, checked on shared draws.
--
-- Five invariants are checked over 'genTypedProgram': P(ANY) = 1, probability
-- never negative, topK at threshold 0 reproducing exact inference, topK never
-- inflating, and branch counting not changing the probability. Each used to be
-- its own property with its own draw, compiling the default config every time:
-- 8 compiles over 5 draws. Now one property draws a program, compiles it once
-- per 'FuzzConfig' its invariants need, and runs every invariant against that
-- one compile (task fuzz-shared-draw-multi-config-compile).
--
-- Two properties rather than one, split by tier. The three cross-config
-- invariants are aspirational: their topK compiles hit the per-case budget on
-- most seeds (see 'aspirationalFuzzNames'), and in one shared case a hang
-- there would take the two default-config invariants down with it and redden
-- @Slow@. The split costs one extra default compile per pair of draws. Once
-- the topK compiles are fixed, the two lists merge into one property.
--
-- Each invariant stays addressable: a failure's counterexample names the
-- invariant, every case tabulates each invariant's verdict, and shrinking is
-- pinned to the invariant the drawn program broke first ('invariantsProperty').

-- | A compiler configuration an invariant reads.
data FuzzConfig = CfgExact | CfgTopK0 | CfgTopK01 | CfgBranches
  deriving (Show, Eq, Enum, Bounded)

fuzzConfig :: FuzzConfig -> CompilerConfig
fuzzConfig CfgExact    = defaultCompilerConfig
fuzzConfig CfgTopK0    = defaultCompilerConfig { topKThreshold = Just 0.0 }
fuzzConfig CfgTopK01   = defaultCompilerConfig { topKThreshold = Just 0.1 }
fuzzConfig CfgBranches = defaultCompilerConfig { countBranches = True }

-- | The config whose compile serves @c@. The topK cutoff is a runtime
-- parameter (task runtime-parametric-topk-threshold), so both topK configs
-- share one compile and 'rethreshold' picks the cutoff.
compileKey :: FuzzConfig -> FuzzConfig
compileKey CfgTopK0 = CfgTopK01
compileKey c        = c

rethreshold :: FuzzConfig -> IREnv -> IREnv
rethreshold CfgTopK0 = withTopKCutoff 0.0
rethreshold _        = id

-- | What one case gives every invariant: the program, its compile under each
-- requested config ('Nothing' for one not requested or that did not compile),
-- and one point drawn from the exact compile ('Nothing' when there is no exact
-- compile or the draw failed or raised).
data InvariantCase = InvariantCase
  { icProgram :: Program
  , icEnv     :: FuzzConfig -> Maybe IREnv
  , icSample  :: Maybe IRValue
  }

-- | An invariant's verdict on one case. 'Vacuous' is "nothing to check here"
-- (no probability function, a draw that raised, ...), the per-invariant form
-- of 'discardVacuous'.
data Verdict = Holds | Vacuous | Broken String
  deriving Show

data Invariant = Invariant
  { invName    :: String
  , invConfigs :: [FuzzConfig]
  , invCheck   :: InvariantCase -> IO Verdict
  }

-- | Force @x@ inside the per-case budget, then judge it. An exception while
-- forcing is 'Vacuous', on the reasoning in 'forcedProbAt'.
judgeForced :: Show a => a -> (a -> Verdict) -> IO Verdict
judgeForced x judge = do
  r <- trySync (evaluate (forceShow x))
  return $ either (const Vacuous) judge r

holdsIf :: Bool -> String -> Verdict
holdsIf ok msg = if ok then Holds else Broken msg

-- | The probability of a sample under two configs, for the invariants that
-- compare one against the other.
probPairAt :: FuzzConfig -> FuzzConfig -> InvariantCase -> Maybe (IRValue, Maybe IRValue, Maybe IRValue)
probPairAt a b c = do
  s <- icSample c
  ea <- icEnv c a
  eb <- icEnv c b
  return (s, irProb (icProgram c) ea s, irProb (icProgram c) eb s)

-- | P(ANY) = 1 for every well-typed generated program that has a probability
-- function at all (some scalar shapes -- e.g. an If condition built from a
-- non-invertible comparison chain -- are legitimately generate-only, and
-- some currently hit unsupported IR shapes, caught by
-- 'prop_Fuzz_TypedCompileNeverCrashes' instead -- both are vacuous here).
marginalAnyIsOne :: Invariant
marginalAnyIsOne = Invariant "MarginalAnyIsOne" [CfgExact] $ \c ->
  judgeForced (icEnv c CfgExact >>= \e -> irProb (icProgram c) e VAny) $ \r -> case r of
    Nothing -> Vacuous
    Just result -> case probDim result of
      Just (pr, _) -> holdsIf (abs (pr - 1) < 1e-6) ("P(ANY) = " ++ show pr ++ ", expected ~1")
      Nothing -> Broken ("unexpected result shape: " ++ show result)

-- | A probability/density value must never be negative, at a sample point
-- drawn from the program itself (a real distribution assigns non-negative
-- mass/density everywhere; a negative result means the change-of-variables
-- or mixture-combination arithmetic somewhere in IRCompiler has a sign bug).
probabilityNeverNegative :: Invariant
probabilityNeverNegative = Invariant "ProbabilityNeverNegative" [CfgExact] $ \c ->
  judgeForced (icSample c >>= \s -> icEnv c CfgExact >>= \e -> Just (s, irProb (icProgram c) e s)) $ \r -> case r of
    Just (sample, Just result) -> case probDim result of
      Just (pr, _) -> holdsIf (pr >= -1e-9) ("P(" ++ show sample ++ ") = " ++ show pr ++ ", expected >= 0")
      Nothing -> Broken ("unexpected result shape: " ++ show result)
    _ -> Vacuous

-- | topK with threshold 0 prunes nothing, so it must reproduce exact
-- inference exactly, at a sample point drawn from the program itself.
topKZeroMatchesExact :: Invariant
topKZeroMatchesExact = Invariant "TopKZeroMatchesExact" [CfgExact, CfgTopK0] $ \c ->
  judgeForced (probPairAt CfgExact CfgTopK0 c) $ \r -> case r of
    Just (_, Just exactR, Just topKR) -> case (probDim exactR, probDim topKR) of
      (Just (pe, de), Just (pt, dt)) ->
        holdsIf (abs (pe - pt) < 1e-6 && abs (de - dt) < 1e-6)
                ("exact=" ++ show (pe, de) ++ " topK0=" ++ show (pt, dt))
      _ -> Broken "unexpected result shapes"
    _ -> Vacuous  -- one side lacks a prob function, or the draw raised

-- | Pruning can only zero out branches, never inflate probability above the
-- exact value, at a sample point drawn from the program itself.
topKNeverInflates :: Invariant
topKNeverInflates = Invariant "TopKNeverInflates" [CfgExact, CfgTopK01] $ \c ->
  judgeForced (probPairAt CfgExact CfgTopK01 c) $ \r -> case r of
    Just (_, Just exactR, Just topKR) -> case (probDim exactR, probDim topKR) of
      -- Same rule as the corpus 'checkTopKNeverInflates': values compare only
      -- at equal dim; pruning drops mixture alternatives and the lowest dim
      -- wins, so an unequal pruned dim must be the higher one (a pruned point
      -- mass leaving a sibling density behind).
      (Just (pe, de), Just (pt, dt))
        | dt == de  -> holdsIf (pt <= pe + 1e-9) (show pt ++ " > " ++ show pe ++ " at dim " ++ show de)
        | otherwise -> holdsIf (dt > de) ("pruned dim " ++ show dt ++ " below exact dim " ++ show de)
      _ -> Broken "unexpected result shapes"
    _ -> Vacuous

-- | Enabling branch counting must not alter the probability value, only add
-- a third result component, at a sample point drawn from the program itself.
branchCountingDoesNotChangeProbability :: Invariant
branchCountingDoesNotChangeProbability = Invariant "BranchCountingDoesNotChangeProbability" [CfgExact, CfgBranches] $ \c ->
  judgeForced (probPairAt CfgExact CfgBranches c) $ \r -> case r of
    Just (_, Just defR, Just bcR) -> case (probDim defR, probDim bcR) of
      (Just (pd, _), Just (pb, _)) -> holdsIf (abs (pd - pb) < 1e-9) ("default=" ++ show pd ++ " bc=" ++ show pb)
      _ -> Broken "unexpected result shapes"
    _ -> Vacuous

-- | The outcome of one case: out of property budget (discard), out of
-- per-case budget (a hang), or each invariant's verdict.
data CaseOutcome = OutOfBudget | TimedOut Int | Ran [(String, Verdict)]

-- | What a case can fail with. Shrinking is pinned to one of these.
data CaseFailure = Breaks String | Hangs
  deriving (Show, Eq)

caseFailures :: CaseOutcome -> [CaseFailure]
caseFailures OutOfBudget  = []
caseFailures (TimedOut _) = [Hangs]
caseFailures (Ran vs)     = [ Breaks n | (n, Broken _) <- vs ]

-- | Compile @p@ once per config the invariants need, draw one sample from the
-- exact compile, and run every invariant, all inside the per-case budget
-- (scaled by @factor@, as 'withinBudgetScaled') and charged to @name@'s
-- property budget.
runInvariantCase :: String -> Int -> [Invariant] -> Program -> IO CaseOutcome
runInvariantCase name factor invs p = do
  hasBudget <- claimBudget propertyBudgetMicros name
  if not hasBudget
    then noteExhaustion name propertyBudgetMicros >> return OutOfBudget
    else do
      let budget = factor * perCaseBudgetMicros
      result <- timeout budget $ do
        let cfgs = [ c | c <- [minBound .. maxBound], any ((c `elem`) . invConfigs) invs ]
        compiled <- mapM (\k -> (,) k <$> compileSafe (fuzzConfig k) p) (nub (map compileKey cfgs))
        let envOf c = rethreshold c <$> (lookup (compileKey c) compiled >>= id)
        sample <- case envOf CfgExact of
          Nothing -> return Nothing
          Just e -> do
            drawn <- trySync (drawSample p e >>= evaluate . forceShow)
            return $ case drawn of
              Right s | not (isRuntimeFailure s) -> Just s
              _ -> Nothing
        let ic = InvariantCase p envOf sample
        verdicts <- mapM (\inv -> (,) (invName inv) <$> invCheck inv ic) invs
        evaluate (forceShow verdicts)
      return (maybe (TimedOut budget) Ran result)

-- | Draw programs and check @invs@ on each, with @n@ (scaled) successes. A
-- case where every invariant was vacuous is discarded.
--
-- A failing draw is shrunk against the *first* failure it showed (an
-- invariant, or a hang): a shrink candidate counts as failing only if it
-- breaks that same invariant. Otherwise shrinking could walk from one
-- invariant's failure to another's, and the minimal program would no longer
-- witness the bug the draw found. The outer 'forAllBlind' does not shrink;
-- 'shrinking' does, seeded with the drawn program, whose known failure is
-- reported without re-running it (the sample point is random, so a re-run
-- might not reproduce it).
invariantsProperty :: String -> Int -> [Invariant] -> Int -> Property
invariantsProperty = invariantsPropertyOn (resize fuzzSize genTypedProgram)

-- | 'invariantsProperty' over a given generator, so the default suite can pin
-- the shrink-against-one-invariant rule on cheap fake invariants.
invariantsPropertyOn :: Gen Program -> String -> Int -> [Invariant] -> Int -> Property
invariantsPropertyOn gen name factor invs n =
  -- 'idempotentIOProperty', not 'ioProperty': the latter strips the
  -- 'shrinking' tree this returns. The IO runs once per draw either way.
  withMaxSuccess (fuzzCases n) $ forAllBlind gen $ \p -> idempotentIOProperty $ do
    o <- runInvariantCase name factor invs p
    return $ case caseFailures o of
      [] -> case o of
        Ran vs | not (all (isVacuous . snd) vs) ->
          tabulate "invariant verdicts" [ n' ++ ": " ++ verdictKind v | (n', v) <- vs ] (property True)
        _ -> discardVacuous
      fs@(target : _) ->
        counterexample ("the drawn program failed " ++ show fs ++ "; shrinking against " ++ show target) $
          shrinking (\(_, q) -> [ (Nothing, q') | q' <- shrinkTypedProgram q ]) (Just o, p) $ \(known, q) ->
            case known of
              Just o' -> reportFailure target o' q
              Nothing -> ioProperty $ do
                o' <- runInvariantCase name factor invs q
                return $ if target `elem` caseFailures o' then reportFailure target o' q else property True
  where
    isVacuous Vacuous = True
    isVacuous _ = False
    verdictKind Holds = "holds"
    verdictKind Vacuous = "vacuous"
    verdictKind (Broken _) = "broken"

-- | A failing case, labelled with the invariant it is being shrunk against.
reportFailure :: CaseFailure -> CaseOutcome -> Program -> Property
reportFailure target o q =
  counterexample (describe target) $
  counterexample ("all failures on this program: " ++ show (caseFailures o)) $
  counterexample ("PROGRAM:\n" ++ pPrintProg q) False
  where
    describe Hangs = case o of
      TimedOut b -> "hang: did not terminate within " ++ show b ++ "us"
      _          -> "hang"
    describe (Breaks n) = "invariant " ++ n ++ " broken: "
      ++ case o of
           Ran vs | Just (Broken msg) <- lookup n vs -> msg
           _ -> "?"

-- | The default-config invariants, in @Slow@.
prop_Fuzz_SharedDrawInvariants :: Property
prop_Fuzz_SharedDrawInvariants =
  invariantsProperty "prop_Fuzz_SharedDrawInvariants" 1
    [marginalAnyIsOne, probabilityNeverNegative] 40

-- | The cross-config invariants, in @Aspirational@: three compiles per draw
-- (default, topK -- shared by thresholds 0 and 0.1, see 'compileKey' -- and
-- branch counting), at twice the per-case budget of a two-compile property.
prop_Fuzz_SharedDrawConfigInvariants :: Property
prop_Fuzz_SharedDrawConfigInvariants =
  invariantsProperty "prop_Fuzz_SharedDrawConfigInvariants" 2
    [topKZeroMatchesExact, topKNeverInflates, branchCountingDoesNotChangeProbability] 40

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
  withMaxSuccess (fuzzCases 25) $ forAll genMixturePair $ \(exprA, exprB, q) -> ioProperty $ withinBudgetScaled "prop_Fuzz_MixtureFollowsCombinationRules" 10 $ do
    -- 'withADTs': since milestone M4 an arm of any type may build or take
    -- apart a pool ADT internally, and has to declare it.
    let progA = withADTs $ Program [("main", exprA)] [] [] [] []
        progB = withADTs $ Program [("main", exprB)] [] [] [] []
        progM = withADTs $ Program [("main", ifThenElse (bernoulli q) exprA exprB)] [] [] [] []
    envs <- mapM (compileSafe defaultCompilerConfig) [progA, progB, progM]
    case envs of
      [Just envA, Just envB, Just envM]
        | all hasProbFun [envA, envB, envM] -> do
            -- Forced and guarded by 'forcedProbAt' for the reasons given
            -- there: the three 'runProbC' calls are pure, so returning them
            -- inside an unforced 'case' would run all three IR
            -- interpretations *after* the per-case 'timeout' had returned.
            drawn <- forcedProbAt progM envM
                       (\x -> ( runProbC progA envA [] x
                               , runProbC progB envB [] x
                               , runProbC progM envM [] x ))
            return $ case drawn of
              Just (x, (Right resA, Right resB, Right resM))
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
  forAllShrink (resize twinSize genNeuralTwinProgram) shrinkNeuralTwin $ \(lazyP, matP) -> ioProperty $ withinBudget "prop_Fuzz_NeuralMaterializedTwinAgrees" $ do
    lazyE <- compileSafe defaultCompilerConfig lazyP
    matE  <- compileSafe defaultCompilerConfig matP
    case (lazyE, matE) of
      (Just le, Just me) | hasProbFun le && hasProbFun me -> do
        -- Sampling is guarded, and discards rather than fails, for the same
        -- reason 'compileSafe' swallows a compile crash: whether the IR
        -- interpreter survives a draw is not this property's subject. It is
        -- 'prop_Fuzz_TypedCompileNeverCrashes'' subject. Left unguarded, one
        -- such crash masks the oracle entirely: the property once died after
        -- eight draws on @head@ of an empty list (since answered as a
        -- 'VError' draw, discarded below) without ever comparing the two
        -- engines.
        drawn <- trySync $ do
          sample <- drawSample lazyP le
          -- A draw the program itself failed on has nothing to compare.
          if isRuntimeFailure sample then return Nothing else
          -- Forced here, inside the guard, and not left to the pure `case`
          -- below: 'irProb' only converts a `Left` into `Nothing`, so an
          -- *exception* raised while evaluating either side would otherwise
          -- escape the guard and fail the property from outside it.
            Just <$> evaluate (forceShow (sample, irProb lazyP le sample, irProb matP me sample))
        return $ case drawn of
         Left _ -> discardVacuous
         Right Nothing -> discardVacuous
         Right (Just (sample, lazyR, matR)) -> case (lazyR, matR) of
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
-- structured-shape compile blowup tracked as @structured-accessor-compile-blowup@), so
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
  , dsArrowShape     :: ArrowShape
  , dsNeuralLabel    :: String
  , dsADTLabel       :: String
  , dsADTShapes      :: [(String, [String])]
  , dsRecShape       :: RecShape
  , dsBoundaryConsts :: [String]
  , dsDivision       :: String
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
    -- Read off the whole program, not off @main@'s core: a helper draw's
    -- function value is a top-level declaration, and a neural draw's core
    -- sits inside a wrapper this axis has no reason to exclude.
    <*> guardAxis NoArrow (arrowShapeOfProgram p)
    <*> guardAxis crashedAxis (neuralLabel p)
    <*> guardAxis crashedAxis (adtLabel p)
    <*> guardAxis [] (adtShapes (adts p))
    <*> guardAxis NoRec (recShapeOfProgram p)
    <*> guardAxis [crashedAxis] (boundaryConstsOfProgram p)
    <*> guardAxis crashedAxis (divisionOfProgram p)

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
showTy TyUnrecovered   = "<unrecovered>"
showTy (TyTuple a b)   = "(" ++ showTy a ++ ", " ++ showTy b ++ ")"
showTy (TyEither a b)  = "Either " ++ showTy a ++ " " ++ showTy b
showTy (TyList a)      = "[" ++ showTy a ++ "]"
showTy (TyArrow a b)   = showTy a ++ " -> " ++ showTy b
showTy (TyADT n)       = n

-- | Coarser than 'showTy': just which outer shape the draw landed on, so the
-- scalar/structured split is one readable row rather than a long tail.
tyShapeLabel :: Program -> String
tyShapeLabel p = case typedMainCoreTy p of
  Nothing             -> "<unrecognised>"
  Just TyTuple{}      -> "tuple"
  Just TyEither{}     -> "either"
  Just TyList{}       -> "list"
  Just TyADT{}        -> "adt"
  -- Never drawn as a program's target type ('genTy' cannot emit an arrow);
  -- here so that a future one is reported rather than counted as a scalar.
  Just TyArrow{}      -> "arrow"
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
isStructured p = tyShapeLabel p `elem` ["tuple", "either", "list", "adt"]

-- | Which pool ADTs the draw declares, as one label (milestone M4). A draw
-- declares an ADT whenever any of its nodes builds, tests or projects one,
-- whatever its own target type -- so this row, not "target shape", is the one
-- that says how much of the run reached ADT code at all.
--
-- Since task fuzz-generate-adt-declarations most declarations are generated,
-- with names of their own, so the row says where the declarations came from
-- rather than naming them; their shapes are the @adt shape@ and @adt feature@
-- rows ('adtShapes').
adtLabel :: Program -> String
adtLabel p = case (any (`elem` adtPool) (adts p), any (`notElem` adtPool) (adts p)) of
  (False, False) -> "none"
  (True,  False) -> "pool only"
  (False, True)  -> "generated only"
  (True,  True)  -> "pool and generated"

prop_Fuzz_GeneratorCoverage :: Property
prop_Fuzz_GeneratorCoverage = withMaxSuccess (fuzzCases 200) $
  -- Four times the per-case budget, because the guards inside 'summarizeDraw'
  -- are per-step: classification may spend one budget in the validator and
  -- another in 'compile', and the realized-pType axis re-runs inference for a
  -- third. The outer bound has to sit above their sum or it would pre-empt
  -- them and lose the labelling they exist to produce.
  forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinBudgetScaled "prop_Fuzz_GeneratorCoverage" 4 $ do
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
      $ tabulate "arrow shape"      [show (dsArrowShape s)]
      $ tabulate "neural"           [dsNeuralLabel s]
      $ tabulate "adt"              [dsADTLabel s]
      $ tabulate "adt shape"        (map fst (dsADTShapes s))
      $ tabulate "adt feature"      (concatMap snd (dsADTShapes s))
      $ tabulate "recursion"        [show (dsRecShape s)]
      -- Task fuzz-boundary-value-leaves: the constants constant folding and
      -- the zero-operand inverse branches special-case, and division.
      $ tabulate "boundary constant" (dsBoundaryConsts s)
      $ tabulate "division"         [dsDivision s]
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
      -- The arrow axis's acceptance criterion (task
      -- fuzz-arrow-generator-coverage), same observe-first shape as the
      -- others. One draw in five is a 'genHelperProgram', which applies a
      -- named function by construction, so the first bound fires on the
      -- arrow productions disappearing entirely rather than on drift (a third
      -- of draws carry a function value: 33.5% and 35% on two 200-draw runs).
      -- The second bound is deliberately slack against a rate that moves a
      -- lot between runs -- 9% and 16% on those same two -- because what it
      -- guards is categorical: a *computed* callee, an @if@ between two
      -- lambdas or one projected out of a tuple or list, is the shape
      -- 'SPLL.CalleeNormalize' exists for, and a run without one has stopped
      -- testing it.
      $ cover 8  (dsArrowShape s /= NoArrow)      "applies a function value"
      $ cover 3  (dsArrowShape s >= SelectedFun)  "applies a computed function value"
      -- M3's acceptance criterion, same observe-first shape as the two above.
      -- 'genTypedProgram' draws a neural program one time in five, and the two
      -- materializing annotations are 4/7 of those, so both bounds are set
      -- well under the nominal rate. A miss means the neural production has
      -- stopped firing, which no other axis would show.
      $ cover 8  (dsNeuralLabel s /= "none")     "declares a neural network"
      $ cover 3  (dsNeuralLabel s == "materialized (of _)"
                  || dsNeuralLabel s == "explicit (of [..])")
                 "neural draw that materializes its support"
      -- M4's acceptance criterion, same observe-first shape. One draw in six
      -- is a 'genRecursiveProgram', most of whose steps do recurse; ADT nodes
      -- reach far more draws than ADT *targets* do, through the field
      -- projections and constructor tests open at scalar targets.
      $ cover 10 (dsADTLabel s /= "none")       "declares an ADT"
      -- Task fuzz-generate-adt-declarations: the generated declarations
      -- must keep showing up, and must keep reaching the shapes the pool
      -- could not. Observe-first floors again, far below the rates measured
      -- when the task landed (see docs/fuzz-testing.md).
      $ cover 10 (any (notElem "pool" . snd) (dsADTShapes s)) "declares a generated ADT"
      $ cover 5  (dsRecShape s /= NoRec)        "contains a recursive declaration"
      -- Task fuzz-boundary-value-leaves, observe-first floors again. The
      -- Float row is the one that matters (the Int @1@ is mostly generator
      -- scaffolding, a recursion's @n - 1@); a division was in 11.5% of draws
      -- on the 200-draw run that landed it.
      $ cover 15 (any (isInfixOf "Float") (dsBoundaryConsts s)) "contains a Float boundary constant"
      $ cover 4  (dsDivision s /= "none")       "divides"
      $ property True

-- ---------------------------------------------------------------------------
-- Backend agreement (docs-repo task backend-agreement-fuzzing).
--
-- The interpreter is the reference semantics; the scalar Python and Julia
-- backends must give the same @(prob, dim, imposs)@ at every point the
-- interpreter answers. Checked per batch of programs, one backend process per
-- batch (see "BackendAgreement" for the drivers and the comparison). This is
-- the property that lets emitted-code-test-impact-analysis M2 drop the
-- runtimes from its per-program key -- but only for the IR constructs it
-- actually exercises, which is why each run tabulates them.

-- | Programs per batch, and batches per run: 4 x 60 = 240 drawn programs.
-- Only the ones with a probability function the interpreter answers at reach
-- the backends; the "programs compared" row says how many that was.
agreementBatchSize, agreementBatches :: Int
agreementBatchSize = 60
agreementBatches = 4

-- | Wall clock for preparing one program: compile, three forward samples and
-- every interpreter query. A program that does not finish is dropped, not
-- failed: non-termination is 'prop_Fuzz_TypedCompileNeverCrashes'' business
-- (the structured-accessor blowup), and with 60 programs a batch a 5s
-- per-program budget would let a few hangs eat the whole property budget.
agreementPerProgramMicros :: Int
agreementPerProgramMicros = 2 * 1000 * 1000

-- | The structural size 'BackendCoverage''s fixed-seed sample draws at: the
-- unscaled default, so the sample (and the exception list it is checked
-- against) does not move with @NEST_FUZZ_SCALE@.
agreementFuzzSize :: Int
agreementFuzzSize = defaultFuzzSize

-- | The plain typed generator, with the neural and named-helper productions
-- weighted up: those are the shapes with the most backend-specific lowering
-- (identity-mocked network calls, cross-function calls).
genAgreementProgram :: Gen Program
genAgreementProgram = frequency
  [ (4, genTypedProgram)
  , (1, genNeuralProgram)
  , (1, genHelperProgram)
  ]

-- | One batch element: a program and the seed its query points are drawn
-- with, so a shrink candidate is queried reproducibly.
genAgreementBatch :: Gen [(Program, Int)]
genAgreementBatch = vectorOf agreementBatchSize ((,) <$> resize fuzzSize genAgreementProgram <*> arbitrary)

-- | A failing batch is first cut to each program alone -- one of them is the
-- culprit, and QuickCheck stops at the first singleton that still fails --
-- and only a singleton is shrunk structurally. Cutting before shrinking is
-- what the task asks for: a batch shrinks badly, because every candidate
-- re-runs every other program's backend check too.
shrinkAgreementBatch :: [(Program, Int)] -> [[(Program, Int)]]
shrinkAgreementBatch [(p, s)] = [ [(p', s)] | p' <- shrinkTypedProgram p ]
shrinkAgreementBatch xs = map (: []) xs

-- | Compile a program, draw its query points from its own generator, and keep
-- the points the interpreter answers at, with its answers. 'Left' says why a
-- program has nothing to compare (no compile, no probability function, a
-- timeout, or no point the interpreter answers).
--
-- Points: three forward samples, their @ANY@-holed variants and their
-- off-support neighbours ('anyHoles', 'offSupport'), at most 'maxAgreementPoints'
-- of them, at @main@'s probability function -- and at its integrate function
-- for the ones without a wildcard, where it has one.
prepareAgreementCase :: (Program, Int) -> IO (Either String AgreementCase)
prepareAgreementCase (p, seed) = fmap (fromMaybe (Left "timed out")) $ timeout agreementPerProgramMicros $ do
  compiled <- compileSafe defaultCompilerConfig p
  case compiled of
    Nothing -> return (Left "no compile")
    Just env | not (hasProbFun env) -> return (Left "no probability function")
    Just env -> do
      let args = fuzzArgs p
      drawn <- trySync (evaluate (forceShow (evalRand (replicateM 3 (runGenC p env args)) (mkStdGen seed))))
      let samples = [ s | Right ss <- [drawn], s <- ss, queryable s ]
          points = take maxAgreementPoints (nub (samples ++ concatMap anyHoles samples ++ concatMap offSupport samples))
          queries = map QProb points
                    ++ (if hasIntegFun env then [ QInteg v | v <- points, not (hasWildcard v) ] else [])
      answered <- fmap concat $ mapM (\q -> do
                    r <- trySync (evaluate (forceShow (interpreterAnswer p env args q)))
                    return [ (q, a) | Right (Just a) <- [r] ]) queries
      return $ if null answered then Left "interpreter answered no point" else Right AgreementCase
        { acProgram = p, acEnv = env
        , acBackendArgs = resolveNeuralParams p args
        , acNets = networkNames p
        , acQueries = answered }
  where
    queryable v = not (isRuntimeFailure v) && renderable v
    -- A sample is rendered into both backends' source; a closure or a symbol
    -- has no literal there (and a typed draw's result never is one).
    renderable v = case v of
      VClosure {} -> False
      VSymbol _ -> False
      VAnyExcept _ -> False
      VTuple a b -> renderable a && renderable b
      VEither (Left a) -> renderable a
      VEither (Right b) -> renderable b
      VADT _ fs -> all renderable fs
      VList l -> renderableList l
      _ -> True
    renderableList (ListCont x xs) = renderable x && renderableList xs
    renderableList _ = True
    hasWildcard v = case v of
      VAny -> True
      VTuple a b -> hasWildcard a || hasWildcard b
      VEither (Left a) -> hasWildcard a
      VEither (Right b) -> hasWildcard b
      VADT _ fs -> any hasWildcard fs
      VList AnyList -> True
      VList l -> anyList l
      _ -> False
    anyList (ListCont x xs) = hasWildcard x || anyList xs
    anyList AnyList = True
    anyList EmptyList = False

maxAgreementPoints :: Int
maxAgreementPoints = 12

-- | Printed once per process: the Julia arm skips, visibly, where there is no
-- @julia@ -- the same convention 'BatchedPython' follows for a missing torch.
{-# NOINLINE notesAnnounced #-}
notesAnnounced :: MVar [String]
notesAnnounced = unsafePerformIO (newMVar [])

noteOnce :: String -> IO ()
noteOnce msg = do
  fresh <- modifyMVar notesAnnounced $ \seen ->
    if msg `elem` seen then return (seen, False) else evaluate (length msg) >> return (msg : seen, True)
  if fresh then hPutStrLn stderr msg else return ()

prop_Fuzz_BackendsAgree :: Property
prop_Fuzz_BackendsAgree = withMaxSuccess (fuzzCases agreementBatches) $
  forAllShrink genAgreementBatch shrinkAgreementBatch $ \batch -> ioProperty $
    withinBudgetScaled "prop_Fuzz_BackendsAgree" 20 $ do
      prepared <- mapM prepareAgreementCase batch
      let cases = rights prepared
      if null cases then return discardVacuous else do
        pyD <- runPythonBatch cases
        julia <- findJulia
        jlD <- case julia of
          Just j -> runJuliaBatch j cases
          Nothing -> do
            noteOnce "prop_Fuzz_BackendsAgree: no julia on the PATH; the Julia arm is skipped (interpreter vs Python only)."
            return []
        let ds = pyD ++ jlD
            nQueries = sum (map (length . acQueries) cases)
        return
          $ tabulate "julia arm" [maybe "skipped (no julia)" (const "ran") julia]
          $ tabulate "drawn program" [ either id (const "compared") r | r <- prepared ]
          $ tabulate "query kind" [ kind q | c <- cases, (q, _) <- acQueries c ]
          $ tabulate "IR construct in a compared body" (concatMap (irEnvConstructs inferenceBodies . acEnv) cases)
          $ counterexample (show (length ds) ++ " disagreement(s) over " ++ show (length cases)
                            ++ " programs / " ++ show nQueries ++ " interpreter-answered queries; first:\n"
                            ++ concatMap renderDisagreement (take 2 ds))
          $ null ds
  where
    kind (QProb v) = "prob" ++ wildcardTag v
    kind (QInteg _) = "integ"
    wildcardTag :: IRValue -> String
    wildcardTag v = if v == VAny then " ANY" else if "VAny" `isInfixOf` show v then " partial ANY" else ""

return []

-- | Every @prop_@ property above, as @$(allProperties)@ names it
-- (@"prop_X from test/TestFuzz.hs:NNN"@).
fuzzProperties :: [(String, Property)]
fuzzProperties = $(allProperties)

-- | The properties that currently fail (or give up) at HEAD: the part of the
-- fuzz tier we want to guarantee but cannot yet. They run in the
-- @Aspirational@ group ('aspirationalFuzzTests', @NEST_ASPIRATIONAL_TESTS=1@)
-- rather than in @Slow@, so that @Slow@ can be expected green. Moving a
-- property back is part of fixing what it finds. Each entry says why it is
-- here; an entry naming no property fails the tree build, so the list cannot
-- rot past a rename.
aspirationalFuzzNames :: [(String, String)]
aspirationalFuzzNames =
  -- Measured 2026-10-01 on faster-tests (off dev ba19bac), three Slow runs at
  -- seeds 7919/15838/23757; nothing outside these failed in any of them.
  [ ("prop_Fuzz_TypedCompileNeverCrashes",
     "3/3 runs, a different compiler crash each time (getProbIndex's \"More \
     \than one probabilistic argument\", \"found no way to convert to IR\", an \
     \enumerated conditional meeting a density)")
  , ("prop_Fuzz_ProbNeverGenerateBacked",
     "3/3 runs: gives up on its discard rate within the wall-clock budget, \
     \or is falsified")
  -- The next entry replaced three per-invariant properties (TopKZeroMatchesExact,
  -- TopKNeverInflates, BranchCountingDoesNotChangeProbability; task
  -- fuzz-shared-draw-multi-config-compile). Re-measured 2026-10-07 at 72288f0
  -- before the merge, seeds 7919/15838/23757/31676/39595/47514: at least one of
  -- the three failed in 4/6 runs, every time with "did not terminate within
  -- 5000000us"; the two default-config invariants passed in all six.
  , ("prop_Fuzz_SharedDrawConfigInvariants",
     "4/6 runs (old per-invariant form): a topK-configured compile exceeds the \
     \per-case budget")
  ]

isAspirationalFuzz :: String -> Bool
isAspirationalFuzz name = propName name `elem` map fst aspirationalFuzzNames

-- | The bare binding name of an 'allProperties' label.
propName :: String -> String
propName = takeWhile (/= ' ')

fuzzTests :: TestTree
fuzzTests = testGroup "Fuzz"
  [testProperties "properties" [ p | p@(n, _) <- checkedFuzzProperties, not (isAspirationalFuzz n) ]]

aspirationalFuzzTests :: TestTree
aspirationalFuzzTests = testGroup "Fuzz"
  [testProperties "properties" [ p | p@(n, _) <- checkedFuzzProperties, isAspirationalFuzz n ]]

-- | 'fuzzProperties', after checking that every 'aspirationalFuzzNames' entry
-- names one of them.
checkedFuzzProperties :: [(String, Property)]
checkedFuzzProperties = case [ n | (n, _) <- aspirationalFuzzNames, n `notElem` map (propName . fst) fuzzProperties ] of
  []    -> fuzzProperties
  stale -> error ("aspirationalFuzzNames lists properties that do not exist: " ++ show stale)

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

-- | Every shrink of a fixed expression passes 'compatibleTys' against it --
-- the type-preservation property, stated for one expression rather than a draw.
shrinkPreservesTy :: Expr -> Property
shrinkPreservesTy e =
  counterexample ("orig ty: " ++ show (tyOfTypedExpr e)) $
    isJust (tyOfTypedExpr e) .&&. conjoin
      [ counterexample (show e' ++ "\n  shrink ty: " ++ show (tyOfTypedExpr e'))
                       (compatibleTys (tyOfTypedExpr e') (tyOfTypedExpr e))
      | e' <- shrinkTypedExpr e ]

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

-- | 'coreSize' plus every other declaration's node count: the measure the
-- shrinker reduces since milestone M4, when declarations started shrinking
-- too (a helper's or a recursive function's body is part of the draw).
--
-- Plus the declarations' size ('adtDeclSize'), since task
-- fuzz-generate-adt-declarations made them shrink too.
generatedSize :: Program -> Int
generatedSize p = coreSize p + sum [ typedExprSize e | (nm, e) <- functions p, nm /= "main" ]
                  + sum (map adtDeclSize (adts p))

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
-- The arrow generator's contract (task fuzz-arrow-generator-coverage).
--
-- Pure and fast, like the two groups above, and in the default suite for the
-- same reason: these pin the machinery the Slow properties rely on being
-- correct about, as opposed to what those properties measure. The classifier
-- cases come first because every coverage bound in this module is stated in
-- terms of it, and it is the one piece with a genuinely ambiguous input --
-- a @let@ is an 'Apply' of a 'Lambda', so "contains an Apply" and "applies a
-- function value" are different questions about the same node.
arrowGeneratorTests :: TestTree
arrowGeneratorTests = testGroup "Arrow generator"
  [ testCase "a let is not a function value" $
      assertEqual "" NoArrow (arrowShapeOf (letIn "v0" uniform (constF 1.0)))
  , testCase "applying a named function is AppliedFun" $
      assertEqual "" AppliedFun (arrowShapeOf (apply (var "helper") (constF 1.0)))
  , testCase "applying an if-selected function is SelectedFun" $
      assertEqual "" SelectedFun
        (arrowShapeOf (apply (ifThenElse (constB True) incLam incLam) (constF 1.0)))
  , testCase "applying two arguments in a row is CurriedFun" $
      assertEqual "" CurriedFun
        (arrowShapeOf (apply (apply (var "helper") (constF 1.0)) (constF 2.0)))
  , testCase "a let-bound function value's type is recoverable" $
      -- Recovery pushes the argument type into the callee, so the parameter
      -- the 'Lambda' node does not record is pinned at the call site. Without
      -- this the whole function-value surface would generate but never shrink.
      assertEqual "" (Just TyFloat)
        (tyOfTypedExpr (letIn "v0" incLam (apply (var "v0") (constF 1.0))))
  , testCase "a let-bound function value with a polymorphic body is recoverable" $ do
      -- Task adt-generator-core-type-recoverable-flake: 'genFunctionLet'
      -- binds a lambda and applies it in the body. Read as a value, the
      -- lambda's parameter is free, and @neg@ over a free argument matches
      -- both its Float and its Int catalog row, so it recovers nothing; the
      -- parameter is taken from the call site instead.
      let negLam = "v1" #-># injF "neg" [ifThenElse (constB False) (var "v1") (var "v1")]
      assertEqual "standalone, the lambda is unrecoverable" Nothing (tyOfTypedExpr negLam)
      assertEqual "applied in a let body" (Just TyFloat)
        (tyOfTypedExpr (letIn "v0" negLam (apply (var "v0") normal)))
      assertEqual "applied to an Int" (Just TyInt)
        (tyOfTypedExpr (letIn "v0" ("v1" #-># injF "neg" [var "v1"]) (apply (var "v0") (constI 1))))
  , testCase "a let-bound function value is typed at its call site even when it recovers alone" $
      -- The neural-draw twin of the above (replay 913155 of "a neural draw's
      -- core type is recoverable"): @(\\a -> \\b -> b) e@ recovers alone, but
      -- only as @? -> ?@, which leaves the @neg@ around its call ambiguous.
      assertEqual "" (Just TyFloat)
        (tyOfTypedExpr (injF "neg" [letIn "v0" (apply ("a" #-># ("b" #-># var "b")) (constB True))
                                              (apply (var "v0") normal)]))
  , testCase "a curried literal lambda has both parameters pushed in" $
      assertEqual "" (Just TyInt)
        (tyOfTypedExpr (apply (apply ("a" #-># ("b" #-># injF "neg" [var "b"])) (constB True)) (constI 2)))
  , testCase "a function value shrinks to a constant function, not from within" $
      -- The soundness rule the 'Shrinker' group's type-preservation property
      -- caught the violation of: at a bare lambda nothing says what the
      -- parameter was bound at, so the body is not descended into, and the
      -- only candidate is the closed constant function.
      assertEqual "" [ "v0" #-># constF 0 ]
        (shrinkTypedExpr ("v0" #-># (var "v0" #+# constF 1.0)))
  , testCase "the constant-function leaf ignores its argument" $
      assertEqual "" [ "p" #-># constF 0 ] (typedLeaves (TyArrow TyBool TyFloat))
  , testProperty "a helper draw validates and applies its helper" $
      forAll (resize fuzzSize genHelperProgram) $ \p ->
        counterexample (show p) $
              validateProgram p === Right ()
         .&&. length (functions p) === 2
         -- At least: the helper's body and the argument are ordinary draws and
         -- may contain a computed callee of their own.
         .&&. property (arrowShapeOfProgram p >= AppliedFun)
  , testCase "a helper called only through a let alias is typed at the alias's call" $ do
      -- replay 272312 of the property below, shrunk by hand: the direct call's
      -- argument mentions the helper itself, so only the alias's call site
      -- (@v0 1.0@) pins the parameter, and @mult h0 h0@ over a free parameter
      -- is ambiguous between Float and Int.
      let helper = "h0" #-># injF "mult" [var "h0", var "h0"]
          mainE = apply (var "helper")
                    (injF "neg" [letIn "v0" (var "helper") (apply (var "v0") (constF 1.0))])
      assertEqual "" (Just TyFloat)
        (typedMainCoreTy (Program [("helper", helper), ("main", mainE)] [] [] [] []))
  , testProperty "a helper draw's main type is recoverable" $
      forAll (resize fuzzSize genHelperProgram) $ \p ->
        counterexample (show p) (property (isJust (typedMainCoreTy p)))
  , testProperty "shrinking a helper draw keeps both declarations and validates" $
      forAll (resize fuzzSize genHelperProgram) $ \p -> conjoin
        [ counterexample (show p')
            (length (functions p') === 2 .&&. validateProgram p' === Right ())
        | p' <- shrinkTypedProgram p ]
  ]
  where incLam = "x" #-># (var "x" #+# constF 1.0)

-- ---------------------------------------------------------------------------
-- Milestone M4's contract: ADTs and recursion (design
-- typed-program-generator-expansion).
--
-- Default suite, like the two groups above. Two of these are safety rules
-- rather than shape checks, and each guards a way the generator could start
-- manufacturing false counterexamples without anything going red: an
-- unguarded field projection on a multi-constructor type (the ADT twin of
-- @head []@), and a recursive function that may not return -- which the
-- shrinker, left to it, would actively walk toward, a timeout reading as
-- "still failing".
adtRecursionGeneratorTests :: TestTree
adtRecursionGeneratorTests = testGroup "ADT and recursion generator"
  [ testCase "withADTs declares exactly the pool types a program uses" $ do
      let declared p = map dataName (adts (withADTs p))
      assertEqual "unused" [] (declared (Program [("main", constF 1.0)] [] [] [] []))
      assertEqual "test on a constructor" ["Hue"]
        (declared (Program [("main", injF "isRed" [injF "Red" []])] [] [] [] []))
      assertEqual "recursive" ["Chain"]
        (declared (Program [("main", injF "Link" [constF 1.0, injF "Stop" []])] [] [] [] []))
      assertEqual "a neural target counts although nothing reads it" ["Pt"]
        (declared (Program [("main", constB True)] [("nn", TArrow TSymbol (TADT "Pt"), Nothing)] [] [] []))
  , testCase "the whole pool validates as declarations" $
      assertEqual "" (Right ()) (validateProgram (Program [("main", constB True)] [] adtPool [] []))
  , testCase "every pool type's smallest leaf recovers to it" $
      mapM_ (\n -> case typedLeaves (TyADT n) of
               (l : _) -> assertEqual n (Just (TyADT n)) (tyOfTypedExpr l)
               []      -> assertFailure ("no leaf for " ++ n)) adtPoolNames
  , testCase "a constructor applied to a wrong-typed field does not recover" $
      -- The shrinker's per-node re-typing would otherwise accept a field
      -- replaced by a value of another type: a constructor node's own type
      -- says nothing about its arguments.
      assertEqual "" Nothing (tyOfTypedExpr (injF "MkPt" [constB True, constB True]))
  , testCase "an ADT draw binding a polymorphic function value is recoverable (seed 890826)" $ do
      -- The minimal counterexample of --quickcheck-replay=890826 on the
      -- property below (task adt-generator-core-type-recoverable-flake),
      -- verbatim: its ADT was incidental, the unrecoverable part was the
      -- let-bound @\v3 -> neg (...)@ whose parameter only the call site pins.
      let more = injF "More" [injF "left" [injF "lt" [uniform, constF 0.46678494200011444]]]
          inner = injF "TCons" [injF "TCons" [cons normal (constL []), constF 0.0], cons (constF (-8.50593741805913)) (constL [])]
          pick3 = injF "plus" [constI 1, ifThenElse (injF "lt" [uniform, constF (1/3)]) (constI 3)
                     (ifThenElse (injF "lt" [uniform, constF 0.5]) (constI 2) (constI 1))]
          negLam = "v3" #-># injF "neg" [ifThenElse (constB False) (var "v3") (var "v3")]
          body = apply ("v0" #-># injF "fst" [apply ("v1" #-># injF "snd" [injF "TCons" [more, inner]]) pick3])
                       (apply ("v2" #-># apply (var "v2") normal) negLam)
          p = Program [("main", body)] [] [ADTDecl "More" [("More", [("idx", TEither TBool TBool)])] Nothing] [] []
      assertEqual "validates" (Right ()) (validateProgram p)
      assertEqual "core type" (Just (TyTuple (TyList TyFloat) TyFloat)) (typedMainCoreTy p)
  , testProperty "an ADT draw validates and its core type is recoverable" $
      forAll (resize fuzzSize genTypedProgram) $ \p ->
        not (null (adts p)) ==>
          counterexample (show p)
            (validateProgram p === Right () .&&. property (isJust (typedMainCoreTy p)))
  , testProperty "a multi-constructor field is projected only under its constructor test" $
      forAll (resize fuzzSize genTypedProgram) $ \p ->
        let bad = unguardedProjections p
        in counterexample (show bad ++ "\n" ++ show p) (null bad)
  , testProperty "no shrink makes a projection unguarded" $
      forAll (resize fuzzSize genTypedProgram) $ \p -> conjoin
        [ counterexample (show p') (unguardedProjections p' === [])
        | p' <- shrinkTypedProgram p ]
  , testCase "a guarded projection is not collapsed onto its then-arm" $ do
      -- The minimized shape the first M4 Aspirational run produced: the
      -- shrinker had reduced a crashing draw to @lv Stop@, the accessor's own
      -- error, by taking the then-arm of the guard.
      let guardedLv = letIn "v0" (injF "Stop" [])
                        (ifThenElse (injF "isLink" [var "v0"]) (injF "lv" [var "v0"]) (constF 1.0))
          prog = withADTs (Program [("main", guardedLv)] [] [] [] [])
      assertEqual "the original is guarded" [] (unguardedProjections prog)
      mapM_ (\p' -> assertEqual (show p') [] (unguardedProjections p')) (shrinkTypedProgram prog)
  , testProperty "a recursive draw validates and its main type is recoverable" $
      forAll (resize fuzzSize genRecursiveProgram) $ \p ->
        counterexample (show p)
          (validateProgram p === Right () .&&. property (isJust (typedMainCoreTy p)))
  , testProperty "a recursive step makes at most one call per invocation" $
      forAll (resize fuzzSize genRecursiveProgram) $ \p ->
        conjoin [ counterexample (show e) (callsOnce nm (underParam e) <= 1)
                | (nm, e) <- functions p, nm /= "main" ]
  , testProperty "every generated recursive declaration is termination-safe" $
      forAll (resize fuzzSize genRecursiveProgram) $ \p ->
        conjoin [ counterexample (show e) (recursionSafe (adts p) nm e e) | (nm, e) <- decls p ]
  , testCase "a shrink may not unwrap a productive call" $ do
      let orig = ifThenElse (bernoulli 0.5) (injF "Stop" []) (injF "Link" [constF 1.0, var "loop"])
      assertBool "the original" (recursionSafe adtPool "loop" orig orig)
      assertBool "Link x loop -> loop"
        (not (recursionSafe adtPool "loop" orig (ifThenElse (bernoulli 0.5) (injF "Stop" []) (var "loop"))))
  , testCase "a shrink may not change a counted call's argument" $ do
      let body a = "k" #-># ifThenElse (var "k" #<# constI 1) (constI 0) (apply (var "loop") a)
          orig = body (var "k" #<-># constI 1)
      assertBool "the original" (recursionSafe adtPool "loop" orig orig)
      assertBool "k - 1 -> k" (not (recursionSafe adtPool "loop" orig (body (var "k"))))
      assertBool "the call removed" (recursionSafe adtPool "loop" orig ("k" #-># constI 0))
  -- Task fuzz-generate-adt-declarations: the declaration generator and the
  -- declaration shrinks.
  , testProperty "generated declarations validate" $
      forAll genADTDecls $ \ds ->
        counterexample (show ds) (validateProgram (Program [("main", constB True)] [] ds [] []) === Right ())
  , testProperty "every declared type has a finite leaf that recovers to it" $
      -- What keeps generation and shrinking finite on a recursive or mutually
      -- recursive declaration, and what the shrinker offers at that type.
      forAll genADTDecls $ \ds -> conjoin
        [ counterexample (show (dataName d) ++ "\n" ++ show ds) $ case adtLeaf ds (dataName d) of
            Nothing -> property False
            Just l  -> let p = Program [("main", l)] [] ds [] []
                       in typedMainCoreTy p === Just (TyADT (dataName d))
                          .&&. validateProgram (withADTs p) === Right ()
        | d <- ds ]
  , testProperty "a mutually recursive pair validates, is mutual, and has finite leaves" $
      -- Not generated in programs yet (ArbitrarySPLL.generateMutualPairs:
      -- such programs hang the compiler, a filed bug), so pinned here.
      forAll genMutualADTPair $ \pair ->
        let ds = adtPool ++ pair
        in counterexample (show pair) $
             validateProgram (Program [("main", constB True)] [] ds [] []) === Right ()
             .&&. map (elem "mutually recursive" . snd) (adtShapes ds) === map (const False) adtPool ++ [True, True]
             .&&. conjoin [ property (isJust (adtLeaf ds (dataName d))) | d <- pair ]
  , testCase "an unused constructor and an unused field shrink away" $ do
      let box cs = ADTDecl "Box" cs Nothing
          full   = ("Full", [("x", TFloat), ("y", TBool)])
          p = Program [("main", injF "Full" [constF 1.0, constB True])] [] [box [("Empty", []), full]] [] []
          shrunk = shrinkTypedProgram p
      assertBool "Empty dropped" ([box [full]] `elem` map adts shrunk)
      assertBool "y dropped, with its argument"
        (Program [("main", injF "Full" [constF 1.0])] [] [box [("Empty", []), ("Full", [("x", TFloat)])]] [] []
           `elem` shrunk)
  , testCase "a constructor or field the program names is never dropped" $ do
      let box = ADTDecl "Box" [("Empty", []), ("Full", [("x", TFloat), ("y", TBool)])] Nothing
          body = letIn "v0" (injF "Full" [constF 1.0, constB True])
                   (ifThenElse (injF "isEmpty" [var "v0"]) (constF 0.0) (injF "x" [var "v0"]))
          p = Program [("main", body)] [] [box] [] []
          kept p' = [ (c, map fst fs) | d <- adts p', (c, fs) <- constructors d ]
          -- A candidate that no longer declares Box at all shrank main past
          -- every use of it, which is the unused-declaration rule, not this one.
          stillBox = [ p' | p' <- shrinkTypedProgram p, not (null (adts p')) ]
      assertBool "some candidate keeps Box" (not (null stillBox))
      mapM_ (\p' -> do assertBool (show p') (lookup "Empty" (kept p') /= Nothing)
                       assertBool (show p') (maybe True ("x" `elem`) (lookup "Full" (kept p'))))
            stillBox
  , testCase "a declaration shrink never leaves a type without a finite value" $ do
      -- Nothing builds a Lst here -- only the network does -- so Nil is an
      -- unused constructor; dropping it would leave Wrap w::Lst, which has
      -- no finite value at all.
      let lst  = ADTDecl "Lst" [("Nil", []), ("Wrap", [("w", TADT "Lst")])] (Just 2)
          body = "sym" #-># letIn "s" (readNN "nn" (var "sym"))
                   (ifThenElse (injF "isWrap" [var "s"]) (constF 1.0) (constF 0.0))
          p = Program [("main", body)] [("nn", TArrow TSymbol (TADT "Lst"), Nothing)] [lst] [] []
      mapM_ (\p' -> assertBool (show (adts p')) (any (any ((== "Nil") . fst) . constructors) (adts p')))
            (shrinkTypedProgram p)
  , testProperty "shrinking a recursive draw keeps its stopping condition and validates" $
      forAll (resize fuzzSize genRecursiveProgram) $ \p -> conjoin
        [ counterexample (show p')
            -- A shrink may remove the recursive call (the step shrinking to a
            -- leaf), which ends the obligation; what it may never do is keep
            -- the call and change the condition guarding it.
            (conjoin [ fmap (stopCond . snd) (find ((== nm) . fst) (decls p)) === Just (stopCond e')
                     | (nm, e') <- decls p' ]
             .&&. validateProgram p' === Right ())
        | p' <- shrinkTypedProgram p ]
  ]
  where
    decls p = [ d | d@(nm, e) <- functions p, nm /= "main", mentionsVar nm e ]
    stopCond e = case node e of
      Lambda _ b       -> stopCond b
      IfThenElse c _ _ -> Just (toStub c)
      _                -> Nothing
    -- Occurrences of @nm@ evaluated at most once per evaluation: not under a
    -- lambda other than a @let@'s (whose body runs once).
    callsOnce nm e = case node e of
      Var x -> if x == nm then 1 else 0 :: Int
      Apply l v | Lambda _ b <- node l -> callsOnce nm b + callsOnce nm v
      IfThenElse c t f -> callsOnce nm c + callsOnce nm t + callsOnce nm f
      InjF _ as -> sum (map (callsOnce nm) as)
      Apply a b -> callsOnce nm a + callsOnce nm b
      _ -> 0
    -- A counted declaration's own parameter lambda runs once per call.
    underParam e = case node e of
      Lambda _ b -> b
      _          -> e

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
        , "neg", "negI", "not", "or", "plus", "plusI", "sq" ]
        (sort (nub (map injFName injFCatalog)))

  , testCase "the exclusions are what we think they are, with reasons" $
      -- 'InjFGuarded' is the one that matters for correctness: @log@, @sqrt@
      -- and @recip@ are partial on their argument type, and generating them
      -- unguarded would manufacture NaN/Infinity densities that say nothing
      -- about the compiler. @recip@ is the cautionary one: it was generated
      -- until its forward declaration was corrected to state the @a /= 0@
      -- domain it always had, and because @typedLeaves TyFloat@ is @0@, the
      -- shrinker minimized any failing draw containing it *towards* @recip 0@
      -- -- turning real counterexamples into Infinity artifacts, the exact
      -- false-counterexample class the shrinker exists to prevent.
      -- The rest are shape, not safety -- 'genTypedRec' owns the
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
        , ("recip", InjFGuarded)
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
        -- The program's own ADT declarations count: their constructors,
        -- accessors and tests enter 'globalFEnv' per declaration (M4).
        let defined = map fst (globalFEnv (adts prog))
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
  , testProperty "an absurd but finite setting is clamped, not taken" $ once $
      -- Unclamped, 'scaleFuzz' would overflow 'Int' on these and could hand
      -- 'timeout' a negative budget, which disables it outright -- a typo
      -- would switch the per-case bound *off* rather than leave the suite
      -- doing its ordinary job.
      conjoin [ counterexample inp (parseFuzzScale (Just inp) === maxFuzzScale)
              | inp <- ["1e30", "1e9", "1001", "1e300"] ]
  , testProperty "the cap keeps every scaled budget a sane positive Int" $
      forAll (choose (0.001, 1e300)) $ \raw ->
        let sc = parseFuzzScale (Just (show (raw :: Double)))
            budgets = [ scaleFuzz (max 1 sc) defaultPerCaseBudgetMicros
                      , scaleFuzz (max 1 sc) defaultPropertyBudgetMicros ]
        in counterexample (show (raw, sc, budgets)) $
             sc <= maxFuzzScale && all (> 0) budgets
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
  , testProperty "the property budget never scales down either" $
      forAll (choose (0.001, 50)) $ \sc ->
        scaleFuzz (max 1 sc) defaultPropertyBudgetMicros >= defaultPropertyBudgetMicros
  , testProperty "a property's first case always runs" $
      -- Even at a zero budget. A property that gave up having executed
      -- nothing would report as a give-up indistinguishable from a picky
      -- precondition, and would make the bound impossible to set safely.
      forAll (choose (0, 1000000)) $ \b ->
      forAll (choose (0, 1000000000)) $ \t ->
        snd (budgetStep b "p" (fromIntegral (t :: Int)) []) === True
  , testProperty "the first case fixes the deadline, and later ones read it" $
      forAll (choose (1000, 1000000)) $ \b ->
        let t0 = 5000 :: Word64
            (tbl, first) = budgetStep b "p" t0 []
        in     counterexample "first case" (first === True)
          .&&. counterexample "deadline stored"
                 (lookup "p" tbl === Just (t0 + fromIntegral b))
          -- Inside the budget the table is left alone, so the deadline is
          -- fixed at the property's start rather than sliding forward with
          -- each case -- which is what makes it an aggregate bound rather
          -- than a second per-case one.
          .&&. counterexample "still inside"
                 (budgetStep b "p" (t0 + fromIntegral b - 1) tbl === (tbl, True))
          .&&. counterexample "exactly at the deadline"
                 (budgetStep b "p" (t0 + fromIntegral b) tbl === (tbl, False))
          .&&. counterexample "past the deadline"
                 (budgetStep b "p" (t0 + fromIntegral b + 1) tbl === (tbl, False))
  , testProperty "properties do not share a budget" $
      -- Each property is bounded on its own clock; one that exhausts its
      -- budget must not drain a sibling that has not started yet.
      let b = 1000 :: Int
          (tbl1, _) = budgetStep b "a" 0 []
          (tbl2, bStarts) = budgetStep b "b" 5000 tbl1
      in     counterexample "a is spent" (snd (budgetStep b "a" 5000 tbl1) === False)
        .&&. counterexample "b still starts" (bStarts === True)
        .&&. counterexample "b got its own deadline"
               (lookup "b" tbl2 === Just 6000)
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
-- Note what is *not* asserted: which of 'Left' or 'Right' comes back -- only
-- that the compiler survives long enough to have an opinion. (What
-- @head []@/@tail []@ mean at run time is settled in
-- 'fuzz-structured-type-bugs': a raise, i.e. 'VError' from sampling and
-- 'Left' from constant folding.)
staticallyEmptyTailProgram :: Program
staticallyEmptyTailProgram =
  Program [("main", ltail (ltail (cons (left (constI 0)) nul)))] [] [] [] []

-- | A draw that crashes the compiler no matter how the error channels are
-- wired: the bottom is inside a constant, so every pass that forces it throws.
-- Stands in for "some future compiler crash" in the coverage test below --
-- 'prop_Fuzz_GeneratorCoverage' must classify such a draw, not die of it.
crashingProgram :: Program
crashingProgram =
  Program [("main", constI (error "deliberate crash: this draw crashes the compiler"))] [] [] [] []

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

-- | The two ways a shrink that preserves the type *at its own site* can still
-- change what an enclosing node recovers (task shrinker-type-recovery-flake).
-- Both were found by the type-preservation property below at roughly one
-- failing draw in 30,000 -- too rare to go red on a default run, so they are
-- pinned here deterministically.
--
-- 'TyAny' read as "free" where it only meant "not recovered": the argument of
-- @sq@ applies a variable bound to a function value, which recovered as '?'.
-- @sq@ is Float-only, so @sq a@ is Float and collapsing it to @a@ passed the
-- site-local test -- but the enclosing @neg@ is polymorphic, and @neg a@
-- recovers as 'Nothing'. (Since task adt-generator-core-type-recoverable-flake
-- the call site types @f@ and this exact shape recovers as Float throughout;
-- 'notRecoveredUnderSq' keeps the class reachable by applying @f@ through a
-- selection, which the call-site push does not see.)
shrinkUnderPolymorphicParent :: Expr
shrinkUnderPolymorphicParent =
  negF (injF "sq" [letIn "f" ("y" #-># var "y") (apply (var "f") (constF 1.0))])

-- | A callee shrink that changes which recovery rule the enclosing
-- application uses. @(let a = 0 in \\b -> b) xs@ has a non-literal callee, so
-- its type is read off the callee's arrow, @? -> ?@, giving '?'. Collapsing the
-- dead @let@ leaves the literal @\\b -> b@, which turns the application into a
-- @let@ that pushes @xs@'s type in and recovers @List Bool@ -- committing, in
-- the enclosing tuple, a position the original left free.
shrinkChangesParentRule :: Expr
shrinkChangesParentRule =
  tuple (apply (letIn "a" (constF 0.0) ("b" #-># var "b")) (cons (constB True) nul))
        (constF 0.0)

-- | The function value of 'shrinkUnderPolymorphicParent', applied through an
-- @if@ so that its parameter is not typed at a call site: @f@ keeps its
-- value reading, @\y -> y@ at an unrecovered parameter, and the application
-- recovers as 'TyUnrecovered'.
notRecoveredArg :: Expr
notRecoveredArg =
  letIn "f" ("y" #-># var "y")
    (apply (ifThenElse (constB True) (var "f") (var "f")) (constF 1.0))

notRecoveredUnderSq :: Expr
notRecoveredUnderSq = injF "sq" [notRecoveredArg]

-- | Task fuzz-tyany-conflates-free-and-unrecovered: recovery tells "no node
-- commits this position" ('TyAny') from "some node does, recovery could not
-- tell to what" ('TyUnrecovered'), and the consumers read the second as
-- "cannot conclude".
freeVsUnrecoveredTests :: TestTree
freeVsUnrecoveredTests = testGroup "free vs not recovered"
  [ testCase "a free position recovers as TyAny" $ do
      assertEqual "left pins only its own side" (Just (TyEither TyFloat TyAny))
        (tyOfTypedExpr (left (constF 1.0)))
      assertEqual "a constant function's parameter is free" (Just (TyArrow TyAny TyFloat))
        (tyOfTypedExpr ("p" #-># constF 0.0))
  , testCase "the first shrinker counterexample's function value is not recovered" $ do
      -- 'shrinkUnderPolymorphicParent''s @f@, read as a value.
      assertEqual "the bound value" (Just (TyArrow TyUnrecovered TyUnrecovered))
        (tyOfTypedExpr ("y" #-># var "y"))
      assertEqual "applied where the call site cannot type it" (Just TyUnrecovered)
        (tyOfTypedExpr notRecoveredArg)
  , testCase "the second shrinker counterexample's callee is not recovered" $
      -- 'shrinkChangesParentRule''s callee, read on its own.
      assertEqual "" (Just (TyArrow TyUnrecovered TyUnrecovered))
        (tyOfTypedExpr (letIn "a" (constF 0.0) ("b" #-># var "b")))
  , testCase "a not-recovered argument is rejected at its own site" $ do
      -- Without the split this collapse passed the site-local test, and only
      -- the per-level re-check one node up caught it.
      assertBool "sq x does not shrink to x"
        (notRecoveredArg `notElem` shrinkTypedExpr notRecoveredUnderSq)
      assertBool "the callee does not collapse onto the bare lambda"
        (("b" #-># var "b") `notElem` shrinkTypedExpr (letIn "a" (constF 0.0) ("b" #-># var "b")))
  , testCase "TyUnrecovered generalizes nothing, and only TyAny generalizes it" $ do
      assertBool "not itself" (not (tyGeneralizes TyUnrecovered TyUnrecovered))
      assertBool "not a concrete type" (not (tyGeneralizes TyUnrecovered TyFloat))
      assertBool "no concrete type generalizes it" (not (tyGeneralizes TyFloat TyUnrecovered))
      assertBool "nor one nested in a structure"
        (not (tyGeneralizes (TyEither TyFloat TyFloat) (TyEither TyFloat TyUnrecovered)))
      assertBool "but a free position nested in one does"
        (tyGeneralizes (TyEither TyFloat TyAny) (TyEither TyFloat TyUnrecovered))
      assertBool "a free position does" (tyGeneralizes TyAny TyUnrecovered)
  , testCase "joining a not-recovered reading unfrees the other side's free positions" $ do
      assertEqual "" (Just (TyEither TyFloat TyUnrecovered))
        (tyJoin (TyEither TyFloat TyAny) TyUnrecovered)
      assertEqual "" (Just TyUnrecovered) (tyJoin TyAny TyUnrecovered)
  , testProperty "a shrink is re-typed under a polymorphic parent (not-recovered argument)" $ once $
      shrinkPreservesTy (negF notRecoveredUnderSq)
  , testCase "a main shrink may not drop the call site that types a helper (replay 520205)" $ do
      -- The helper's parameter is typed at its call in @main@, whose argument
      -- recovers only through the @if@'s else-arm. Collapsing the @if@ onto
      -- its then-arm is type-preserving in the scope the *original* program
      -- recovers, but leaves the helper at its value reading -- parameter not
      -- recovered -- and @main@ with it.
      let helper = "h0" #-># injF "head" [injF "Cons" [var "h0", nul]]
          selected = ifThenElse (constB False) (var "helper") (var "helper")
          mainE  = apply (var "helper")
                     (apply (ifThenElse (constB True) selected ("v1" #-># constI 1)) (constI 2))
          p = Program [("helper", helper), ("main", mainE)] [] [] [] []
          collapsed = apply (var "helper") (apply selected (constI 2))
      assertEqual "the original recovers" (Just TyInt) (typedMainCoreTy p)
      assertEqual "the collapse alone does not"
        (Just TyUnrecovered) (typedMainCoreTy p { functions = [("helper", helper), ("main", collapsed)] })
      assertBool "and is not offered"
        (collapsed `notElem` [ e | p' <- shrinkTypedProgram p, Just e <- [lookup "main" (functions p')] ])
      assertBool "every offered shrink keeps the core type"
        (and [ compatibleTys (typedMainCoreTy p') (typedMainCoreTy p) | p' <- shrinkTypedProgram p ])
  ]

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
        [ counterexample (show p') (generatedSize p' < generatedSize p)
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
                  (validateProgram (withADTs (Program [("main", e')] [] [] [] [])) === Right ())
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
  , testProperty "a shrink is re-typed under a polymorphic parent" $ once $
      shrinkPreservesTy shrinkUnderPolymorphicParent
  , testProperty "a shrink is re-typed when it changes the parent's recovery rule" $ once $
      shrinkPreservesTy shrinkChangesParentRule
  , testProperty "a shared-draw failure names its invariant and shrinks against that one" $ once $ ioProperty $ do
      -- Two fake invariants that need no compile. Every draw breaks both, and
      -- the first listed is the one shrinking is pinned to, so every run must
      -- end on a program that still breaks it. A shrink that kept only the
      -- second broken (a big program with its Normal gone) is exactly what an
      -- unpinned shrink would take. Not every draw has a shrink keeping its
      -- Normal (@head(Cons(Normal, []))@ has none), so the runs only need
      -- some draw to shrink past the second invariant altogether -- which
      -- also shows a pinned shrink does make progress.
      let holdsOnMain f = maybe False f . mainBody . icProgram
          gaussian = Invariant "fake-gaussian-leaf" [] $ \c ->
            return (if holdsOnMain containsNormal c then Broken "has a Normal leaf" else Holds)
          big = Invariant "fake-big" [] $ \c ->
            return (if holdsOnMain ((> 3) . typedExprSize) c then Broken "is big" else Holds)
          gen = resize fuzzSize genTypedProgram `suchThat` \p ->
            maybe False (\b -> containsNormal b && typedExprSize b > 3) (mainBody p)
          onlyGaussian = "all failures on this program: " ++ show [Breaks "fake-gaussian-leaf"]
      rs <- replicateM 20 $ quickCheckWithResult stdArgs { chatty = False }
              (invariantsPropertyOn gen "shrinker-test-shared-draw" 1 [gaussian, big] 100)
      let finals = [ (failingTestCase r, numShrinks r) | r@Failure{} <- rs ]
      return $
        counterexample (unlines (concatMap fst finals)) $
             length finals === length rs
        .&&. conjoin [ counterexample "a run's final program does not name the first invariant" $
                         "invariant fake-gaussian-leaf broken: has a Normal leaf" `elem` ls
                     | (ls, _) <- finals ]
        .&&. counterexample "no run shrank to a program breaking only the first invariant"
               (any (\(ls, k) -> k > 0 && onlyGaussian `elem` ls) finals)
  , localOption (QuickCheckMaxRatio 30) $
    testProperty "minimization keeps the failing feature and never grows" $
      -- The guard below ("this draw contains a Normal") is satisfied by about
      -- one draw in ten -- 98 passes against 1000 discards, measured on the
      -- run that first exceeded QuickCheck's default 10:1 budget -- so the
      -- default gives up just short of 100 successes. Two things pushed it
      -- there, both from the arrow axis: a 'genHelperProgram' draw's @main@ is
      -- a single call, with the body (and any Normal in it) in the
      -- declaration this property does not look at, and an application spends
      -- budget on nodes that are not leaves. Raising the ratio keeps the
      -- property's power (it still wants 100 real successes) rather than
      -- weakening what it checks.
      forAll (resize fuzzSize genTypedProgram) $ \p ->
        case mainBody p of
          Nothing -> property True
          Just b  -> containsNormal b ==>
            let m = minimizeBy containsNormal b
            in counterexample (show m)
                 (containsNormal m .&&. typedExprSize m <= typedExprSize b)
  , freeVsUnrecoveredTests
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

-- | Carries a whole-property deadline too, on the same reasoning as
-- 'withinBudgetScaled' -- and with more force here, since this property's
-- per-case budget is 8s and it is the other oracle that has never returned a
-- verdict. Its budget is the SuperSlow tier's own, not the Slow one's: the
-- tier is opt-in and expected to be long, so bounding it at 120s would report
-- a give-up for the ordinary reason that it is slow.
superSlowPropertyBudgetMicros :: Int
superSlowPropertyBudgetMicros = scaleFuzz (max 1 fuzzScale) (600 * 1000 * 1000)

withinSuperSlowBudget :: String -> IO Property -> IO Property
withinSuperSlowBudget name act = do
  hasBudget <- claimBudget superSlowPropertyBudgetMicros name
  if not hasBudget
    then noteExhaustion name superSlowPropertyBudgetMicros >> return discardVacuous
    else do
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
-- docs/pipeline-and-types.md's PType section -- but 'drawQueryPoints' filters query points
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
    , not (isRuntimeFailure s)
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
fuzzSamplingMatchesPDF = withMaxSuccess (fuzzCases 20) $ forAllShrink (resize fuzzSize genTypedProgram) shrinkTypedProgram $ \p -> ioProperty $ withinSuperSlowBudget "prop_Fuzz_SamplingMatchesPDF" $ do
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


-- ---------------------------------------------------------------------------
-- The admission oracle itself (task admission-totality-property).
--
-- 'prop_Fuzz_AdmissionTotality' is opt-in (Slow), so the oracle it rests on is
-- pinned here, in the default suite, on hand-written programs: one per
-- classification it makes. The violation case is the non-vacuity check -- a
-- program the lattice admits and the IR compiler crashes on (a filed
-- known-issues pin) must come out as a crash attributed to the function and
-- the inference mode, or the property could pass by never seeing one. All of
-- these compile in well under a second.

admissionOracleTests :: TestTree
admissionOracleTests = testGroup "Admission oracle"
  [ testCase "an admitted program evaluates in every mode" $ do
      rep <- oracleOn "main = if Uniform < 0.3 then 1.0 else Normal"
      assertNoViolation rep
      assertEqual "outcomes" [(ModeGenerate, "value"), (ModeProbability, "value"), (ModeIntegrate, "value")]
        (outcomesOf "main" rep)
  , testCase "a refused program still generates, and nothing else is asked of it" $ do
      rep <- oracleOn "main = Uniform + Normal"
      assertNoViolation rep
      assertEqual "verdict" (Just Bottom) (verdictOf "main" rep)
      assertEqual "outcomes" [(ModeGenerate, "value")] (outcomesOf "main" rep)
  , testCase "an IRError raised by the interpreter is a refusal, not a crash" $ do
      -- cdf over an ADT: the compiler emits an IRError on purpose, and the
      -- interpreter raises it rather than answering Left.
      rep <- oracleOn "data Hue = Red | Green\nmain = if Uniform < 0.5 then Red else Green"
      assertNoViolation rep
      assertEqual "integrate" [(ModeIntegrate, "refusal")]
        [ o | o@(m, _) <- outcomesOf "main" rep, m == ModeIntegrate ]
  , testCase "a helper is evaluated at canonical arguments" $ do
      rep <- oracleOn "shift x = x + Normal\nmain = shift 1.0"
      assertNoViolation rep
      assertEqual "helper outcomes" [(ModeGenerate, "value"), (ModeProbability, "value"), (ModeIntegrate, "value")]
        (outcomesOf "shift" rep)
  , testCase "an admitted function the IR compiler crashes on is a violation naming it" $ do
      -- Docs task function-value-compared-in-probability-mode: admitted, and
      -- the IR compiler dies on an internal invariant (a CDF comparison built
      -- for an arrow type) rather than refusing. Earlier versions of this case
      -- used fuzz-admission-oracle-bugs item 7's curried lambda and then the
      -- bare equality of two neural reads, both of which compile now.
      rep <- oracleOn "main = \\v0 -> v0 0 (if False then (if Uniform < 0.894 then \\v1 -> Uniform else \\v2 -> 0.0) else head ((\\v3 -> [\\v4 -> Uniform]) 1.0))"
      case [ v | v@(Check "main" _ _ (Crash _)) <- violations rep ] of
        (Check _ pt _ (Crash msg) : _) -> do
          assertBool ("admitted: " ++ show pt) (admitted pt)
          assertBool msg ("Comparison not implemented for type: TArrow" `isInfixOf` msg)
        _ -> assertFailure ("expected a crash on main, got " ++ show (violations rep))
  , testCase "an admitted function the IR compiler refuses is an over-promise, and generate survives" $ do
      -- test/cases/known-issues/correlatedGaussianLetSharesLatent: admitted,
      -- and the set-valued witness engine refuses the shared latent. That
      -- crashed the whole compile, generate included, until
      -- static-refusals-become-absent-variants made it an absent variant with
      -- a recorded reason. (This case used item 4's negated log-normal of
      -- fuzz-admission-oracle-bugs until that compiled.) Not a crash, but
      -- still a lattice bug, so its own class (task
      -- admission-oracle-promised-variants-present): the non-vacuity check
      -- that the property sees an over-promise, under the over-promise label
      -- and filed in 'knownOverPromises'.
      rep <- oracleOn "main = draw x = Normal in draw a = x + Normal in draw b = x + Normal in (a, b)"
      assertNoViolation rep
      assertEqual "outcomes" [(ModeGenerate, "value"), (ModeProbability, "promised-absent"), (ModeIntegrate, "promised-absent")]
        (outcomesOf "main" rep)
      assertEqual "over-promises" [ModeProbability, ModeIntegrate] (map ckMode (overPromises rep))
      let (filed, unfiled) = partitionKnownOverPromises (overPromises rep)
      assertEqual "unfiled over-promises" [] (map renderViolation unfiled)
      assertEqual "filed under" ["fuzz-admission-over-promises", "fuzz-admission-over-promises"] (map snd filed)
  , testCase "the mixture-Fin repro (a historical F2 instance) honours the contract" $ do
      -- Task modality-mixture-fin-joins-not-meets (haskell-dppl d0ab543): the
      -- lattice used to type this finite-support, admit it, and crash the IR
      -- compiler's catch-all. Re-seeding that bug (meetGroundMixture = meetGround)
      -- makes this case fail with the crash attributed to main's probability
      -- variant -- the check that the oracle reaches the class it is for.
      rep <- oracleOn "main = (if Uniform < 0.5 then 1.0 else Uniform) + Normal"
      assertNoViolation rep
      assertEqual "outcomes" [(ModeGenerate, "value")] (outcomesOf "main" rep)
  , testCase "finite-by-type is not an enumerable domain: a clean Bottom, not an over-promise" $ do
      -- Task finiteness-single-producer: two untagged random Bools combined
      -- were 'Finite' by their type, keepD admitted a density, and the IR
      -- compiler refused both inference variants (the refusal bucket).
      rep <- oracleOn "main = isLeft (if Uniform < 0.5 then left Normal else right 1.0) && isLeft (if Uniform < 0.3 then left Normal else right 2.0)"
      assertNoViolation rep
      assertEqual "verdict" (Just Bottom) (verdictOf "main" rep)
      assertEqual "outcomes" [(ModeGenerate, "value")] (outcomesOf "main" rep)
  , testCase "every known violation family names a doc" $
      assertEqual "entries without a doc" [] [ n | (n, d) <- knownAdmissionCrashes ++ knownOverPromises, null d ]
  ]
  where
    oracleOn src = case tryParseProgram "<admission>" src of
      Left err -> assertFailure (show err) >> error "unreachable"
      Right p  -> admissionCheck defaultCompilerConfig p []
    assertNoViolation rep = assertEqual "violations" [] (map renderViolation (violations rep))
    outcomesOf f (Checked _ cs) = [ (ckMode c, outcomeBucket (ckOutcome c)) | c <- cs, ckFunction c == f ]
    outcomesOf _ (NotTyped why) = [(ModeCompile, "not typed: " ++ why)]
    verdictOf f (Checked vs _) = lookup f vs
    verdictOf _ _ = Nothing
