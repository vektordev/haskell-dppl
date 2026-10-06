{-# LANGUAGE PatternSynonyms #-}
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
-- program's own @.tst@ query points.
module TestRewrites (rewriteTests, rewriteCorpusTests) where

import Control.Concurrent (forkIO, getNumCapabilities)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.QSem (newQSem, signalQSem, waitQSem)
import Control.Exception (SomeException, bracket_, evaluate, throwIO, try)
import Control.Monad (forM, replicateM)
import Control.Monad.Random.Lazy (evalRandIO)
import Data.List (intercalate, isInfixOf, nub)
import Data.Maybe (isJust)
import qualified Data.Set as Set
import System.FilePath (takeBaseName)
import System.Timeout (timeout)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, testCaseInfo, assertBool, assertFailure, (@?=))

import SPLL.Lang.Types
import SPLL.Lang.Lang (freeVarsExpr)
import SPLL.IntermediateRepresentation (IRValue, defaultCompilerConfig, pattern VProbDim)
import SPLL.Parser (tryParseProgram)
import SPLL.Prelude (compile, runProbC, runGenC)
import TestCaseParser (parseTestCases, TestCase(..), Backend(..))
import End2EndTesting (getAllTestFiles)
import TestTolerances (probTolerance, samplingTolerance)
import Rewrites

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
-- * 'DrawIntro', 'LinearInline': M6, dispatch-on-law-certificates.
refusalIsHard :: Family -> Bool
refusalIsHard AliasIntro = False
refusalIsHard HelperExtract = False
refusalIsHard DrawIntro = False
refusalIsHard LinearInline = False

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
  -- `draw z = Normal in 0.0 * z`: the random factor bound instead of the
  -- zero. (The zero bound, `draw z = 0.0 in z * Normal`, agrees since
  -- fuzz-admission-oracle-bugs item 6: a factor whose value set is {0} is the
  -- absorbing element.)
  [ Known "probe10" DrawIntro "draw-intro Normal" zeroRandomBound
  , Known "multDeterministicZero" DrawIntro "draw-intro Normal" zeroRandomBound
  -- A structured random value read through a second binder -- an alias, or
  -- a helper's parameter -- loses a field's constraint.
  , Known "drawDestructuredShared" DrawIntro "" structuredReread
  , Known "drawDestructuredShared" AliasIntro "" structuredReread
  , Known "drawDestructuredShared" HelperExtract "" structuredReread
  , Known "setWitnessTupleDisjointFields" HelperExtract "" structuredReread
  , Known "letBoundEitherDestructure" HelperExtract "isLeft" structuredReread
  -- `isR m = isRight m` on the draw-bound Maybe m: every point query answers
  -- P(isRight) = 0.5, the payload's density dropped. Pre-existing (the same
  -- 0.5 at the base compiler); exposed when observeMaybePayloadRightAny left
  -- known-issues for the corpus.
  , Known "observeMaybePayloadRightAny" HelperExtract "isRight" structuredReread
  -- The swapped wrapper re-read through a second binder: before per-mask
  -- variants the concrete query refused ("binding 'x' is unobserved"); f's
  -- variants now answer the split sub-queries, so p((0.7, 0.6)) is 1.0
  -- instead of impossible.
  , Known "maskSwappedWrapper" DrawIntro "" variantsSilenceReread
  , Known "maskSwappedWrapper" AliasIntro "" variantsSilenceReread
  , Known "maskSwappedWrapper" HelperExtract "" variantsSilenceReread
  -- `draw z = Normal in draw x0 = z in (x0, 0.5 * Normal)`: re-binding the
  -- witnessed draw through an alias applies a scaled sibling draw's Jacobian
  -- twice (p((0, 0)) = 4 phi(0)^2, not 2 phi(0)^2). Pre-existing; exposed when
  -- ouChainUnrolled joined the corpus.
  , Known "ouChainUnrolled" DrawIntro "draw-intro Normal" aliasDoubleJacobian
  , Known "ouChainUnrolled" AliasIntro "" aliasDoubleJacobian
  ]
  where
    zeroRandomBound = "draw-bound-random-factor-times-literal-zero-loses-dirac-mass"
    aliasDoubleJacobian = "aliased-draw-scaled-sibling-double-jacobian"
    structuredReread = "structured-draw-reread-through-binder-drops-field"
    variantsSilenceReread = "mask-variants-silence-reread-refusal-into-wrong-result"

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
data Outcome = Answered [(Double, Double)] | Refused String

-- | Compile at the default config and answer every query. Any failure --
-- a 'Left', a missing probability function, a crash or a timeout -- is
-- 'Refused' with its message; the whole run is one outcome.
runQueries :: Program -> [Query] -> IO Outcome
runQueries p qs = do
  r <- timeout (20 * 1000000) (try (evaluate (forceOutcome (answer p qs))))
  return $ case r of
    Nothing -> Refused "timeout (20s)"
    Just (Left ex) -> Refused ("crash: " ++ firstLine (show (ex :: SomeException)))
    Just (Right o) -> o
  where
    firstLine = shorten . takeWhile (/= '\n')

-- | Crash messages can carry a whole annotated AST; a log line needs the
-- diagnostic, not the dump.
shorten :: String -> String
shorten m = if length m > 160 then take 160 m ++ "..." else m

answer :: Program -> [Query] -> Outcome
answer p qs = case compile defaultCompilerConfig p of
  Left err -> Refused ("refused: " ++ shorten (takeWhile (/= '\n') err))
  Right env -> either (Refused . ("refused: " ++) . shorten . takeWhile (/= '\n')) Answered
                 (mapM (\(s, params) -> runProbC p env params s >>= probDim) qs)
  where
    probDim (VProbDim pr d) = Right (pr, d)
    probDim v = Left ("not a probability result: " ++ show v)

forceOutcome :: Outcome -> Outcome
forceOutcome o@(Answered xs) = sum (map (\(a, b) -> a + b) xs) `seq` o
forceOutcome o@(Refused m) = length m `seq` o

-- | Do two answers agree? Probability within 'probTolerance' (relative above
-- 1, since densities can be large), dim exactly -- unless both are zero, where
-- the dim carries no information. Two NaNs agree with each other only.
agrees :: (Double, Double) -> (Double, Double) -> Bool
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
  out <- runQueries rewritten qs
  case (origOut, out) of
    (Answered as, Answered bs)
      | and (zipWith agrees as bs) -> return Agree
      | otherwise ->
          let msg = site ++ "\n      original " ++ show as ++ "\n      rewritten " ++ show bs
          in return $ maybe (HardMismatch msg) (\k -> KnownMismatch k (msg ++ " [" ++ kDoc k ++ "]"))
                             (knownDivergence prog fam site)
    (Answered _, Refused why)
      | refusalIsHard fam -> return (HardRefusal (site ++ ": " ++ why))
      | otherwise -> return (LoggedRefusal (site ++ ": " ++ why))
    (Refused _, Refused _) -> return BothRefuse
    (Refused _, Answered bs) -> samplingCheck rewritten (zip qs bs)

-- | The refused -> answers transition: there is no second derivation, so the
-- answering program is checked against its own forward sampler, at every
-- query point where a window estimate is meaningful (a scalar or a tuple of
-- scalars, with dim 0 or dim equal to the continuous coordinate count, and at
-- most 1 -- a higher-dimensional estimate needs prohibitively many draws).
samplingCheck :: Program -> [(Query, (Double, Double))] -> IO Verdict
samplingCheck p rows = case compile defaultCompilerConfig p of
  Left err -> return (SampleUnchecked err)
  Right env -> do
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
          est = fromIntegral inside / fromIntegral n / (eps ** d)
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
  origOut <- runQueries p qs
  concurrently [ (,) (variantFamily v) <$> judge prog (variantFamily v) (variantSite v) origOut (variantProgram v) qs
               | fam <- allFamilies, v <- variants fam p ]

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
    line (f, v) = familyName f ++ ": " ++ case v of
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
      forward <- judge name fam "hand-written rewrite" ow pr qs
      backward <- judge name fam "hand-written rewrite, reversed" orr pw qs
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
  [ testCase "draw and literal application parse to the same AST" $
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
  ]
  where
    paramsOf (Expr _ (Lambda v b)) = v : paramsOf b
    paramsOf _ = []

-- ---------------------------------------------------------------------------
-- Corpus sweep
-- ---------------------------------------------------------------------------

rewriteTests :: TestTree
rewriteTests = testGroup "RewriteInvariance" [unitTests, probeTests]

-- | One test per corpus program: every family at every site, compared at the
-- program's own probability query points (both possible and impossible rows).
rewriteCorpusTests :: IO TestTree
rewriteCorpusTests = do
  files <- getAllTestFiles
  cases <- forM files $ \(ppl, tst) -> do
    (backends, slow, _, tcs) <- parseTestCases tst
    src <- readFile ppl
    return (takeBaseName ppl, parseSrc ppl src, backends, slow, tcs)
  let usable = [ (n, p, qs) | (n, p, backends, slow, tcs) <- cases
               , Interpreter `elem` backends, not slow, null (neurals p)
               , let qs = [(s, params) | ProbTestCase _ s params _ <- tcs], not (null qs) ]
  return $ testGroup "RewriteInvarianceCorpus"
    [ testCaseInfo n (sweep n p qs >>= report n) | (n, p, qs) <- usable ]
