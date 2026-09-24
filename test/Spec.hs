{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

import Test.QuickCheck hiding (verbose)
import Test.Tasty (TestTree, testGroup, defaultMain, localOption)
import Test.Tasty.QuickCheck (testProperties, QuickCheckMaxRatio(..))
import System.Environment (lookupEnv, setEnv)
import Data.Maybe (isNothing)

import SPLL.Examples
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import SPLL.Validator
import Control.Monad.Random.Lazy (evalRandIO)
import SPLL.Parser
import TestParser (parserTests)
import TestInternals (internalsTests, slowInternalsTests)
import TestObservationMask (observationMaskTests)
import TestRejection (rejectionTests)
import TestModality (modalityTests)
import TestModalityInfer (modalityInferTests)
import TestDeterminism (determinismTests)
import TestWriteLogitsProperties (writeLogitsTests, writeLogitsRoundtripTests)
import TestShowcase (showcaseTests)
import End2EndTesting (end2endTests, slowEnd2EndTests, selectPassDifferentialTests, batchedPythonTests, slowBatchedPythonTests, batchedRefusalTests, batchedAdtCdfNaNGuardTests, batchedEnumBucketingTests, branchCountBackendTests)
import TestKnownIssues (knownIssuesTests)
import TestFuzz (fuzzTests, shrinkerTests, superSlowFuzzTests, errorChannelTests,
                 neuralGeneratorTests, arrowGeneratorTests, fuzzScalingTests,
                 injFCatalogTests)
import TestCaseParser (parseProgram, corpusPplPath)
import TestSupport (topKConf, topKBCConf, bcConf, irDensity, reasonablyClose, expectCompiled)
import SPLL.Prelude
import qualified SPLL.CodeGenPyTorch
import qualified SPLL.CodeGenJulia
import Data.List (isInfixOf)


normalPDF :: Double -> Double
normalPDF x = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)

invalidTestCases :: [Program]
invalidTestCases = [invalidDuplicateDecl1, invalidDuplicateDecl2, invalidDuplicateDecl3, invalidDuplicateDecl4, invalidDuplicateDecl5, invalidMissingDecl, invalidMissingInjF, invalidReservedName, invalidReservedName2, invalidWrongArgCount]

prop_CheckInvalidPrograms :: Property
prop_CheckInvalidPrograms = forAll (elements invalidTestCases) checkInvalidPrograms

prop_TopK :: Property
prop_TopK = once $ ioProperty $ do
  let actualOutput0 = irDensity (topKConf 0.1) testTopK (VFloat 0) []
  let actualOutput1 = irDensity (topKConf 0.1) testTopK (VFloat 1) []
  case (actualOutput0, actualOutput1) of
    (VProbDim a _, VProbDim b _) -> return $ (b == 0.95) && (a == 0)
    _ -> return False

-- DO NOT CHANGE THIS CODE WITHOUT ALSO CHANGING THE CODE IN THE README
prop_CheckReadmeCodeListing1 :: Property
prop_CheckReadmeCodeListing1 = ioProperty $ do
  let twoDice = Program [("main", dice 6 #<+># dice 6)] [] [] []
  case runGen defaultCompilerConfig twoDice [] of
    Left err -> return $ counterexample err False
    Right gen' -> do
      gen <- evalRandIO gen'
      case runProb defaultCompilerConfig twoDice [] gen of
        Left err -> return $ counterexample err False
        Right (VProbDim prob _dim) -> do
          -- Original Listing above, Tests below
          if gen == (VInt 2) || gen == (VInt 12) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 1/36)
          else if gen == (VInt 3) || gen == (VInt 11) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 2/36)
          else if gen == (VInt 4) || gen == (VInt 10) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 3/36)
          else if gen == (VInt 5) || gen == (VInt 9) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 4/36)
          else if gen == (VInt 6) || gen == (VInt 8) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 5/36)
          else if gen == (VInt 7) then
            return $ (VFloat prob) `reasonablyClose` (VFloat $ 6/36)
          else
            return $ counterexample ("No valid dice roll " ++ show gen) False
        Right other -> return $ counterexample ("probability query returned " ++ show other
                                                 ++ ", not a (prob, dim) pair") False

-- DO NOT CHANGE THIS CODE WITHOUT ALSO CHANGING THE CODE IN THE README
prop_CheckReadmeCodeListing2 :: Property
prop_CheckReadmeCodeListing2 = ioProperty $ do
  let dist = Program [("main", normal #*# constF 2 #+# constF 1)] [] [] []
  case runGen defaultCompilerConfig dist [] of
    Left err -> return $ counterexample err False
    Right gen' -> do 
      gen <- evalRandIO gen'
      case runProb defaultCompilerConfig dist [] gen of
        Left err -> return $ counterexample err False
        Right (VProbDim prob _dim) -> case gen of
          -- Original Listing above, Tests below
          VFloat genF ->
            return $ (VFloat prob) `reasonablyClose` (VFloat (normalPDF ((genF - 1) / 2) / 2))
          other -> return $ counterexample ("expected a float sample, got " ++ show other) False
        Right other -> return $ counterexample ("probability query returned " ++ show other
                                                 ++ ", not a (prob, dim) pair") False

checkInvalidPrograms :: Program -> Property
checkInvalidPrograms p = case validateProgram p of
  Left _ -> property True
  Right _ -> counterexample "Program validates even though it should not" False

-- Two-level nesting: inner true branch has global prob 0.12*0.12=0.0144 < thresh=0.1, so it is
-- pruned by global topK but would survive local topK (local condT=0.12 > 0.1).
prop_TopKNestedPrunesDeeper :: Property
prop_TopKNestedPrunesDeeper = once $ ioProperty $ do
  let twoLevel = Program [("main",
        ifThenElse (bernoulli 0.12)
          (ifThenElse (bernoulli 0.12) (constF 1.0) (constF 0.0))
          (constF 2.0))] [] [] []
  let topKResult = irDensity (topKConf 0.1) twoLevel (VFloat 1.0) []
  let exactResult = irDensity defaultCompilerConfig twoLevel (VFloat 1.0) []
  case (topKResult, exactResult) of
    (VProbDim topKP _, VProbDim exactP _) ->
      return $ counterexample ("global topK P(1.0)=" ++ show topKP ++ ", expected 0") (topKP == 0.0)
             .&&. counterexample ("exact P(1.0) should be 0.0144") (VFloat exactP `reasonablyClose` VFloat 0.0144)
    _ -> return $ counterexample "Return type was no tuple" False

-- Cross-function: accProb passes through a _prob call boundary.
-- main = if bernoulli(0.12) then inner else 2.0
-- inner = if bernoulli(0.12) then 1.0 else 0.0
-- With thresh=0.1: main's true branch has accProb=0.12, inner receives it;
-- inner's true branch has global prob 0.12*0.12=0.0144 < 0.1 → pruned, P(1.0)=0.
prop_TopKCrossFunction :: Property
prop_TopKCrossFunction = once $ ioProperty $ do
  let crossFunc = Program
        [ ("main",  ifThenElse (bernoulli 0.12) (var "inner") (constF 2.0))
        , ("inner", ifThenElse (bernoulli 0.12) (constF 1.0) (constF 0.0)) ]
        [] [] []
  let topKResult = irDensity (topKConf 0.1) crossFunc (VFloat 1.0) []
  let exactResult = irDensity defaultCompilerConfig crossFunc (VFloat 1.0) []
  case (topKResult, exactResult) of
    (VProbDim topKP _, VProbDim exactP _) ->
      return $ counterexample ("global topK P(1.0)=" ++ show topKP ++ ", expected 0") (topKP == 0.0)
             .&&. counterexample ("exact P(1.0) should be 0.0144") (VFloat exactP `reasonablyClose` VFloat 0.0144)
    _ -> return $ counterexample "Return type was no tuple" False

-- BC counts both if-else leaf branches and InjF enumerable branches.
-- testDiceAdd = plusI(dice6, dice6): for P(sum=7), all 6 die combinations are valid,
-- so without topK BC=6.  With threshold=0.2 (>1/6), accProb*(1/6)<0.2 → all 6 pruned → BC=0.
prop_TopKFewerBranches :: Property
prop_TopKFewerBranches = once $ ioProperty $ do
  let topKBCResult = irDensity (topKBCConf 0.2) testDiceAdd (VInt 7) []
  let noBCResult   = irDensity bcConf           testDiceAdd (VInt 7) []
  case (topKBCResult, noBCResult) of
    (VProbDimBC _ _ topKBC, VProbDimBC _ _ noBC) ->
      return $ counterexample (show topKBC ++ " >= " ++ show noBC ++ " (topK should reduce branch count when a branch is pruned)") (topKBC < noBC)
    _ -> return $ counterexample "Return type was no tuple" False

-- Higher threshold prunes more InjF enum branches: BC(high_thresh) ≤ BC(low_thresh).
-- testDiceAdd at P(sum=7): each d6 face has P=1/6.
--   threshold=0.1 (<1/6): accProb*(1/6)>0.1 → all 6 branches kept → BC=6
--   threshold=0.2 (>1/6): accProb*(1/6)<0.2 → all 6 branches pruned → BC=0
prop_TopKMonotonicBranches :: Property
prop_TopKMonotonicBranches = once $ ioProperty $ do
  let bcLow  = irDensity (topKBCConf 0.1) testDiceAdd (VInt 7) []
  let bcHigh = irDensity (topKBCConf 0.2) testDiceAdd (VInt 7) []
  case (bcLow, bcHigh) of
    (VProbDimBC _ _ lowBC, VProbDimBC _ _ highBC) ->
      return $ counterexample (show highBC ++ " > " ++ show lowBC ++ " (higher threshold should prune at least as much)") (highBC <= lowBC)
    _ -> return $ counterexample "Return type was no tuple" False

-- BC for if-else: each leaf emits 1, IfThenElse uses formula cond+left+right-1.
-- A 3-leaf if-else (if b then (if b2 then uniform else 3.0) else 1.0) should give BC=3.
-- inner: cond(1)+uniform(1)+const3(1)-1=2; outer: cond(1)+2+const1(1)-1=3.
prop_BCLeafCountIfElse :: Property
prop_BCLeafCountIfElse = once $ ioProperty $ do
  let prog = Program [("main", ifThenElse (bernoulli 0.5) (ifThenElse (bernoulli 0.5) uniform (constF 3.0)) (constF 1.0))] [] [] []
  let result = irDensity bcConf prog (VFloat 0.5) []
  case result of
    VProbDimBC _ _ bc -> return $ counterexample ("Expected BC=3, got " ++ show bc) (bc == 3.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- dice 6 is a pure if-else tree with 6 leaves. BC should equal 6 for any query.
-- dice1=1; dice(n)=cond(1)+constI(n)(1)+dice(n-1)-1 = dice(n-1)+1; so dice(6)=6.
prop_BCDiceIfElse :: Property
prop_BCDiceIfElse = once $ ioProperty $ do
  let result = irDensity bcConf testDice (VInt 3) []
  case result of
    VProbDimBC _ _ bc -> return $ counterexample ("Expected BC=6, got " ++ show bc) (bc == 6.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- Consistency: dice6 as if-else (BC=6) and testDiceAdd as InjF (BC=6 for P(7)) agree.
prop_BCConsistency :: Property
prop_BCConsistency = once $ ioProperty $ do
  let diceResult    = irDensity bcConf testDice    (VInt 3) []
  let diceAddResult = irDensity bcConf testDiceAdd (VInt 7) []
  case (diceResult, diceAddResult) of
    (VProbDimBC _ _ diceBC, VProbDimBC _ _ diceAddBC) ->
      return $ counterexample ("dice BC=" ++ show diceBC ++ ", diceAdd BC=" ++ show diceAddBC ++ " (expected both=6)") (diceBC == diceAddBC)
    _ -> return $ counterexample "Return type was no tuple" False

-- Leaf-anchor consistency (task bc-recursive-prob-divergence). Branch count is
-- anchored on "every terminal leaf resolution counts 1, deterministic or
-- random", so the same deterministic value carried into the same branch
-- position must produce the same count regardless of which AST constructor
-- spells it. These three programs are the same distribution, reached through
-- three different toIRInference leaf cases:
--   x          -- Var-is-a-local-variable
--   x + 0.0    -- InjF with no probabilistic parameter
--   ident x    -- deterministic Apply (closure applied to a deterministic arg)
-- All three must agree AND equal 2 (one leaf per if-arm: the leaf under test,
-- plus the constant 3.0 in the else). The absolute value is pinned as well as
-- the agreement because before the fix all three sites returned 0 branches --
-- they agreed with each other at BC=1 (the outer if's condition alone, via the
-- old cond+left+right-1 formula) while every one of them was wrong.
prop_BCLeafSpellingIndependence :: Property
prop_BCLeafSpellingIndependence = once $ ioProperty $ do
  let srcs = [ ("bare Var",              "f x = if Uniform < 0.5 then x else 3.0\nmain = f 2.0")
             , ("InjF, no prob param",   "f x = if Uniform < 0.5 then x + 0.0 else 3.0\nmain = f 2.0")
             , ("deterministic Apply",   "ident y = y\nf x = if Uniform < 0.5 then ident x else 3.0\nmain = f 2.0") ]
  return $ conjoin
    [ case tryParseProgram lbl src of
        Left err -> counterexample ("parse failed for " ++ lbl ++ ": " ++ show err) False
        Right prog -> case irDensity bcConf prog (VFloat 2.0) [] of
          VProbDimBC _ _ bc -> counterexample (lbl ++ ": expected BC=2, got " ++ show bc) (bc == 2.0)
          x -> counterexample (lbl ++ ": unexpected result shape: " ++ show x) False
    | (lbl, src) <- srcs ]

-- Recursion-depth fidelity (task bc-recursive-prob-divergence). test/cases/conditionals/dice.ppl
-- is genuinely self-recursive (dice x = ... else dice (x-1), from dice 4.0), unlike
-- the dice 6 builder above which is a Haskell-side unrolled if-tree. Its branch
-- count must be exactly the recursion depth, 4 -- one leaf resolution per level --
-- and independent of the queried value, since only the recursion-control conditions
-- (x == 1.0, Uniform < 1/x) decide which paths are dead, never the sample. Two
-- separate bugs used to show up right here: the count diverged outright (the dead
-- arm's recursive call was evaluated strictly, so x counted down past 1.0 forever),
-- and once that was fixed it collapsed to a constant 1.0 (every level's leaf was a
-- bare Var, which contributed 0). 5.0 is out of support: probability 0, but the
-- compiled artifact still traverses the same 4 leaves.
prop_BCRecursiveDiceDepth :: Property
prop_BCRecursiveDiceDepth = once $ ioProperty $ do
  prog <- corpusPplPath "dice" >>= parseProgram
  return $ conjoin
    [ case irDensity bcConf prog (VFloat v) [] of
        VProbDimBC _ _ bc -> counterexample ("p(" ++ show v ++ "): expected BC=4, got " ++ show bc) (bc == 4.0)
        x -> counterexample ("p(" ++ show v ++ "): unexpected result shape: " ++ show x) False
    | v <- [1.0, 2.0, 3.0, 4.0, 5.0] ]

-- dice 6 has equal 1/6 marginal probability per face regardless of tree structure.
-- Global topK therefore either prunes all branches or none:
--   threshold=0.1 (<1/6): accumulated prob of every branch is ~1/6 > 0.1 → nothing pruned, P(3)=1/6
--   threshold=0.2 (>1/6): accumulated prob of every branch is ~1/6 < 0.2 → all pruned, P(3)=0
-- Local topK would behave differently because the raw bernoulli probabilities vary by depth.
prop_TopKDiceAllOrNothing :: Property
prop_TopKDiceAllOrNothing = once $ ioProperty $ do
  let low   = irDensity (topKConf 0.1)        testDice (VInt 3) []
  let high  = irDensity (topKConf 0.2)        testDice (VInt 3) []
  let exact = irDensity defaultCompilerConfig testDice (VInt 3) []
  case (low, high, exact) of
    (VProbDim lowP _, VProbDim hP _, VProbDim exactP _) ->
      return $ VFloat lowP `reasonablyClose` VFloat exactP
            .&&. counterexample ("threshold=0.2 should prune all branches: P=" ++ show hP) (hP == 0.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- testDiceAdd = plusI(dice, dice): InjF enumerates discrete values of the left arg.
-- Each d6 face has P=1/6; InjF branch filter is (accProb * pLeft > threshold).
--   threshold=0.1 (<1/6): 1.0*(1/6)=0.167 > 0.1 → all enum branches kept, P(7)=6/36
--   threshold=0.2 (>1/6): 1.0*(1/6)=0.167 < 0.2 → all enum branches pruned, P(7)=0
prop_TopKInjFEnum :: Property
prop_TopKInjFEnum = once $ ioProperty $ do
  let low   = irDensity (topKConf 0.1)        testDiceAdd (VInt 7) []
  let high  = irDensity (topKConf 0.2)        testDiceAdd (VInt 7) []
  let exact = irDensity defaultCompilerConfig testDiceAdd (VInt 7) []
  case (low, high, exact) of
    (VProbDim lowP _, VProbDim hP _, VProbDim exactP _) ->
      return $ VFloat lowP `reasonablyClose` VFloat exactP
            .&&. counterexample ("threshold=0.2 should prune all InjF enum branches: P=" ++ show hP) (hP == 0.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- Parses test/cases/conditionals/dice.ppl (d4, equal P=0.25 per face) and runs it through the full
-- parsing + compilation pipeline with topK enabled, via the public runProb API
-- (which threads the initial acc_prob for topK-compiled programs).
-- threshold=0.1 (<0.25): no branch is pruned; each face should have P=0.25.
prop_TopKEndToEnd :: Property
prop_TopKEndToEnd = once $ ioProperty $ do
  prog <- corpusPplPath "dice" >>= parseProgram
  let results = map (\v -> irDensity (topKConf 0.1) prog (VFloat v) []) [1.0, 2.0, 3.0, 4.0]
  return $ conjoin
    [ case r of
        VProbDim p _ -> VFloat p `reasonablyClose` VFloat 0.25
        x -> counterexample ("Unexpected result shape: " ++ show x) False
    | r <- results ]

-- testConditionalLambdaBC: named deterministic selector applied to a coin-flip argument.
-- Routes through IsConditional + toIREnumerate path in IRCompiler.
-- Argument has 2 discrete values; each iteration traverses one if-else arm → BC = 2.
prop_BCConditionalLambda :: Property
prop_BCConditionalLambda = once $ ioProperty $ do
  let result = irDensity bcConf testConditionalLambdaBC (VFloat 1.0) []
  case result of
    VProbDimBC _ _ bc ->
      return $ counterexample ("Expected BC=2, got " ++ show bc) (bc == 2.0)
    _ -> return $ counterexample ("Unexpected result shape: " ++ show result) False

-- Investigation program-equivalence-invariants, required invariant #1:
-- `apply (var "f") (discrete_arg)` (routed through IsConditional + toIREnumerate,
-- same shape as testConditionalLambdaBC above) vs. the fully hand-inlined
-- if-else over the same discrete argument must agree on (prob, dim, bc) at
-- every query point. This is the exact program pair the investigation
-- reported diverging (named selector: BC=0, inline if-else: BC>=2); as of
-- task bc-recursive-prob-divergence's anchor fix (43017e4) the two agree.
prop_BCNamedConditionalEqualsInline :: Property
prop_BCNamedConditionalEqualsInline = once $ ioProperty $ do
  let coin = ifThenElse (bernoulli 0.5) (constF 2.0) (constF 1.0)
      named = Program
        [ ("main",     apply (var "selector") coin)
        , ("selector", "x" #-># ifThenElse (var "x" #># constF 1.5) (constF 1.0) (constF 0.0))
        ] [] [] []
      inlined = Program
        [ ("main", ifThenElse (coin #># constF 1.5) (constF 1.0) (constF 0.0)) ] [] [] []
  return $ conjoin
    [ case (irDensity bcConf named (VFloat q) [], irDensity bcConf inlined (VFloat q) []) of
        (VProbDimBC pN dN bcN, VProbDimBC pI dI bcI) ->
          counterexample
            ("q=" ++ show q ++ ": named=(" ++ show pN ++ "," ++ show dN ++ "," ++ show bcN
              ++ ") inline=(" ++ show pI ++ "," ++ show dI ++ "," ++ show bcI ++ ")")
            (pN == pI && dN == dI && bcN == bcI)
        (r1, r2) -> counterexample ("Unexpected result shapes: " ++ show r1 ++ ", " ++ show r2) False
    | q <- [0.0, 1.0] ]

-- Investigation program-equivalence-invariants, required invariant #3:
-- a named non-conditional wrapper function applied to an enumerable argument
-- must give the same (prob, dim, bc) as inlining the wrapper's body at the
-- call site, for the callee's own contribution -- "a call forwards the
-- callee's own count unmodified" (CLAUDE.md, Branch Counting).
prop_BCNamedWrapperEqualsInline :: Property
prop_BCNamedWrapperEqualsInline = once $ ioProperty $ do
  let coin = ifThenElse (bernoulli 0.5) (constF 2.0) (constF 1.0)
      named = Program
        [ ("main", apply (var "wrap") coin)
        , ("wrap", "x" #-># injF "plus" [var "x", constF 1.0])
        ] [] [] []
      inlined = Program
        [ ("main", injF "plus" [coin, constF 1.0]) ] [] [] []
  return $ conjoin
    [ case (irDensity bcConf named (VFloat q) [], irDensity bcConf inlined (VFloat q) []) of
        (VProbDimBC pN dN bcN, VProbDimBC pI dI bcI) ->
          counterexample
            ("q=" ++ show q ++ ": named=(" ++ show pN ++ "," ++ show dN ++ "," ++ show bcN
              ++ ") inline=(" ++ show pI ++ "," ++ show dI ++ "," ++ show bcI ++ ")")
            (pN == pI && dN == dI && bcN == bcI)
        (r1, r2) -> counterexample ("Unexpected result shapes: " ++ show r1 ++ ", " ++ show r2) False
    | q <- [2.0, 3.0] ]

-- killAll coverage: a program that calls a sub-function via Var with a non-trivial
-- change-of-variables correction.  testNormalScaledViaVar uses injF "mult" with factor
-- 2.0, whose inverse derivative is 1/2.  If killAll fails to rewrite the dim extraction
-- from the sub-function result (IRDestruct AcFst(IRDestruct AcSnd(IRVar x)) → IRDestruct AcSnd(IRVar x)), dim would
-- be 0 and the CoV factor would be skipped, giving normalPDF(1.0) instead of
-- the correct normalPDF(1.0) * 0.5.
-- P(main = 2.0) = normalPDF(1.0) * 0.5.
prop_killAllVarExtraction :: Property
prop_killAllVarExtraction = once $ ioProperty $ do
  let result = irDensity defaultCompilerConfig testNormalScaledViaVar (VFloat 2.0) []
  case result of
    VProbDim p _ ->
      return $ counterexample ("Expected normalPDF(1)*0.5≈" ++ show (normalPDF 1.0 * 0.5) ++ ", got " ++ show p)
        (abs (p - normalPDF 1.0 * 0.5) < 1e-6)
    _ -> return $ counterexample ("Unexpected shape: " ++ show result) False

-- Enabling countBranches must not alter probability values, only add a third field.
-- Verify on testDice that P(X=3) is the same with and without branch counting.
prop_BCDoesNotChangeProbability :: Property
prop_BCDoesNotChangeProbability = once $ ioProperty $ do
  let withBC    = irDensity bcConf testDice (VInt 3) []
  let withoutBC = irDensity defaultCompilerConfig testDice (VInt 3) []
  case (withBC, withoutBC) of
    (VProbDim pBC _, VProbDim pNone _) ->
      return $ counterexample
        ("P with BC=" ++ show pBC ++ " /= P without BC=" ++ show pNone)
        (abs (pBC - pNone) < 1e-9)
    _ -> return $ counterexample
      ("Unexpected result shapes: " ++ show withBC ++ ", " ++ show withoutBC) False

-- stripBranchCount structural check: countBranches=False must drop the branch
-- count from the result and nothing else.  The result always carries the
-- impossibility flag as its last field (design inference-result-side-channels),
-- so the layouts are (prob, (dim, (bc, imposs))) and (prob, (dim, imposs)) --
-- what this pins is that exactly the bc slot disappears.
-- Also exercises the killAll IRVar path: testDice's main calls the dice sub-expression
-- via Var, so killAll must rewrite the bc/flag extractions from the called
-- function's result to the shortened layout.
prop_stripBranchCountReturnShape :: Property
prop_stripBranchCountReturnShape = once $ ioProperty $ do
  let withBC    = irDensity bcConf testDice (VInt 3) []
  let withoutBC = irDensity defaultCompilerConfig testDice (VInt 3) []
  let hasBC (VTuple _ (VTuple _ (VTuple _ (VBool _)))) = True
      hasBC _                                          = False
      noBC  (VTuple _ (VTuple _ (VBool _)))            = True
      noBC  _                                          = False
  return $
    counterexample ("countBranches=True should return (p, (d, (bc, imposs))), got: " ++ show withBC)
      (hasBC withBC)
    .&&.
    counterexample ("countBranches=False should return (p, (d, imposs)), got: " ++ show withoutBC)
      (noBC withoutBC)

-- When topKThreshold is set, IREnv should contain exactly one constant named TOP_K_CUTOFF
-- with the value matching the config.
prop_TopKConstantPresentInEnv :: Property
prop_TopKConstantPresentInEnv = once $ ioProperty $ do
  let conf = defaultCompilerConfig { topKThreshold = Just 0.005 }
      irEnv = expectCompiled (compile conf testDice)
      IREnv _ _ consts = irEnv
  return $ case lookup "TOP_K_CUTOFF" consts of
    Just (VFloat v) -> counterexample ("Expected 0.005, got " ++ show v) (abs (v - 0.005) < 1e-12)
    Just other      -> counterexample ("Expected VFloat, got " ++ show other) False
    Nothing         -> counterexample "TOP_K_CUTOFF constant absent from IREnv" False

-- When topKThreshold is Nothing, no TOP_K_CUTOFF constant should appear in IREnv.
prop_TopKConstantAbsentWithoutFlag :: Property
prop_TopKConstantAbsentWithoutFlag = once $ ioProperty $ do
  let irEnv = expectCompiled (compile defaultCompilerConfig testDice)
      IREnv _ _ consts = irEnv
  return $ counterexample "TOP_K_CUTOFF should not appear when topK is disabled"
    (isNothing (lookup "TOP_K_CUTOFF" consts))

-- The generated Python should contain a plain assignment `TOP_K_CUTOFF = <value>`,
-- not a class definition.
prop_TopKPythonConstantIsPlainAssignment :: Property
prop_TopKPythonConstantIsPlainAssignment = once $ ioProperty $ do
  let conf = defaultCompilerConfig { topKThreshold = Just 0.001 }
      irEnv = expectCompiled (compile conf testDice)
      pyLines = SPLL.CodeGenPyTorch.generateFunctions True irEnv
  let hasAssignment = any ("TOP_K_CUTOFF = " `isInfixOf`) pyLines
      hasClass       = any ("class TOP_K_CUTOFF" `isInfixOf`) pyLines
  return $ counterexample ("Expected plain assignment, lines: " ++ unlines pyLines)
    (hasAssignment && not hasClass)

-- The value in the generated Python assignment must match the threshold passed in.
prop_TopKPythonConstantValueMatchesConfig :: Property
prop_TopKPythonConstantValueMatchesConfig = once $ ioProperty $ do
  let thresh = 0.0042 :: Double
      conf = defaultCompilerConfig { topKThreshold = Just thresh }
      irEnv = expectCompiled (compile conf testDice)
      pyLines = SPLL.CodeGenPyTorch.generateFunctions True irEnv
      assignmentLines = filter ("TOP_K_CUTOFF = " `isInfixOf`) pyLines
  return $ case assignmentLines of
    [line] -> counterexample ("Assignment line: " ++ line)
                (show thresh `isInfixOf` line)
    other  -> counterexample ("Expected exactly one assignment line, got: " ++ show other) False

-- A log-space compile must render its zero as a literal the *target language*
-- knows. Haskell's 'show' spells the non-finite doubles @Infinity@/@-Infinity@/
-- @NaN@, and log space reaches them constantly -- its zero is @-1/0@
-- ('SPLL.Semiring.negInfIR'), so every impossible arm carries one. @Infinity@
-- is not a Python name and @-Infinity@ is not Julia syntax, so emitting it
-- produced code that died with a NameError at run time rather than failing the
-- compile.
--
-- The suite missed this for as long as it existed because the log-space corpus
-- properties route through the interpreter, which never renders a literal --
-- these two are the only tests that put a log-space compile through a text
-- backend.
--
-- Both halves are asserted deliberately: the "no bare Infinity" half is the
-- regression, and the "does emit the mapped literal" half is what keeps the
-- test from going vacuous if log-space zero ever stops reaching codegen.
prop_LogSpacePythonRendersInfinity :: Property
prop_LogSpacePythonRendersInfinity = once $ ioProperty $ do
  let conf = defaultCompilerConfig { logSpace = True }
      src  = unlines (SPLL.CodeGenPyTorch.generateFunctions True
                        (expectCompiled (compile conf testDice)))
  return $ counterexample ("emitted Python:\n" ++ src)
    (not ("Infinity" `isInfixOf` src) && "float('-inf')" `isInfixOf` src)

prop_LogSpaceJuliaRendersInfinity :: Property
prop_LogSpaceJuliaRendersInfinity = once $ ioProperty $ do
  let conf = defaultCompilerConfig { logSpace = True }
      src  = unlines (SPLL.CodeGenJulia.generateFunctions
                        (expectCompiled (compile conf testDice)))
  return $ counterexample ("emitted Julia:\n" ++ src)
    (not ("Infinity" `isInfixOf` src) && "-Inf" `isInfixOf` src)

-- The interpreter must resolve IRVar "TOP_K_CUTOFF" via the constant in IREnv:
-- a topK compile with threshold=0.001 on testDice should agree with exact inference
-- (all branches kept since 1/6 >> 0.001).
prop_TopKConstantResolvedByInterpreter :: Property
prop_TopKConstantResolvedByInterpreter = once $ ioProperty $ do
  let withTopK = irDensity (topKConf 0.001)      testDice (VInt 3) []
  let exact    = irDensity defaultCompilerConfig testDice (VInt 3) []
  case (withTopK, exact) of
    (VProbDim topKP _, VProbDim exactP _) ->
      return $ VFloat topKP `reasonablyClose` VFloat exactP
    _ -> return $ counterexample "Return type was no tuple" False

return []

specTests :: TestTree
specTests = localOption (QuickCheckMaxRatio 20) $ testProperties "Spec" $(allProperties)

main :: IO ()
main = do
  -- Quiet-on-success by default: only failures (and the summary line) are printed.
  -- tasty reads option defaults from TASTY_* environment variables, so setting it
  -- here (only when unset) keeps it overridable: TASTY_HIDE_SUCCESSES=false stack test
  -- prints the full test tree including per-test timings.
  hideSuccesses <- lookupEnv "TASTY_HIDE_SUCCESSES"
  if isNothing hideSuccesses then setEnv "TASTY_HIDE_SUCCESSES" "true" else return ()
  e2e <- end2endTests
  selectDiff <- selectPassDifferentialTests
  batchedPy <- batchedPythonTests
  branchCountBackends <- branchCountBackendTests
  detTests <- determinismTests
  showcase <- showcaseTests
  writeLogitsRoundtrip <- writeLogitsRoundtripTests
  knownIssues <- knownIssuesTests
  -- A handful of tests (deep plan enumeration, mainly) are expensive enough
  -- to noticeably slow day-to-day `stack test` while rarely catching
  -- regressions outside the code they pin. They're skipped unless
  -- NEST_SLOW_TESTS is set, e.g. `NEST_SLOW_TESTS=1 stack test --ta '-p Slow'`.
  runSlow <- lookupEnv "NEST_SLOW_TESTS"
  slow <- if isNothing runSlow then return (testGroup "Slow" []) else do
    slowE2e <- slowEnd2EndTests
    slowBatchedPy <- slowBatchedPythonTests
    return $ testGroup "Slow" [slowInternalsTests, slowE2e, slowBatchedPy, fuzzTests]
  -- 'prop_Fuzz_SamplingMatchesPDF' (the sampling-vs-PDF cross-check between
  -- `generate` and `probability`) draws up to tens of thousands of forward
  -- samples per case, dwarfing every other Slow test's runtime, so it gets
  -- its own further opt-in tier: `NEST_SUPERSLOW_TESTS=1 stack test --ta '-p SuperSlow'`.
  runSuperSlow <- lookupEnv "NEST_SUPERSLOW_TESTS"
  let superSlow = if isNothing runSuperSlow then testGroup "SuperSlow" [] else testGroup "SuperSlow" [superSlowFuzzTests]
  -- The Corpus group lives in its own test-suite (haskell-dppl-test-corpus,
  -- module TestCorpus) and its own OS process, not here: see TestCorpus's
  -- module haddock for why (it compiles the whole corpus 8x over and, kept
  -- alive by tasty's TestTree for the rest of this process's life, that was
  -- driving stack test to an OOM kill).
  defaultMain $ testGroup "Tests"
    [ specTests
    , parserTests
    , internalsTests
    , observationMaskTests
    , shrinkerTests
    , neuralGeneratorTests
    , arrowGeneratorTests
    , errorChannelTests
    , fuzzScalingTests
    , injFCatalogTests
    , rejectionTests
    , modalityTests
    , modalityInferTests
    , detTests
    , writeLogitsTests
    , writeLogitsRoundtrip
    , showcase
    , knownIssues
    , e2e
    , selectDiff
    , batchedPy
    , batchedRefusalTests
    , batchedAdtCdfNaNGuardTests
    , batchedEnumBucketingTests
    , branchCountBackends
    , slow
    , superSlow
    ]
