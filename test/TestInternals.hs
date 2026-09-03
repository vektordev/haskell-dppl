{-# LANGUAGE TemplateHaskell #-}

module TestInternals (
  internalsTests,
  slowInternalsTests
) where

import SPLL.Lang.Lang
import SPLL.Lang.Types

import ArbitrarySPLL ()

import Test.QuickCheck hiding (collect, label, sample, total)
import SPLL.Typing.RInfer (tryAddRTypeInfo, RTypeError(..))
import SPLL.Typing.RType (RType(..))
import SPLL.Prelude
import SPLL.Parser (tryParseProgram)
import SPLL.Analysis (annotateEnumsProg, materializationDomain, withinMaterializationBudget)
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Typing.ForwardChaining (FCData, annotateProg, progToFCData, isInvertibleLambda, isWitnessedLambda)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import SPLL.AutoNeural (PartitionPlan(..), makePartitionPlan)
import SPLL.IntermediateRepresentation
import SPLL.Semiring (semiringSuffix)
import SPLL.IROptimizer (postProcess, optimizeEnv, deterministicGens, distributeIf, OptEnv(..))
import SPLL.CodeGenPyTorchBatched (adtEnv, batchedGuard, generateFunctionsBatched, structural)
import SPLL.IRCompiler (injFLatentVerdicts, materializationVerdicts)
import Data.Foldable (toList)
import Data.List (isInfixOf, intercalate)
import Control.Exception (try, evaluate, ErrorCall(..))
import System.Timeout (timeout)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertEqual, assertFailure, (@?=))
import IRInterpreter (generateDet)
import TestCaseParser (Backend(..), TestCase(..), expectationProb, defaultBackends, parseTestCasesFromString)
import Test.Tasty.QuickCheck (testProperties)
import System.Random (StdGen)
import Control.Monad.Random (Rand)
import Control.Monad (forM_)
import Data.Number.Erf (erf)


-- | The (prob, dim) pair a probability query must return; a different shape
-- is a compiler bug rather than a wrong number, so say which.
probDimOf :: IRValue -> (Double, Double)
probDimOf (VProbDim p d) = (p, d)
probDimOf v = error ("probability query returned " ++ show v ++ ", not a (prob, dim) pair")

-- | As 'probDimOf', for a countBranches build's (prob, dim, branchCount).
probDimBCOf :: IRValue -> (Double, Double, Double)
probDimBCOf (VProbDimBC p d bc) = (p, d, bc)
probDimBCOf v = error ("probability query returned " ++ show v ++ ", not a (prob, dim, bc) triple")

prop_tMapId :: Expr -> Property
prop_tMapId expr = tMap getTypeInfo expr === expr

prop_tMapMId :: Expr -> Property
prop_tMapMId expr = tMapM (return . getTypeInfo) expr === [expr]
    -- Ensures the test works with any monad that can be used with tMapM
    -- forAll (return . getTypeInfo) $ \typeInfoFunc ->
        -- Run tMapM and check if the result is identical to the original
        -- tMapM typeInfoFunc expr === return expr

-- Helper: type-check a single-function program
typechecks :: Program -> Bool
typechecks p = case tryAddRTypeInfo p of
  Right _ -> True
  Left _  -> False

-- GreaterType (SPLL.Typing.RType) is a transient unification device used only
-- inside RInfer's constraint solver (unifies/greaterType) to defer choosing
-- between two candidate types; it must never survive into an RType annotation
-- once inference has finished (task cleanup-rinfer).
containsGreaterType :: RType -> Bool
containsGreaterType (GreaterType _ _) = True
containsGreaterType (ListOf t)        = containsGreaterType t
containsGreaterType (Tuple t1 t2)     = containsGreaterType t1 || containsGreaterType t2
containsGreaterType (TEither t1 t2)   = containsGreaterType t1 || containsGreaterType t2
containsGreaterType (TArrow t1 t2)    = containsGreaterType t1 || containsGreaterType t2
containsGreaterType _                 = False

exprSubtree :: Expr -> [Expr]
exprSubtree e = e : concatMap exprSubtree (getSubExprs e)

-- Property: for any (untyped) generated program, if RType inference succeeds,
-- no GreaterType ever appears in any of the resulting RType annotations.
-- Ill-typed programs (Left) are out of scope for this invariant -- there is no
-- annotated tree to inspect.
prop_noGreaterTypeAfterRInfer :: Program -> Property
prop_noGreaterTypeAfterRInfer prog = case tryAddRTypeInfo prog of
  Left _ -> property True
  Right typed ->
    let allRTypes = [ rType (getTypeInfo e)
                     | (_, body) <- functions typed
                     , e <- exprSubtree body ]
    in property (not (any containsGreaterType allRTypes))

-- plus on two float constants should succeed
test_plusFloat :: TestTree
test_plusFloat = testCase "plusFloat" $
  assertBool "plus TFloat TFloat should typecheck" $
    typechecks (Program [("main", constF 1.0 #+# constF 2.0)] [] [] [])

-- plus on two int constants should succeed
test_plusInt :: TestTree
test_plusInt = testCase "plusInt" $
  assertBool "plusI TInt TInt should typecheck" $
    typechecks (Program [("main", constI 1 #<+># constI 2)] [] [] [])

-- Bool + Bool should be rejected with a ClassConstraintViolation
test_plusBoolReject :: TestTree
test_plusBoolReject = testCase "plusBoolReject" $ do
  let src = unlines
        [ "coin = if Uniform < 0.5 then True else False"
        , "main = coin + coin"
        ]
  case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err)
    Right prog -> case tryAddRTypeInfo prog of
      Left (ClassConstraintViolation _ _) -> return ()
      other -> assertFailure ("Expected ClassConstraintViolation, got: " ++ show other)

classConstraintTests :: TestTree
classConstraintTests = testGroup "classConstraints"
  [ test_plusFloat
  , test_plusInt
  , test_plusBoolReject
  ]

-- Specification test: a closed-form tuple-of-normals program with known, constant
-- parameters.  The writeLogits function is expected to recover those parameters directly
-- from the compiled SPLL distribution rather than reading the raw NN logit-vector slots.
--
-- Expected writeLogits output: [mu1, sigma1, mu2, sigma2] = [2.0, 1.5, -1.0, 0.5]
-- regardless of which sample is passed in.
--
-- makeWriteLogitsPlan handles TuplePlan by delegating each Continuous sub-plan to
-- the per-component normal function (main_normal_fst / main_normal_snd), which
-- returns (mu, sigma) derived from the compiled SPLL program rather than the raw
-- NN logit vector.
test_writeLogitsTupleGaussianParams :: TestTree
test_writeLogitsTupleGaussianParams = testCase "writeLogitsTupleGaussianParams" $ do
  let src = unlines
        [ "neural tupleNN :: (Symbol -> (Float, Float))"
        , "main = (1.5 * Normal + 2.0, 0.5 * Normal + (-1.0))"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  -- Closed-form program: no outer params, so runWriteLogits takes an empty arg list.
  -- The writeLogits function lives on main (the value producer), derived from its
  -- (Float, Float) output.
  case runWriteLogits defaultCompilerConfig prog "main" [] of
    Left err -> assertFailure ("runWriteLogits failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
      assertEqual "writeLogits length" 4 (length items)
      -- writeLogits must recover the actual distribution parameters,
      -- not the mock NN's random output.
      let checkSlot i expected = case items !! i of
            VFloat actual ->
              assertBool ("slot " ++ show i ++ ": expected " ++ show expected
                          ++ ", got " ++ show actual)
                         (abs (actual - expected) < 1.0e-6)
            other -> assertFailure ("slot " ++ show i ++ " is not VFloat: " ++ show other)
      checkSlot 0   2.0   -- mu1
      checkSlot 1   1.5   -- sigma1
      checkSlot 2 (-1.0)  -- mu2
      checkSlot 3   0.5   -- sigma2
    Right other -> assertFailure ("expected VList, got: " ++ show other)

-- Property: for a discrete-output program, the writeLogits output (probability vector) should
-- sum to approximately 1.0 for any mock NN sym input.
-- Tests with the discrete nonidentity program: main sym = if discreteNN sym == 0 then 2 else 0
-- Output type Int with values [0,1,2], so writeLogits returns [P(0), P(1), P(2)] which must
-- sum to 1.
test_writeLogitsDiscreteSumsToOne :: TestTree
test_writeLogitsDiscreteSumsToOne = testCase "writeLogitsDiscreteSumsToOne" $ do
  let src = unlines
        [ "neural discreteNN :: (Symbol -> Int) of [0, 1, 2]"
        , "main sym = if discreteNN sym == 0 then 2 else 0"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  -- Try several different mock syms; each should give a prob vector summing to 1.
  let mockSyms = [ VTuple (VInt 0) (VInt s) | s <- [0, 1, 42, 100, 999] ]
  mapM_ (\sym -> case runWriteLogits defaultCompilerConfig prog "main" [sym] of
    Left err -> assertFailure ("runWriteLogits failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
          total = sum [ x | VFloat x <- items ]
      assertBool ("writeLogits probs should sum to ~1.0, got " ++ show total)
                 (abs (total - 1.0) < 1.0e-4)
    Right other -> assertFailure ("expected VList, got: " ++ show other)
    ) mockSyms

-- Property: for the Gaussian identity program, writeLogits always returns exactly 2 elements
-- and sigma > 0, regardless of mock sym.
test_writeLogitsGaussianSigmaPositive :: TestTree
test_writeLogitsGaussianSigmaPositive = testCase "writeLogitsGaussianSigmaPositive" $ do
  let src = unlines
        [ "neural gaussNN :: (Symbol -> Float)"
        , "main sym = gaussNN sym"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let mockSyms = [ VTuple (VInt 0) (VInt s) | s <- [0, 1, 7, 42] ]
  mapM_ (\sym -> case runWriteLogits defaultCompilerConfig prog "main" [sym] of
    Left err -> assertFailure ("runWriteLogits failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
      assertEqual "writeLogits length for Gaussian" 2 (length items)
      case items of
        [_, VFloat sigma] ->
          assertBool ("sigma should be positive, got " ++ show sigma) (sigma > 0)
        _ -> assertFailure ("expected [mu, sigma], got: " ++ show items)
    Right other -> assertFailure ("expected VList, got: " ++ show other)
    ) mockSyms

-- A standalone "neural writeLogits :: Int of [...]" declaration registers a PartitionPlan
-- annotation for Int without declaring any callable network. main's Int output picks up
-- that registry entry, so main's own writeLogits group produces the registered number of
-- slots (3) even though Int is not auto-derivable on its own.
test_writeLogitsUsesStandaloneRegistration :: TestTree
test_writeLogitsUsesStandaloneRegistration = testCase "writeLogitsUsesStandaloneRegistration" $ do
  let src = unlines
        [ "neural writeLogits :: Int of [0, 1, 2]"
        , "neural decA :: (Symbol -> Int)"
        , "main sym = decA sym"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let sym = VTuple (VInt 0) (VInt 42)
  case runWriteLogits defaultCompilerConfig prog "main" [sym] of
    Left err          -> assertFailure ("runWriteLogits main failed: " ++ err)
    Right (VList lst) -> assertEqual "main writeLogits length" 3 (length (toList lst))
    Right other       -> assertFailure ("expected VList, got: " ++ show other)

-- A program with no neural declarations at all, whose main has an auto-derivable output
-- type (Bool), still gets an writeLogitsFun on its own "main" group (task
-- encode-main-auto-derived). The writeLogits output is a probability vector over
-- [True, False], queried from main_prob, so it must sum to ~1.0.
test_writeLogitsMainAutoDerivedBool :: TestTree
test_writeLogitsMainAutoDerivedBool = testCase "writeLogitsMainAutoDerivedBool" $ do
  let src = unlines
        [ "main = if Uniform < 0.3 then True else False"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  case runWriteLogits defaultCompilerConfig prog "main" [] of
    Left err -> assertFailure ("runWriteLogits main failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
          total = sum [ x | VFloat x <- items ]
      assertEqual "writeLogits length over [True, False]" 2 (length items)
      assertBool ("writeLogits probs should sum to ~1.0, got " ++ show total)
                 (abs (total - 1.0) < 1.0e-4)
    Right other -> assertFailure ("expected VList, got: " ++ show other)

-- Registry-first: main's Int output is not auto-derivable, but the read-logits network's
-- "of [0,1,2]" registers a PartitionPlan for Int into writeLogitsDecls (the of-clause
-- sugar). So main's own group gets an writeLogitsFun, sliced by that registry entry
-- (length 3) — the registry ∪ auto-derive rule from the parent design
-- (encode-partitionplan-decoupling). The read-logits group itself hosts no writeLogits
-- (it is an NN1 reader).
test_writeLogitsMainIntViaRegistry :: TestTree
test_writeLogitsMainIntViaRegistry = testCase "writeLogitsMainIntViaRegistry" $ do
  let src = unlines
        [ "neural decA :: (Symbol -> Int) of [0, 1, 2]"
        , "main sym = decA sym"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let sym = VTuple (VInt 0) (VInt 42)
      writeLogitsLen target = case runWriteLogits defaultCompilerConfig prog target [sym] of
        Left err          -> assertFailure ("runWriteLogits " ++ target ++ " failed: " ++ err) >> return (-1)
        Right (VList lst) -> return (length (toList lst))
        Right other       -> assertFailure ("expected VList, got: " ++ show other) >> return (-1)
  lenMain <- writeLogitsLen "main"
  assertEqual "main writeLogits length (registry Int)" 3 lenMain
  -- The read-logits group is an NN1 reader and hosts no writeLogits.
  case runWriteLogits defaultCompilerConfig prog "decA_auto" [sym] of
    Left _  -> return ()
    Right v -> assertFailure ("decA_auto should host no writeLogits, got: " ++ show v)

-- A program with no neural declarations whose main has a type that is neither
-- auto-derivable nor in the registry (a list) gets NO writeLogitsFun — the addition is purely
-- additive and degrades to a clean "no writeLogits function" error rather than crashing.
test_writeLogitsMainNotRepresentable :: TestTree
test_writeLogitsMainNotRepresentable = testCase "writeLogitsMainNotRepresentable" $ do
  let src = unlines
        [ "main = (Normal : (Normal : []))"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  case runWriteLogits defaultCompilerConfig prog "main" [] of
    Left err -> assertBool ("error should mention main has no writeLogits function, got: " ++ err)
                           ("main" `isInfixOf` err)
    Right v  -> assertFailure ("expected main to have no writeLogitsFun, got: " ++ show v)

-- main's output type is auto-derivable (Bool); main carries its own writeLogitsFun even when a
-- read-logits declaration shares that type. The read-logits group itself hosts no writeLogits
-- (it is an NN1 reader), so only "main" is addressable for writeLogits.
test_writeLogitsMainAndReadLogitsShareType :: TestTree
test_writeLogitsMainAndReadLogitsShareType = testCase "writeLogitsMainAndReadLogitsShareType" $ do
  let src = unlines
        [ "neural decB :: (Symbol -> Bool)"
        , "main sym = if decB sym then True else False"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let sym = VTuple (VInt 0) (VInt 42)
  case runWriteLogits defaultCompilerConfig prog "main" [sym] of
    Left err          -> assertFailure ("runWriteLogits main failed: " ++ err)
    Right (VList lst) -> assertEqual "main writeLogits length over [True, False]" 2 (length (toList lst))
    Right other       -> assertFailure ("expected VList, got: " ++ show other)
  -- The read-logits group is an NN1 reader and hosts no writeLogits.
  case runWriteLogits defaultCompilerConfig prog "decB_auto" [sym] of
    Left _  -> return ()
    Right v -> assertFailure ("decB_auto should host no writeLogits, got: " ++ show v)

-- An *auxiliary* (non-main) function with sum-type output gets a correct, non-stub Either
-- writeLogits via its OWN prob function (classify_prob) — proving the old null-probFnName stub
-- arms are gone (they emitted all-zero vectors). The flag slot is a real P(Left) = P(cond).
-- (task encode-per-function-endpoints, encode_aux_either)
test_writeLogitsAuxEither :: TestTree
test_writeLogitsAuxEither = testCase "writeLogitsAuxEither" $ do
  let src = unlines
        [ "neural writeLogits :: Either Int Bool of ([0] | _)"
        , "classify s = if Uniform < s then left 0 else right True"
        , "main s = classify s"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  case runWriteLogits defaultCompilerConfig prog "classify" [VFloat 0.4] of
    Left err -> assertFailure ("runWriteLogits classify failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
      assertEqual "Either writeLogits length (flag + Int[0] + Bool[True,False])" 4 (length items)
      case items of
        (VFloat flag : _) -> do
          assertBool ("flag should be a real P(Left) ~= 0.4, not a zero stub, got " ++ show flag)
                     (abs (flag - 0.4) < 1.0e-3)
        _ -> assertFailure ("expected a VFloat flag slot, got: " ++ show items)
    Right other -> assertFailure ("expected VList, got: " ++ show other)

-- writeLogits(readLogits(L)) ≈ normalise(L): for an identity `main sym = nnB sym` over a Bool
-- read-logits network, writeLogits reproduces the (normalised) read-logits distribution.
-- Spiking the mock NN toward a value shifts the written distribution toward that value, and
-- the slots always sum to 1 — i.e. reading then re-writing is a no-op on the normalised
-- logit vector. (encode_roundtrip_noop)
test_writeLogitsRoundtripNoop :: TestTree
test_writeLogitsRoundtripNoop = testCase "writeLogitsRoundtripNoop" $ do
  let src = unlines
        [ "neural nnB :: (Symbol -> Bool)"
        , "main sym = nnB sym"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let spike v = VTuple (VInt 1) (VTuple v (VInt 0))
      encSlots sym = case runWriteLogits defaultCompilerConfig prog "main" [sym] of
        Left err          -> assertFailure ("runWriteLogits main failed: " ++ err) >> return []
        Right (VList lst) -> return [ x | VFloat x <- toList lst ]
        Right other       -> assertFailure ("expected VList, got: " ++ show other) >> return []
  slotsTrue  <- encSlots (spike (VBool True))
  slotsFalse <- encSlots (spike (VBool False))
  assertEqual "Bool writeLogits length" 2 (length slotsTrue)
  assertBool ("True-spiked slots should sum to ~1, got " ++ show slotsTrue)
             (abs (sum slotsTrue - 1.0) < 1.0e-4)
  assertBool ("False-spiked slots should sum to ~1, got " ++ show slotsFalse)
             (abs (sum slotsFalse - 1.0) < 1.0e-4)
  assertBool ("readLogits->writeLogits should track the input: True-spiked P(True) > 0.5, got " ++ show (head slotsTrue))
             (head slotsTrue > 0.5)
  assertBool ("readLogits->writeLogits should track the input: False-spiked P(True) < 0.5, got " ++ show (head slotsFalse))
             (head slotsFalse < 0.5)

-- Sibling positive case to the reversed-shape rejection (TestRejection/reversedNeuralShapeDecl):
-- with the (Bool -> Symbol) reversed declaration gone, Bool auto-derives and main's own
-- writeLogits yields the exact [P(True), P(False)] vector — confirming the registration job
-- survives via honest syntax / auto-derivation.
test_writeLogitsBoolExactProbs :: TestTree
test_writeLogitsBoolExactProbs = testCase "writeLogitsBoolExactProbs" $ do
  let src = "main = if Uniform < 0.4 then True else False"
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  case runWriteLogits defaultCompilerConfig prog "main" [] of
    Left err -> assertFailure ("runWriteLogits main failed: " ++ err)
    Right (VList lst) -> case [ x | VFloat x <- toList lst ] of
      [pT, pF] -> do
        assertBool ("P(True) should be ~0.4, got " ++ show pT) (abs (pT - 0.4) < 1.0e-4)
        assertBool ("P(False) should be ~0.6, got " ++ show pF) (abs (pF - 0.6) < 1.0e-4)
      other -> assertFailure ("expected [P(True), P(False)], got: " ++ show other)
    Right other -> assertFailure ("expected VList, got: " ++ show other)

-- | True if `name` is directly applied (IRApply (IRVar name) _) anywhere inside
-- an enumeration loop body.  Used to check that NN forward calls are hoisted
-- out of loops.
--
-- The loop is a tensor map since the enum-sum lowering (design
-- ir-tensor-values): matching 'IREnumSum' here would make the assertion below
-- vacuously true, because no 'IREnumSum' survives that pass.
nnCallInsideEnumSum :: String -> IRExpr -> Bool
nnCallInsideEnumSum name (IREnumSum _ _ body) = containsDirectNNApply name body
nnCallInsideEnumSum name (IRBuiltin BMap [IRLambda _ body, _]) = containsDirectNNApply name body
nnCallInsideEnumSum name expr = any (nnCallInsideEnumSum name) (getIRSubExprs expr)

-- | Is there an enumeration loop anywhere in this expression, under either
-- spelling? Guards the hoisting assertion above against going vacuous.
irAnyLoop :: IRExpr -> Bool
irAnyLoop e = isLoop e || any irAnyLoop (getIRSubExprs e)
  where
    isLoop IREnumSum{} = True
    isLoop IRLogEnumSum{} = True
    isLoop IREnumSumPaired{} = True
    isLoop (IRBuiltin BMap _) = True
    isLoop _ = False

containsDirectNNApply :: String -> IRExpr -> Bool
containsDirectNNApply name (IRApply (IRVar v) _) = v == name
containsDirectNNApply name expr = any (containsDirectNNApply name) (getIRSubExprs expr)

-- | mNistAdd: readMNist(a) ++ readMNist(b) — the NN forward pass is loop-invariant
-- w.r.t. the IREnumSum over digit values, so it must be hoisted outside the loop.
test_nnHoistedOutOfEnumSum :: TestTree
test_nnHoistedOutOfEnumSum = testCase "nnHoistedOutOfEnumSum" $ do
  src <- readFile "testCases/mNistAdd.ppl"
  case tryParseProgram "mNistAdd.ppl" src of
    Left err -> assertFailure ("Parse error: " ++ show err)
    Right prog ->
      case compile defaultCompilerConfig prog of
        Left err -> assertFailure ("Compile error: " ++ show err)
        Right irEnv -> do
          (probExpr, _) <- case probFun (lookupIREnv "main" irEnv) of
            Just pf -> return pf
            Nothing -> assertFailure "compiled main has no probability variant"
          -- Assert the loop is there before asserting nothing is inside it:
          -- the property is "hoisted out of the loop", so a compile with no
          -- loop at all would satisfy the negative check vacuously. That is
          -- not hypothetical -- it is what happened when the enum-sum lowering
          -- (design ir-tensor-values) replaced IREnumSum with a tensor map.
          assertBool "mNistAdd's probability body should still contain an enumeration loop" $
            irAnyLoop probExpr
          assertBool "readMNist forward call should be hoisted outside the enumeration loop" $
            not (nnCallInsideEnumSum "readMNist" probExpr)

-- A program with no "main" function must be rejected with a descriptive
-- CompilerError early on, instead of crashing deep in the IR lookup
-- (lookupIREnv) or with a failed irrefutable pattern match in
-- runGen/runProb/runInteg.
test_missingMainFunction :: TestTree
test_missingMainFunction = testCase "missingMainFunction" $ do
  let prog = Program [("notMain", constF 1.0)] [] [] []
  let assertMissingMain label result = case result of
        Left err -> assertBool (label ++ ": error should mention 'main', got: " ++ err)
                                ("main" `isInfixOf` err)
        Right _ -> assertFailure (label ++ ": expected a CompilerError for a program without 'main'")
  assertMissingMain "compile" (compile defaultCompilerConfig prog)
  assertMissingMain "runGen" (runGen defaultCompilerConfig prog [] :: Either CompilerError (Rand StdGen IRValue))
  assertMissingMain "runProb" (runProb defaultCompilerConfig prog [] (VFloat 1.0))
  assertMissingMain "runInteg" (runInteg defaultCompilerConfig prog [] (VFloat 1.0))

-- Regression for observe-partials-umbrella N4: addP's mixture combinator used to
-- decide "which branch contributed zero" via an epsilon-approximate float compare
-- (floatApproxEqThresh = 1e-10). A far-tail continuous density is legitimately
-- smaller than that threshold without being the impossible-event zero the check
-- was meant to catch, so it got mistaken for the *other* (structurally zero, wrong
-- constructor arm) branch and silently discarded. The probTolerance-based End2End
-- harness can't see this: a tail density this small is already within tolerance of
-- 0, so a magnitude check would pass either way. What distinguishes fixed from
-- broken is that the broken path collapses to an *exact* 0.0/dim 0, so assert
-- non-zero-ness and dimensionality directly instead.
test_farTailEitherDensityNotZeroed :: TestTree
test_farTailEitherDensityNotZeroed = testCase "farTailEitherDensityNotZeroed" $ do
  let prog = Program [("main", ifThenElse (normal #>#  constF 0.0) (left normal) (right unit))] [] [] []
  case runProb defaultCompilerConfig prog [] (VEither (Left (VFloat 7.0))) of
    Right (VProbDim p d) -> do
      assertBool ("expected a nonzero far-tail density, got exactly " ++ show p) (p > 0)
      assertEqual "far-tail density must keep dim=1 (continuous)" 1.0 d
    other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- The same program past the float underflow floor -- the residual half of the
-- bug above (task addp-zero-check-non-total). At x=39 the true density is around
-- 1e-331, which is not representable: the density itself IS exactly 0.0, so no
-- amount of care with the zero test can tell it apart from an impossible branch
-- BY VALUE. What still distinguishes them is provenance, and that is what the
-- impossibility flag carries: the Left arm's density underflowed (possible,
-- dim 1), the Right arm's indicator did not match (impossible), so the mixture
-- must report the Left arm's dimension. Before the flag, this returned dim 0.
test_underflowedTailKeepsDimension :: TestTree
test_underflowedTailKeepsDimension = testCase "underflowedTailKeepsDimension" $ do
  let prog = Program [("main", ifThenElse (normal #>#  constF 0.0) (left normal) (right unit))] [] [] []
  case runProb defaultCompilerConfig prog [] (VEither (Left (VFloat 39.0))) of
    Right res@(VProbDim p d) -> do
      assertEqual "the density underflows to a true float zero at this depth" 0.0 p
      assertEqual "but the branch is possible, so the mixture keeps dim=1" 1.0 d
      assertEqual "and the result is not flagged impossible" (Just False) (resultImpossible res)
    other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- Design mar-sum-types-observe §3: renormalising an observation needs no
-- compiler feature of its own, because 'observe' keeps the result in Maybe --
-- the conditional distribution p(v | Just) is the ratio of two ordinary
-- probability queries, p(Just v) / p(Just ANY), and the denominator is what the
-- structural-ANY marginalisation over the sum type provides. Pinned as a
-- direct HUnit assertion rather than a .tst case because a ratio of two query
-- results is not expressible in the .tst expectation language.
test_observeRenormalizesViaJustAny :: TestTree
test_observeRenormalizesViaJustAny = testCase "observeRenormalizesViaJustAny" $ do
  -- Unconditionally: 1 with p=0.3, else 2 or 3 with p=0.35 each. Observing
  -- "v /= 1" rejects the 1, so the renormalised posterior is 2 and 3 at 1/2 each.
  let src = "main = observe (if Uniform < 0.3 then 1 else (if Uniform < 0.5 then 2 else 3)) (\\v -> not (v == 1))"
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let probOf v = case runProb defaultCompilerConfig prog [] v of
        Right (VProbDim p _) -> return p
        other -> assertFailure ("expected a probability tuple, got: " ++ show other) >> return 0
      approx name expected actual =
        assertBool (name ++ ": expected " ++ show expected ++ ", got " ++ show actual)
                   (abs (actual - expected) < 1.0e-9)
  pJust2   <- probOf (VEither (Right (VInt 2)))
  pJust3   <- probOf (VEither (Right (VInt 3)))
  pJustAny <- probOf (VEither (Right VAny))
  pNothing <- probOf (VEither (Left VUnit))
  approx "p(Just 2)" 0.35 pJust2
  approx "p(Just 3)" 0.35 pJust3
  -- The denominator is the marginal over the whole Just branch, i.e. exactly
  -- the mass the observation keeps.
  approx "p(Just ANY)" 0.7 pJustAny
  -- ... and the Maybe-valued result is a proper distribution to begin with:
  -- nothing is renormalised away by 'observe' itself (umbrella N2b).
  approx "p(Just ANY) + p(Nothing)" 1.0 (pJustAny + pNothing)
  approx "p(2 | Just)" 0.5 (pJust2 / pJustAny)
  approx "p(3 | Just)" 0.5 (pJust3 / pJustAny)

-- The flag's own meaning, in the case where value-based detection is right but
-- says nothing about why: a sample in the wrong Either arm is not a zero-valued
-- density, it is an event the program cannot produce.
test_structurallyImpossibleSampleIsFlagged :: TestTree
test_structurallyImpossibleSampleIsFlagged = testCase "structurallyImpossibleSampleIsFlagged" $ do
  let prog = Program [("main", left uniform)] [] [] []
  case runProb defaultCompilerConfig prog [] (VEither (Right (VFloat 0.5))) of
    Right res -> do
      assertEqual "wrong Either arm is impossible" (Just True) (resultImpossible res)
    other -> assertFailure ("expected a probability tuple, got: " ++ show other)
  -- ... whereas a sample the program CAN produce is never flagged, however
  -- little density it carries.
  case runProb defaultCompilerConfig prog [] (VEither (Left (VFloat 0.5))) of
    Right res -> assertEqual "a live arm is possible" (Just False) (resultImpossible res)
    other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- Uniform is the case where a *density* leaf really is a structural zero: off
-- its support the event cannot occur, and the mixture must be able to tell that
-- apart from the deep-tail case above (where the value is equally zero but the
-- event is possible).
test_uniformOffSupportIsImpossible :: TestTree
test_uniformOffSupportIsImpossible = testCase "uniformOffSupportIsImpossible" $ do
  let prog = Program [("main", uniform)] [] [] []
  case runProb defaultCompilerConfig prog [] (VFloat 2.0) of
    Right res -> assertEqual "2.0 is outside [0,1]" (Just True) (resultImpossible res)
    other -> assertFailure ("expected a probability tuple, got: " ++ show other)
  case runProb defaultCompilerConfig prog [] (VFloat 0.5) of
    Right res -> assertEqual "0.5 is in support" (Just False) (resultImpossible res)
    other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- An InjF whose image is smaller than its type is a second way a *density*
-- result can be a structural zero, alongside a leaf's own support: observing a
-- value the function cannot produce. Where the inverse declares an
-- applicability test (exp, sq: b > 0) the flag comes from that test for free,
-- and where the argument has bounded support the observation is often caught
-- transitively -- pushed back through the inverse, it lands off the leaf's
-- support. Neither covers `sqrt` and `recip` at an observation whose preimage
-- lands back INSIDE the argument's support, which is why their inverses now
-- carry image tests of their own. p(sqrt(X) = -0.5) used to report X's density
-- at 0.25 (squaring maps the negative observation right back into [0,1]), and
-- p(recip(X) = 0) used to report NaN.
test_injFImageIsImpossible :: TestTree
test_injFImageIsImpossible = testGroup "InjF image constraints"
  [ testCase "sqrt: a negative observation is impossible, not X's density at its square" $ do
      let prog = Program [("main", sqrtF uniform)] [] [] []
      assertImpossible prog (VFloat (-0.5))
      assertPossible   prog (VFloat 0.9) 1.8
  , testCase "recip: a zero observation is impossible, not NaN" $ do
      let prog = Program [("main", recipF uniform)] [] [] []
      assertImpossible prog (VFloat 0.0)
      assertPossible   prog (VFloat 2.0) 0.25
  , testCase "exp: an observation off (0, inf) is impossible (via the declared applicability test)" $ do
      let prog = Program [("main", expF normal)] [] [] []
      assertImpossible prog (VFloat (-1.0))
      assertPossible   prog (VFloat 2.0) 0.1568740192789811
  ]
  where
    assertImpossible prog x = case runProb defaultCompilerConfig prog [] x of
      Right res@(VProbDim p _) -> do
        assertEqual ("probability at " ++ show x) 0.0 p
        assertEqual ("impossibility flag at " ++ show x) (Just True) (resultImpossible res)
      other -> assertFailure ("expected a probability tuple, got: " ++ show other)
    assertPossible prog x expected = case runProb defaultCompilerConfig prog [] x of
      Right res@(VProbDim p _) -> do
        assertBool ("expected " ++ show expected ++ " at " ++ show x ++ ", got " ++ show p)
                   (abs (p - expected) < 1e-9)
        assertEqual ("impossibility flag at " ++ show x) (Just False) (resultImpossible res)
      other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- Regression for observe-partials-umbrella: 'intersectSet's WPoint/WPoint case
-- (IRCompiler.hs) used to unconditionally keep the first witness and silently
-- discard the second whenever a let-bound stochastic Either is destructured
-- via the named-binding idiom `let e = ... in if isLeft e then fromLeft e
-- else fromRight e` -- three occurrences of `e` force the set-witness
-- fallback, which case-splits on `isLeft e` and then intersects that
-- condition's own witness (isLeft's inverse: tag-only, `Left VAny`) with the
-- branch's sample-derived witness (fromLeft's inverse, the actual value). The
-- condition's placeholder witness always won, so the compiled program ignored
-- the query sample entirely and returned the constant marginal
-- P(isLeft)+P(isRight)=1 for every query -- and, separately, a structurally
-- impossible sample (`Left ()`/Nothing, which fromLeft/fromRight's own guard
-- makes unreachable here) also wrongly returned 1 instead of 0, since neither
-- placeholder witness carries enough information to detect the Left-vs-Right
-- tag conflict on its own. Fixed by tracking, per witness, a runtime
-- "informative" guard (mirrors the witness expression's own branching -- a
-- single static flag can't work, since e.g. fromLeft/fromRight's *total*
-- inverse is only ANY-tainted on the arm that reconstructs a Nothing) and
-- using 'OpEq' -- already deep VAny-wildcard-aware in the interpreter -- as
-- the cross-check guard.
test_letBoundEitherDestructureUsesSample :: TestTree
test_letBoundEitherDestructureUsesSample = testCase "letBoundEitherDestructureUsesSample" $ do
  let boundE = ifThenElse (uniform #<# constF 0.5) (left normal) (right (constF 0.0))
  let body = ifThenElse (sisLeft (var "e")) (sfromLeft (var "e")) (sfromRight (var "e"))
  let prog = Program [("main", letIn "e" boundE body)] [] [] []
  let phi x = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)
  case runProb defaultCompilerConfig prog [] (VEither (Right (VFloat 0.3))) of
    Right (VProbDim p d) -> do
      assertBool ("expected 0.5*phi(0.3) =~ 0.1907, got " ++ show p) (abs (p - 0.5 * phi 0.3) < 0.0001)
      assertEqual "continuous arm keeps dim=1" 1.0 d
    other -> assertFailure ("expected a probability tuple, got: " ++ show other)
  case runProb defaultCompilerConfig prog [] (VEither (Left VUnit)) of
    Right (VProbDim p _) ->
      assertEqual "Nothing is structurally impossible here (fromLeft/fromRight always succeed under their own isLeft/isRight guard)" 0.0 p
    other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- Regression for observe-partials-umbrella N6, second half: 'intersectSet's
-- WPoint/WPoint case, once fixed to prefer whichever witness is informative
-- (above), still silently dropped information when TWO witnesses each hold
-- *complementary* partial knowledge of a composite (tuple) variable -- e.g.
-- one occurrence recovered only the first field via fst's inverse
-- (`TCons(b, VAny)`), another only the second via snd's (`TCons(VAny, b)`).
-- Neither side is "the informative one"; both need to be merged field-by-field.
-- The set-witness fallback's TCons-body case (`let e = (Normal, Uniform) in
-- (fst e, snd e)`, wrapped in a deterministic if to force the fallback instead
-- of the ordinary point-inversion path, which already merges this correctly
-- via ForwardChaining.hs's mergeExpr2) intersects exactly such a pair. Before
-- the fix, the second field silently fell back to a *marginal* (P(ANY)=1)
-- instead of the concrete point density -- invisible in the probability
-- magnitude (a marginal always integrates to exactly 1, masking the loss) but
-- visible in the dimensionality (1.0 instead of the correct 2.0, one
-- continuous dimension short). Fixed by 'mergeWitnessValue' recursing through
-- IRTCons to pick whichever side of each field is not ANY-tainted, checked
-- fresh per field via 'irRuntimeContainsAny' (a first attempt that checked
-- with 'OpEq' per decomposed field, mirroring the sibling Either fix, broke
-- this: OpEq's VAny-wildcard tolerance only applies to a VAny *nested inside*
-- a container comparison -- IRInterpreter.hs's cmp -- not a bare top-level
-- VAny, which a field-level comparison always is after decomposition; the
-- compatibility guard has to stay a single 'OpEq' on the whole undecomposed
-- value, where OpEq's own recursion already handles nested VAny correctly).
test_setWitnessMergesComplementaryTupleFields :: TestTree
test_setWitnessMergesComplementaryTupleFields = testCase "setWitnessMergesComplementaryTupleFields" $ do
  let boundE = tuple normal uniform
  let body = ifThenElse (constF 1.0 #># constF 0.0)
               (tuple (tfst (var "e")) (tsnd (var "e")))
               (tuple (constF 0.0) (constF 0.0))
  let prog = Program [("main", letIn "e" boundE body)] [] [] []
  let phi x = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)
  case runProb defaultCompilerConfig prog [] (VTuple (VFloat 0.3) (VFloat 0.7)) of
    Right (VProbDim p d) -> do
      assertBool ("expected phi(0.3)*1 =~ 0.3814, got " ++ show p) (abs (p - phi 0.3) < 0.0001)
      assertEqual "both fields recovered => dim=2 (two independent continuous slots)" 2.0 d
    other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- AutoNeural: auto-derivation of MultiValue annotations for the "Nothing" (no "of ...")
-- and "_" (MultiAuto) cases. Float, Bool, Tuple/Either/non-recursive ADTs of these can be
-- fully derived from the RType alone; Int and recursive ADTs cannot (unbounded/non-terminating).
test_autoDeriveFloat :: TestTree
test_autoDeriveFloat = testCase "autoDeriveFloat" $
  assertEqual "Float auto-derives to MultiContinuous"
    (Right MultiContinuous) (autoDeriveMultiValue [] TFloat)

test_autoDeriveBool :: TestTree
test_autoDeriveBool = testCase "autoDeriveBool" $
  assertEqual "Bool auto-derives to [True, False]"
    (Right (MultiDiscretes [VBool True, VBool False])) (autoDeriveMultiValue [] TBool)

test_autoDeriveIntFails :: TestTree
test_autoDeriveIntFails = testCase "autoDeriveIntFails" $ case autoDeriveMultiValue [] TInt of
  Left err -> assertBool ("error should mention Int: " ++ err) ("Int" `isInfixOf` err)
  Right mv -> assertFailure ("expected auto-derive of Int to fail, got: " ++ show mv)

test_autoDeriveTuple :: TestTree
test_autoDeriveTuple = testCase "autoDeriveTuple" $
  assertEqual "Tuple of (Bool, Float) auto-derives componentwise"
    (Right (MultiTuple (MultiDiscretes [VBool True, VBool False]) MultiContinuous))
    (autoDeriveMultiValue [] (Tuple TBool TFloat))

colorADT :: ADTDecl
colorADT = ADTDecl "Color" [("Red", []), ("Green", []), ("Blue", [])] Nothing

test_autoDeriveNonRecursiveADT :: TestTree
test_autoDeriveNonRecursiveADT = testCase "autoDeriveNonRecursiveADT" $
  assertEqual "non-recursive enum ADT auto-derives all constructors"
    (Right (MultiADT [("Red", []), ("Green", []), ("Blue", [])]))
    (autoDeriveMultiValue [colorADT] (TADT "Color"))

-- Recursive, no `depth`: auto-derivation has no finite enumeration to produce.
treeADT :: ADTDecl
treeADT = ADTDecl "Tree"
  [ ("Leaf", [("val", TInt)])
  , ("Node", [("l", TADT "Tree"), ("r", TADT "Tree")])
  ] Nothing

test_autoDeriveRecursiveADTFails :: TestTree
test_autoDeriveRecursiveADTFails = testCase "autoDeriveRecursiveADTFails" $ case autoDeriveMultiValue [treeADT] (TADT "Tree") of
  Left err -> assertBool ("error should mention recursion: " ++ err) ("recursive" `isInfixOf` err)
  Right mv -> assertFailure ("expected auto-derive of recursive ADT to fail, got: " ++ show mv)

-- Recursive WITH a declared depth: auto-derivation unrolls to that depth. At
-- depth 1 the self-referential FCons tail may only be FNil (the recursive
-- constructor is dropped at the leaf).
flistADT :: ADTDecl
flistADT = ADTDecl
  { dataName = "FList"
  , constructors = [ ("FCons", [("hd", TFloat), ("tl", TADT "FList")]), ("FNil", []) ]
  , adtDepth = Just 1 }

test_autoDeriveRecursiveADTWithDepth :: TestTree
test_autoDeriveRecursiveADTWithDepth = testCase "autoDeriveRecursiveADTWithDepth" $
  assertEqual "recursive ADT with `depth 1` unrolls one level (tail must be FNil)"
    (Right (MultiADT
      [ ("FCons", [MultiContinuous, MultiADT [("FNil", [])]])
      , ("FNil", []) ]))
    (autoDeriveMultiValue [flistADT] (TADT "FList"))

-- AutoNeural: makePartitionPlan resolves "Nothing" and "_" (MultiAuto) via auto-derivation,
-- and "Real" (MultiContinuous) directly to a Continuous plan.
test_makePartitionPlanNothingFloat :: TestTree
test_makePartitionPlanNothingFloat = testCase "makePartitionPlanNothingFloat" $
  assertEqual "Nothing for Float resolves to Continuous"
    Continuous (makePartitionPlan [] TFloat Nothing)

test_makePartitionPlanNothingTuple :: TestTree
test_makePartitionPlanNothingTuple = testCase "makePartitionPlanNothingTuple" $
  assertEqual "Nothing for (Bool, Float) resolves componentwise"
    (TuplePlan (Discretes TBool (MultiDiscretes [VBool True, VBool False])) Continuous)
    (makePartitionPlan [] (Tuple TBool TFloat) Nothing)

test_makePartitionPlanWildcardMatchesNothing :: TestTree
test_makePartitionPlanWildcardMatchesNothing = testCase "makePartitionPlanWildcardMatchesNothing" $
  assertEqual "explicit '_' placeholders resolve the same as Nothing"
    (makePartitionPlan [] (Tuple TBool TFloat) Nothing)
    (makePartitionPlan [] (Tuple TBool TFloat) (Just (MultiTuple MultiAuto MultiContinuous)))

test_makePartitionPlanMixedExplicitAuto :: TestTree
test_makePartitionPlanMixedExplicitAuto = testCase "makePartitionPlanMixedExplicitAuto" $
  assertEqual "an explicit Int enumeration alongside an auto-derived ('_') Float"
    (TuplePlan (Discretes TInt (MultiDiscretes [VInt 0, VInt 1, VInt 2])) Continuous)
    (makePartitionPlan [] (Tuple TInt TFloat) (Just (MultiTuple (MultiDiscretes [VInt 0, VInt 1, VInt 2]) MultiAuto)))

autoNeuralDerivationTests :: TestTree
autoNeuralDerivationTests = testGroup "autoNeuralDerivation"
  [ test_autoDeriveFloat
  , test_autoDeriveBool
  , test_autoDeriveIntFails
  , test_autoDeriveTuple
  , test_autoDeriveNonRecursiveADT
  , test_autoDeriveRecursiveADTFails
  , test_autoDeriveRecursiveADTWithDepth
  , test_makePartitionPlanNothingFloat
  , test_makePartitionPlanNothingTuple
  , test_makePartitionPlanWildcardMatchesNothing
  , test_makePartitionPlanMixedExplicitAuto
  ]

-- .tst files may carry an optional `backends:` header that routes the file's
-- cases to a subset of the End2End backends; no header means the three scalar
-- backends (`defaultBackends`) -- notably NOT the opt-in `batched` token.
-- They may also carry an optional `slow` header (in either order relative to
-- `backends:`) that moves the file into the opt-in Slow test group.
test_tstBackendsHeader :: TestTree
test_tstBackendsHeader = testCase "tstBackendsHeader" $ do
  let parse = parseTestCasesFromString "header.tst"
  case parse "p(0.5)=(1.0, 1.0)\n" of
    Left err -> assertFailure err
    Right (bs, slow, tcs) -> do
      assertEqual "no header defaults to the scalar backends" defaultBackends bs
      assertEqual "no header defaults to not slow" False slow
      assertEqual "test case count without header" 1 (length tcs)
  case parse "backends: interpreter\np(0.5)=(1.0, 1.0)\n" of
    Left err -> assertFailure err
    Right (bs, _, tcs) -> do
      assertEqual "interpreter-only routing" [Interpreter] bs
      assertEqual "test case count with header" 1 (length tcs)
  case parse "backends: julia, python\ncdf(0.5)=(0.5, 0.0)\n" of
    Left err -> assertFailure err
    Right (bs, _, _) -> assertEqual "two-backend routing" [Julia, Python] bs
  case parse "slow\np(0.5)=(1.0, 1.0)\n" of
    Left err -> assertFailure err
    Right (bs, slow, _) -> do
      assertEqual "slow header alone still defaults to the scalar backends" defaultBackends bs
      assertEqual "slow header is recognized" True slow
  case parse "backends: python, batched\np(0.5)=(1.0, 1.0)\n" of
    Left err -> assertFailure err
    Right (bs, _, _) -> assertEqual "batched is an explicit opt-in token" [Python, Batched] bs
  case parse "backends: interpreter\nslow\np(0.5)=(1.0, 1.0)\n" of
    Left err -> assertFailure err
    Right (bs, slow, _) -> do
      assertEqual "backends-then-slow routing" [Interpreter] bs
      assertEqual "backends-then-slow is recognized" True slow
  case parse "slow\nbackends: interpreter\np(0.5)=(1.0, 1.0)\n" of
    Left err -> assertFailure err
    Right (bs, slow, _) -> do
      assertEqual "slow-then-backends routing" [Interpreter] bs
      assertEqual "slow-then-backends is recognized" True slow

return []

-- ---------------------------------------------------------------------------
-- ForwardChaining invertibility certificate (modality-split-forwardchaining)
-- ---------------------------------------------------------------------------

-- | Parse + the pre-inference annotation stages + type inference that the FC
-- certificate depends on (progToFCData reads rType, so types must be present).
prepTypedFC :: String -> (Program, FCData)
prepTypedFC src =
  let p0    = annotateProg (annotateEnumsProg (parse src))
      -- addTypeInfo returns its own (knownAnchors-seeded) certificate since
      -- witnessed-inference milestone 2; these tests keep building the
      -- anchor-free one so the certificate queries are pinned in isolation.
      typed = either (\e -> error ("type inference failed: " ++ show e)) fst (addTypeInfo p0)
  in (typed, progToFCData Set.empty typed)
  where
    parse s = either (\e -> error ("parse failed: " ++ show e)) id (tryParseProgram "test" s)

universeE :: Expr -> [Expr]
universeE e = e : concatMap universeE (getSubExprs e)

allNodes :: Program -> [Expr]
allNodes prog = concatMap (universeE . snd) (functions prog)

-- The chain name of the function on the left of the first Apply — exactly the
-- handle 'IRCompiler' passes to the certificate / 'toInvExpr'.
applyLeftCN :: Program -> ChainName
applyLeftCN prog = head [ chainName (getTypeInfo l) | Expr _ (Apply l _) <- allNodes prog ]

constNodeCN :: Program -> ChainName
constNodeCN prog = head [ chainName (getTypeInfo c) | c@(Expr _ (Constant _)) <- allNodes prog ]

forwardChainingCertTests :: TestTree
forwardChainingCertTests = testGroup "ForwardChaining certificate"
  [ testCase "invertible probabilistic-bound lambda is witnessed" $
      let (prog, fc) = prepTypedFC "main=(\\x -> x + 5.0)(Uniform)"
      in assertBool "\\x -> x + 5.0 should invert in x"
           (isInvertibleLambda fc (adts prog) (applyLeftCN prog))
  , testCase "many-to-one comparison body is not witnessed" $
      -- `x > 0.5` is many-to-one onto {T,F}; no inversion path exists, so the
      -- certificate must report False (this is the program that otherwise
      -- crashes codegen in toInvExpr's mergeExpr).
      let (prog, fc) = prepTypedFC "main=(\\x -> x > 0.5)(Uniform)"
      in assertBool "\\x -> x > 0.5 must not invert in x"
           (not (isInvertibleLambda fc (adts prog) (applyLeftCN prog)))
  , testCase "a non-lambda chain name is not invertible" $
      let (prog, fc) = prepTypedFC "main=(\\x -> x + 5.0)(Uniform)"
      in assertBool "a Constant node is not an invertible lambda"
           (not (isInvertibleLambda fc (adts prog) (constNodeCN prog)))
  ]

-- The lambda that binds @v@ — a let binding's handle (the parser rewrites
-- @let v = e in b@ to @Apply (Lambda v b) e@).
letLambdaCN :: String -> Program -> ChainName
letLambdaCN v prog =
  head [ chainName (getTypeInfo l) | l@(Expr _ (Lambda n _)) <- allNodes prog, n == v ]

declRootCN :: String -> Program -> ChainName
declRootCN fname prog = case lookup fname (functions prog) of
  Just e  -> chainName (getTypeInfo e)
  Nothing -> error ("no function " ++ fname)

-- | Witnessed-binding query (design modality-witnessed-inference, milestone 1).
-- Same FC machinery as the certificate above, but the chaining is seeded at the
-- DECLARATION'S observed result rather than the binding's own body. Pins the
-- design's discriminating programs; the modality engine consumes this verdict in
-- milestone 2. The residual-latent boundary (two fresh draws in one observed
-- slot) is deliberately NOT this query's concern — the marginalize floor
-- self-enforces it, so those cases assert only on the bound variable itself.
witnessedBindingTests :: TestTree
witnessedBindingTests = testGroup "ForwardChaining witnessed-binding query"
  [ testCase "additive witness: x is recovered from the observed tuple" $
      let (prog, fc) = prepTypedFC
            "main = let x = Uniform in let y = x + Uniform in (x, y)"
      in assertBool "x should be witnessed via fst"
           (isWitnessedLambda fc (adts prog) (declRootCN "main" prog) (letLambdaCN "x" prog))
  , testCase "multiplicative witness: x is recovered from the observed tuple" $
      let (prog, fc) = prepTypedFC
            "main = let x = Uniform in let y = x * Uniform in (x, y)"
      in assertBool "x should be witnessed via fst"
           (isWitnessedLambda fc (adts prog) (declRootCN "main" prog) (letLambdaCN "x" prog))
  , testCase "y-only: x is NOT witnessed (genuine convolution)" $
      -- The load-bearing discriminator (investigation
      -- fc-recovers-capability-marginalize-floors): observing only y = x + u2
      -- gives one equation for two fresh draws, so x must not be witnessed.
      let (prog, fc) = prepTypedFC
            "main = let x = Uniform in let y = x + Uniform in y"
      in assertBool "x must not be witnessed from y alone"
           (not (isWitnessedLambda fc (adts prog) (declRootCN "main" prog) (letLambdaCN "x" prog)))
  , testCase "y-only: the y-binding itself IS witnessed (why x is the discriminator)" $
      -- y equals the observation, so the y-binding is trivially recoverable in
      -- both programs — consulting it cannot separate the witness from the
      -- convolution. Pins why milestone 2 must key on the x-binding's verdict.
      let (prog, fc) = prepTypedFC
            "main = let x = Uniform in let y = x + Uniform in y"
      in assertBool "y is the observed value itself"
           (isWitnessedLambda fc (adts prog) (declRootCN "main" prog) (letLambdaCN "y" prog))
  , testCase "two residual latents: x itself is still witnessed (floor guards the rest)" $
      -- x is observed directly via fst, so THIS query answers True; keeping the
      -- program at Bottom is the marginalize floor's job (u2 + u3 in one slot),
      -- pinned in TestModalityInfer's permanent guards.
      let (prog, fc) = prepTypedFC
            "main = let x = Uniform in (x, x + Uniform + Uniform)"
      in assertBool "x is observed directly"
           (isWitnessedLambda fc (adts prog) (declRootCN "main" prog) (letLambdaCN "x" prog))
  , testCase "let-chain: the observation reaches x through chained equivalences" $
      -- Confirms the per-let verdict suffices for the let-chains-feeding-output
      -- shape (milestone 1's open question): the observed tuple chains through
      -- z and y back to x.
      let (prog, fc) = prepTypedFC
            "main = let x = Uniform in let y = x + Uniform in let z = 2.0 * y in (x, z)"
      in assertBool "x should be witnessed through the chain"
           (isWitnessedLambda fc (adts prog) (declRootCN "main" prog) (letLambdaCN "x" prog))
  , testCase "let under a many-to-one context: witnessed says False where the certificate says True" $
      -- The seeding difference that makes this query honest: the let's body
      -- (x + 1.0) would recover x if it were observed, but the enclosing (> 0.5)
      -- is many-to-one, so the declaration's observation witnesses nothing.
      let (prog, fc) = prepTypedFC
            "main = (let x = Uniform in x + 1.0) > 0.5"
          lamCN = letLambdaCN "x" prog
      in do assertBool "own-body certificate claims invertibility"
              (isInvertibleLambda fc (adts prog) lamCN)
            assertBool "observation-seeded query must not"
              (not (isWitnessedLambda fc (adts prog) (declRootCN "main" prog) lamCN))
  ]

-- | Runtime ANY-refusal guard (design modality-witnessed-inference, §ANY —
-- the milestone-3 remainder). ANY in the slot that witnesses a let binding
-- means the binding is unobserved. When it is a sink (single occurrence, no
-- downstream randomness) the marginal is free — pinned in the letWitnessed*
-- .tst cases. Otherwise the marginal is a convolution the engine cannot
-- compute, and the compiled probability code must refuse with a diagnostic —
-- never crash on VAny arithmetic, never return a silent 1.0.
anyRefusalTests :: TestTree
anyRefusalTests = testGroup "witnessed-inference ANY refusal"
  [ testCase "ANY in the witnessing slot of the additive witness refuses, naming x" $
      expectMarginalRefusal
        "main = let x = Uniform in let y = x + Uniform in (x, y)"
        (VTuple VAny (VFloat 1.0)) "x"
  , testCase "ANY in the witnessing slot of the multiplicative witness refuses, naming x" $
      expectMarginalRefusal
        "main = let x = Uniform in let y = x * Uniform in (x, y)"
        (VTuple VAny (VFloat 0.25)) "x"
  , testCase "mid-chain ANY with an observed dependent slot refuses, naming y" $
      -- z = y + u3 is observed, so recovering u3 needs y's value: a genuine
      -- convolution. The guard must fire at the y-binding, not crash at the
      -- z-binding's inverse arithmetic.
      expectMarginalRefusal
        "main = let x = Uniform in let y = x + Uniform in let z = y + Uniform in (x, (y, z))"
        (VTuple (VFloat 0.5) (VTuple VAny (VFloat 1.5))) "y"
  ]

expectMarginalRefusal :: String -> IRValue -> String -> IO ()
expectMarginalRefusal src sample varName = do
  let prog = either (\e -> error ("parse failed: " ++ show e)) id (tryParseProgram "test" src)
  r <- try (case runProb defaultCompilerConfig prog [] sample of
              Left cerr -> return (Left cerr)
              Right v   -> evaluate (length (show v)) >> return (Right v))
  case r of
    Left (ErrorCall msg) -> do
      assertBool ("expected the marginal-refusal diagnostic, got: " ++ msg)
        ("cannot compute marginal" `isInfixOf` msg)
      assertBool ("diagnostic should name the binding '" ++ varName ++ "', got: " ++ msg)
        (("'" ++ varName ++ "'") `isInfixOf` msg)
    Right (Left cerr) -> assertFailure ("expected runtime refusal, got compile error: " ++ show cerr)
    Right (Right v) -> assertFailure ("expected runtime refusal, got value: " ++ show v)

-- | Enum annotation must not offer enumeration for a MultiValue containing a
-- continuous (Real) leaf: enumerating it would walk only the discrete residue
-- (e.g. just the Left values of ([0,1] | Real)) and silently drop the
-- continuous probability mass. annotateEnumsProg declines to tag such neurals,
-- the same treatment as a neural with no `of` annotation at all.
enumTagsOf :: String -> [MultiValue]
enumTagsOf src =
  let prog = either (\e -> error ("parse failed: " ++ show e)) id (tryParseProgram "test" src)
  in [mv | e <- allNodes (annotateEnumsProg prog), DiscreteValues mv <- tags (getTypeInfo e)]

enumContinuousRefusalTests :: TestTree
enumContinuousRefusalTests = testGroup "enum annotation refuses continuous leaves"
  [ testCase "mixed Either ([0,1] | Real) gets no DiscreteValues tag" $
      assertEqual "expected no tags" []
        (enumTagsOf "neural f :: (Symbol -> Either Int Float) of ([0, 1] | Real)\nmain sym = f sym\n")
  , testCase "pure Real gets no DiscreteValues tag" $
      assertEqual "expected no tags" []
        (enumTagsOf "neural f :: (Symbol -> Float) of Real\nmain sym = f sym\n")
  , testCase "tuple with an auto-derived Float slot gets no DiscreteValues tag" $
      -- '_' resolves to MultiContinuous for a Float slot, so the whole tuple
      -- annotation must be declined, not enumerated as a residue.
      assertEqual "expected no tags" []
        (enumTagsOf "neural f :: (Symbol -> (Int, Float)) of ([0, 1], _)\nmain sym = f sym\n")
  , testCase "pure discrete enumeration is still tagged" $
      assertBool "expected DiscreteValues tags" (not (null
        (enumTagsOf "neural f :: (Symbol -> Int) of [0, 1, 2]\nmain sym = f sym\n")))
  , testCase "multiValueContainsContinuous finds nested leaves" $ do
      assertBool "tuple/Either nesting" (multiValueContainsContinuous
        (MultiTuple (MultiDiscretes [VInt 0]) (MultiEither (MultiDiscretes [VBool True]) MultiContinuous)))
      assertBool "ADT field" (multiValueContainsContinuous
        (MultiADT [("A", [MultiDiscretes [VInt 0]]), ("B", [MultiContinuous])]))
      assertBool "pure discrete composite is clean" (not (multiValueContainsContinuous
        (MultiTuple (MultiDiscretes [VInt 0]) (MultiADT [("A", [])]))))
  -- 'multiValueIsFinite' backs the dense-enumeration domain (design
  -- heterogeneous-batch-inference M3). It is deliberately *stricter* than
  -- @not . multiValueContainsContinuous@, and each row below is a case where
  -- the two answers differ -- which is the whole reason it exists rather than
  -- reusing the older predicate.
  , testCase "multiValueIsFinite is stricter than the continuity check" $ do
      assertBool "wholly discrete composite is finite" (multiValueIsFinite
        (MultiTuple (MultiDiscretes [VInt 0, VInt 1]) (MultiDiscretes [VBool True])))
      assertBool "nullary ADT constructor contributes one value" (multiValueIsFinite
        (MultiADT [("A", []), ("B", [MultiDiscretes [VInt 0]])]))
      -- An Either with one continuous arm: enumerating only the discrete arm
      -- would be a strict subset of the domain, so it is not a domain at all.
      assertBool "Either with a continuous arm is not finite" (not (multiValueIsFinite
        (MultiEither (MultiDiscretes [VInt 0]) MultiContinuous)))
      -- These two are *not* continuous, yet still have no usable enumeration:
      -- multiValueToValueList would error on the first and has no case for the
      -- second, so a caller wanting the values must be told no.
      assertBool "unresolved auto placeholder is not finite"
        (not (multiValueContainsContinuous MultiAuto) && not (multiValueIsFinite MultiAuto))
      assertBool "unresolved type reference is not finite"
        (not (multiValueContainsContinuous (MultiTypeRef "T"))
         && not (multiValueIsFinite (MultiTypeRef "T")))
      assertBool "empty enumeration is not finite" (not (multiValueIsFinite (MultiDiscretes [])))
  ]

-- | Plan-guided lazy enumeration milestone 2 (design
-- plan-guided-lazy-enumeration): a recursive-specialization corpus program
-- under the topK and branch-counting compiler variants, checked against the
-- values pinned in its .tst. TopK wraps Expr-level IfThenElse inference arms,
-- which the plan engine bypasses (worlds carry their own guards and are
-- exact), so probabilities must be unchanged; branch counting counts one
-- branch per live world, so the count must be strictly positive and the
-- shifted result triple must still carry the same probability. Parametrized
-- over the program so the cheap depth-3 shape can be pinned in the fast
-- Internals group (planEnumThreadedTopKAndBC) while the pricier
-- multi-predicate differential twin (planEnumRecChain, 4 extra full
-- compiles) stays in slowInternalsTests.
planEnumTopKAndBCTest :: String -> String -> TestTree
planEnumTopKAndBCTest testName baseName = testCase testName $ do
  let pplPath = "testCases/" ++ baseName ++ ".ppl"
      tstPath = "testCases/" ++ baseName ++ ".tst"
  src <- readFile pplPath
  prog <- case tryParseProgram pplPath src of
    Left err -> assertFailure ("Parse error: " ++ show err)
    Right p  -> return p
  tstSrc <- readFile tstPath
  (_, _, tcs) <- case parseTestCasesFromString tstPath tstSrc of
    Left err -> assertFailure ("tst parse error: " ++ err)
    Right r  -> return r
  let probCases = [ (s, ps, expectationProb expct) | ProbTestCase _ s ps expct <- tcs ]
  assertBool (baseName ++ ".tst should contain prob cases") (not (null probCases))
  -- compile once per config, evaluate every pinned case against each
  let compiledWith conf = either (error . show) id (compile conf prog)
  let cDef  = compiledWith defaultCompilerConfig
  let cTopK = compiledWith defaultCompilerConfig{topKThreshold = Just 0.05}
  let cBC   = compiledWith defaultCompilerConfig{countBranches = True}
  let cBoth = compiledWith defaultCompilerConfig{topKThreshold = Just 0.05, countBranches = True}
  let evalWith c ps s = either (error . show) id (runProbC prog c ps s)
  mapM_ (\(s, ps, expected) -> do
          let (pDef, dimDef)      = probDimOf   (evalWith cDef ps s)
          let (pTopK, _)          = probDimOf   (evalWith cTopK ps s)
          let (pBC, dimBC, bc)    = probDimBCOf (evalWith cBC ps s)
          let (pBoth, _, bcBoth)  = probDimBCOf (evalWith cBoth ps s)
          assertBool ("default prob " ++ show pDef ++ " differs from .tst " ++ show expected)
            (abs (pDef - expected) < 1e-4)
          assertEqual "all-discrete plan worlds have dim 0" 0 dimDef
          assertEqual "topK must not change plan-world probabilities" pDef pTopK
          assertEqual "branch counting must not change the probability" pDef pBC
          assertEqual "bc variant dim" 0 dimBC
          assertBool ("branch count should be strictly positive, got " ++ show bc) (bc >= 1)
          assertEqual "topK+bc must not change the probability" pDef pBoth
          assertBool "topK+bc branch count should be strictly positive" (bcBoth >= 1))
        probCases

-- | Structural inversion of a *constructed* ADT observation (a body that builds
-- a value rather than choosing among a few), pinned against the materializing
-- enumeration path on the same program -- the `*Materialized` differential twin
-- idiom, written here rather than as a corpus pair because the query values are
-- ADT values, which `.tst` (via `pValue`) cannot spell.
--
-- `filterGreen` is the shape that motivated this: it returns a Scene it builds
-- from the observed one, so value enumeration declines it (its result set is the
-- whole depth-unrolled support) and the observation has to be pushed onto the
-- constructor's fields instead.
planEnumStructuralADTTests :: TestTree
planEnumStructuralADTTests = testGroup "planEnumStructuralADT"
  [ testCase "lazy structural inversion matches materialized enumeration" $ do
      lazyProg <- parseOrFailSrc (progSrc "")
      matProg  <- parseOrFailSrc (progSrc " of _")
      let cfg = defaultCompilerConfig
      let cLazy = either (error . show) id (compile cfg lazyProg)
      let cMat  = either (error . show) id (compile cfg matProg)
      forM_ queries $ \(label, q) -> do
        let (pLazy, dLazy) = probDimOf (either (error . show) id (runProbC lazyProg cLazy [sym] q))
        let (pMat,  dMat)  = probDimOf (either (error . show) id (runProbC matProg  cMat  [sym] q))
        assertBool (label ++ ": lazy " ++ show pLazy ++ " vs materialized " ++ show pMat)
          (abs (pLazy - pMat) < 1e-9)
        assertEqual (label ++ ": dim") dMat dLazy
  , testCase "every filtered-scene observation together carries all the mass" $ do
      -- The queries below are every Scene the filter can *output* at depth 2, so
      -- their probabilities must sum to 1. This is the check the differential
      -- cannot make on its own: two paths agreeing on a wrong normalisation
      -- would still agree.
      prog <- parseOrFailSrc (progSrc "")
      let c = either (error . show) id (compile defaultCompilerConfig prog)
      let ps = [ fst (probDimOf (either (error . show) id (runProbC prog c [sym] q))) | (_, q) <- queries ]
      assertBool ("outputs sum to " ++ show (sum ps) ++ ", expected 1") (abs (sum ps - 1) < 1e-9)
  ]
  where
    -- The `of` clause is the only difference: with it the program routes to
    -- materializing enumeration over the whole Scene support, without it to
    -- plan-guided lazy structural inversion.
    progSrc ofClause = unlines
      [ "data Color = Red | Green"
      , "data Object = Nil | Obj color::Color"
      , "data Scene = List hd::Object, tl::Scene | Empty depth 2"
      , "neural readScene :: (Symbol -> Scene)" ++ ofClause
      , "main symbol = let scene = readScene symbol in filterGreen scene"
      -- Recurses to the end of the spine, replacing every non-green object with
      -- Nil. Deliberately total (the `isEmpty old` case comes first): the
      -- materializing oracle evaluates the filter at *every* scene in the
      -- support, so a filter that reads `tl old` before testing emptiness --
      -- as the program this feature came from does -- crashes there rather than
      -- yielding a comparison. See planEnumStructuralPartialTests for that case.
      , "filterGreen old = if isEmpty old"
      , "    then Empty"
      , "    else if isNil (hd old)"
      , "        then List Nil (filterGreen (tl old))"
      , "        else if isGreen (color (hd old))"
      , "            then List (hd old) (filterGreen (tl old))"
      , "            else List Nil (filterGreen (tl old))"
      ]
    -- Verbatim mock logits (mode 2), so both paths read one fixed distribution.
    sym = VTuple (VInt 2) (constructVList (map VFloat logits))
    -- 13 slots, exactly the plan the compiler prints as the read-logits network's required
    -- output layout; every softmax group sums to 1.
    logits = [ 0.6, 0.4          -- 0..1   Scene ctor flags: List|Empty
             , 0.3, 0.7          -- 2..3   List/f0 Object ctor flags: Nil|Obj
             , 0.25, 0.75        -- 4..5   List/f0/Obj/f0 Color: Red|Green
             , 0.55, 0.45        -- 6..7   List/f1 Scene ctor flags: List|Empty
             , 0.2, 0.8          -- 8..9   List/f1/List/f0 Object: Nil|Obj
             , 0.35, 0.65        -- 10..11 List/f1/List/f0/Obj/f0 Color: Red|Green
             , 1.0 ]             -- 12     List/f1/List/f1 Scene: Empty (depth-pruned)
    nil    = VADT "Nil" []
    obj c  = VADT "Obj" [VADT c []]
    empty  = VADT "Empty" []
    scene1 h = VADT "List" [h, empty]
    scene2 h t = VADT "List" [h, VADT "List" [t, empty]]
    queries =
      [ ("Empty",              empty)
      , ("[Nil]",              scene1 nil)
      , ("[Obj Green]",        scene1 (obj "Green"))
      , ("[Nil, Nil]",         scene2 nil nil)
      , ("[Nil, Obj Green]",   scene2 nil (obj "Green"))
      , ("[Obj Green, Nil]",   scene2 (obj "Green") nil)
      , ("[Obj Green, Obj Green]", scene2 (obj "Green") (obj "Green"))
      ]

-- | The shape this feature came from: a filter that reads @tl old@ before
-- testing emptiness, so it is undefined on an empty scene. It has no
-- materialized twin to check against (materialization evaluates the filter at
-- every scene in the support, including the empty one, and dies there), so what
-- is pinned instead is that the mass it does assign is exactly the probability
-- of the inputs on which it *is* defined -- i.e. the partiality costs the empty
-- input's mass and nothing else.
planEnumStructuralPartialTests :: TestTree
planEnumStructuralPartialTests = testGroup "planEnumStructuralPartial"
  [ testCase "partial filter's outputs carry exactly the defined inputs' mass" $ do
      prog <- parseOrFailSrc src
      let c = either (error . show) id (compile defaultCompilerConfig prog)
      let ps = [ fst (probDimOf (either (error . show) id (runProbC prog c [sym] q))) | q <- queries ]
      -- pSceneIsList is logit slot 0: every defined input has a List at the root.
      assertBool ("outputs sum to " ++ show (sum ps) ++ ", expected " ++ show pSceneIsList)
        (abs (sum ps - pSceneIsList) < 1e-9)
      assertBool "every listed output should be reachable" (all (> 0) ps)
  ]
  where
    pSceneIsList = 0.6
    src = unlines
      [ "data Color = Red | Green"
      , "data Object = Nil | Obj color::Color"
      , "data Scene = List hd::Object, tl::Scene | Empty depth 2"
      , "neural readScene :: (Symbol -> Scene)"
      , "main symbol = let scene = readScene symbol in filterGreen scene"
      , "filterGreen old = if isEmpty (tl old)"
      , "    then if isNil (hd old)"
      , "        then List Nil Empty"
      , "        else if isGreen (color (hd old))"
      , "            then List (hd old) Empty"
      , "            else List Nil Empty"
      , "    else if isNil (hd old)"
      , "        then List Nil (filterGreen (tl old))"
      , "        else if isGreen (color (hd old))"
      , "            then List (hd old) (filterGreen (tl old))"
      , "            else List Nil (filterGreen (tl old))"
      ]
    sym = VTuple (VInt 2) (constructVList (map VFloat
            [ 0.6, 0.4, 0.3, 0.7, 0.25, 0.75, 0.55, 0.45, 0.2, 0.8, 0.35, 0.65, 1.0 ]))
    nil   = VADT "Nil" []
    green = VADT "Obj" [VADT "Green" []]
    empty = VADT "Empty" []
    -- Every scene the partial filter can output: a one-element result for a
    -- one-element input, a two-element one for a two-element input.
    queries = [ VADT "List" [h, empty] | h <- [nil, green] ]
           ++ [ VADT "List" [h, VADT "List" [t, empty]] | h <- [nil, green], t <- [nil, green] ]

-- | Structural inversion routes its match-worlds through the milestone-4 value
-- grouping ('planSpecializeTarget'). Without that, a structure-returning
-- recursion costs one world per constructor per level: measured on this program
-- the emitted IR grew ~6.5x per level (75 KB at depth 2 to 52 MB at depth 6),
-- against ~2.5x with grouping (66 KB to 1.7 MB) -- a 31x saving at depth 6 that
-- grows with depth.
--
-- This pins the base, not polynomiality: unlike the counting folds
-- 'test_planEnumM4Polynomial' covers, structural inversion is still exponential
-- here, because the caller crosses each level's grouped worlds with its own
-- branches. Depths kept low deliberately -- depth 6 alone takes ~25 s.
test_planEnumStructuralGrouped :: TestTree
test_planEnumStructuralGrouped = testCase "planEnumStructuralGrouped" $ do
  let prog d = unlines
        [ "data Color = Red | Green"
        , "data Object = Nil | Obj color::Color"
        , "data Scene = List hd::Object, tl::Scene | Empty depth " ++ show d
        , "neural readScene :: (Symbol -> Scene)"
        , "main symbol = let scene = readScene symbol in filterGreen scene"
        , "filterGreen old = if isEmpty old"
        , "    then Empty"
        , "    else if isNil (hd old)"
        , "        then List Nil (filterGreen (tl old))"
        , "        else if isGreen (color (hd old))"
        , "            then List (hd old) (filterGreen (tl old))"
        , "            else List Nil (filterGreen (tl old))"
        ]
  let sizeAt :: Int -> IO Int
      sizeAt d = do
        p <- parseOrFailSrc (prog d)
        case compile defaultCompilerConfig p of
          Left e   -> assertFailure ("compile error at depth " ++ show d ++ ": " ++ show e)
          Right ir -> return (length (show ir))
  s3 <- sizeAt 3
  s5 <- sizeAt 5
  -- Ungrouped this ratio was ~17x (6.5 per level over two levels); grouped it is
  -- ~5x. A regression that switched grouping off would blow straight through 10.
  assertBool ("structural-inversion IR is growing at the ungrouped rate: s3=" ++ show s3
              ++ " s5=" ++ show s5 ++ " ratio=" ++ show (fromIntegral s5 / fromIntegral s3 :: Double))
    (s5 < 10 * s3)

parseOrFailSrc :: String -> IO Program
parseOrFailSrc src = case tryParseProgram "<inline>" src of
  Left err -> assertFailure ("Parse error: " ++ show err)
  Right p  -> return p

-- | Fast-group case: pins topK/branch-counting interaction on the cheapest
-- recursive-specialization shape (depth-3, single threaded-bool predicate),
-- so this behaviour class stays covered even though the pricier
-- multi-predicate chain moved to slowInternalsTests.
test_planEnumThreadedTopKAndBC :: TestTree
test_planEnumThreadedTopKAndBC = planEnumTopKAndBCTest "planEnumThreadedTopKAndBC" "planEnumRecThreaded"

test_planEnumRecTopKAndBC :: TestTree
test_planEnumRecTopKAndBC = planEnumTopKAndBCTest "planEnumRecTopKAndBC" "planEnumRecChain"

-- | Branch counting must not multiply the IR (fuzz-qc-compiler-bugs item 3).
--
-- A probability sum over an enumerated support needs two reductions over the
-- same loop body when @countBranches@ is on -- the probability and the branch
-- count. Read off an unshared body, each carries its own full copy of that
-- body; and since the body is the recursively-compiled sub-inference, at every
-- level of a nested enumerable chain that doubles what the level above copies,
-- which is exponential in the nesting depth. Measured before the single-loop
-- paired enum sum went in: 12.0 MB of shown IR at depth 6 against 0.72 MB
-- without branch counting (16.7x), 2x more per added level, and depth 8 did
-- not finish.
--
-- Pinned as a ratio against the same program's default compile at two depths,
-- because the failure mode is a per-level multiplier: any surviving
-- duplication shows up as a ratio that grows with depth, whichever level
-- reintroduces it. Same @length (show ir)@ node-count proxy the plan-enum
-- polynomial tests use.
--
-- The nesting is built as a Haskell 'Expr' rather than written as SPLL source
-- on purpose (it mirrors what the fuzz generator builds): SPLL-level recursion
-- compiles to a single shared 'IRApply' call, so a recursive @.ppl@ would not
-- exercise this inline-duplication class at all. Measured at -O0 for the same
-- reason -- the question is what the compiler emits, not what the optimizer
-- can claw back afterwards.
test_branchCountingDoesNotMultiplyIR :: TestTree
test_branchCountingDoesNotMultiplyIR = testCase "branchCountingDoesNotMultiplyIR" $ do
  -- Both operands of the outer plusI are enumerable and non-deterministic, so
  -- every level routes through the enumerated-sum path, and the right operand
  -- nests the next level inside an if.
  let nest :: Int -> Expr
      nest 0 = dice 3
      nest d = negIF (dice 5)
                 #<+># ifThenElse (bernoulli 0.4 #||# bernoulli 0.6) (dice 3) (nest (d - 1))
      prog d = Program [("main", nest d)] [] [] []
      sizeAt cb d =
        case compile defaultCompilerConfig{countBranches = cb, optimizerLevel = 0} (prog d) of
          Left e   -> assertFailure ("compile error at depth " ++ show d ++ ": " ++ show e)
          Right ir -> return (length (show ir))
  forM_ [4, 7] $ \d -> do
    plain <- sizeAt False d
    counted <- sizeAt True d
    let ratio = fromIntegral counted / fromIntegral plain :: Double
    assertBool ("branch counting multiplied the depth-" ++ show d ++ " IR: "
                ++ show plain ++ " -> " ++ show counted ++ " (" ++ show ratio ++ "x)")
      (counted < 2 * plain)

-- | Task recursive-list-prob-missed-cse: probability-mode compilation of a
-- self-recursive list (@main = if Uniform > p then [] else X : main@, the
-- README's own "Recursive lists" example) must cost work LINEAR in the query
-- list's length, not exponential.
--
-- Unlike 'test_branchCountingDoesNotMultiplyIR' just above -- whose own
-- comment notes that SPLL-level recursion compiles to a single shared
-- 'IRApply' call site, so it deliberately builds its nested-nonrecursive
-- 'Expr' by hand to exercise inline duplication -- the bug this pins lived
-- one level down: the recursive call site itself was never duplicated, but
-- the field-constructor equation for the list's Cons cell read the tail
-- field's (prob, dim, branch count, impossibility) result several times
-- (2-3x observed), each read re-triggering 'anySafeShared's decision to
-- SHARE that read afresh, without any guard of its own protecting it from
-- the caller's later applicability check. That multiplies once per list
-- element, giving the ~11-20x-per-element blowup the task doc measured
-- (Python: 0.0004s / 0.0071s / 0.1346s / 2.7250s at lengths 1-4), and
-- reproduces identically against the interpreter (measured while writing
-- this test: a clean ~3x-per-element blowup, 0.010s at length 3 to 23.4s at
-- length 10, on this exact program).
--
-- This is timed rather than sized. 'test_branchCountingDoesNotMultiplyIR'
-- and the plan-enum polynomial tests above pin their bugs against
-- @length (show ir)@ because those bugs unroll a bounded structure at
-- compile time, so a regression shows up as bigger IR. This bug is
-- different: the recursive function is compiled exactly ONCE regardless of
-- query length (genuine self-recursion, not compile-time unrolling), and
-- 'branchCount' -- the other structural instrument this suite uses -- is
-- *also* the wrong tool here (tried first; verified empirically): it counts
-- logical leaf resolutions, which stayed perfectly linear (2n+1) even on the
-- unpatched, exponentially-slow code, because every duplicate copy of the
-- tail field computes the *same* final count. The duplication was pure
-- wasted re-evaluation at runtime, invisible to any static count -- so wall
-- time is the only signal that actually distinguishes the two.
--
-- A linear implementation answers the length-18 query in low milliseconds;
-- the measured ~3x/element interpreter blowup above would need roughly
-- 3^8 =~ 6500x longer than length-10's 23s to reach length-18, so the
-- generous budget below still fails promptly on a regression.
test_recursiveListMissedCSE :: TestTree
test_recursiveListMissedCSE = testCase "recursiveListMissedCSE" $ do
  let src = unlines
        [ "data Sym = A"
        , "rec = if Uniform < 0.5 then [] else A : rec"
        , "main = rec"
        ]
  prog <- case tryParseProgram "recursiveListMissedCSE" src of
    Left err -> assertFailure ("parse error: " ++ show err)
    Right p  -> return p
  let compiled = either (\e -> error ("compile error: " ++ show e)) id (compile defaultCompilerConfig prog)
  let n = 18 :: Int
  let queryOfLength = VList (iterate (ListCont (VADT "A" [])) EmptyList !! n)
  let expected = 0.5 ^^ (n + 1) -- p(stop) * p(not stop)^n
  -- Force the (prob, dim) fields inside the timeout so it measures the
  -- recursive evaluation rather than returning instantly with an
  -- unevaluated thunk.
  result <- timeout (5 * 1000000) (evaluate (probDimOf' (runProbC prog compiled [] queryOfLength)))
  case result of
    Nothing -> assertFailure
      ("probability query on a " ++ show n ++ "-element recursive-list sample did not \
       \finish within 5s -- this is exactly the exponential missed-CSE blowup task \
       \recursive-list-prob-missed-cse fixed (a correct, linear implementation answers \
       \this in low milliseconds)")
    Just (p, _) ->
      assertBool ("probability " ++ show p ++ " does not match the expected " ++ show expected)
        (abs (p - expected) < 1e-9)
  where
    probDimOf' (Left e)  = error ("prob query error: " ++ show e)
    probDimOf' (Right v) = let (p, d) = probDimOf v in p `seq` d `seq` (p, d)

-- | Milestone-4 value-grouped DP acceptance: a counting fold compared against
-- a deterministic bound compiles to polynomially-sized IR. At milestone 2 the
-- fold enumerated 2^depth (value, world) pairs, so the IR grew exponentially;
-- the value DP collapses same-count worlds into one measured mass per count,
-- keeping the IR O(depth^2). We measure IR size as the length of the shown IR
-- (the same node-count proxy the orthant-refusal test uses) at depth 10 and
-- depth 30: a 2^depth blow-up would put depth 30 astronomically above depth 10
-- (ratio ~2^20), whereas the DP keeps the ratio a small polynomial factor. The
-- test completing at all also proves depth 30 does not hang or OOM.
test_planEnumM4Polynomial :: TestTree
test_planEnumM4Polynomial = testCase "planEnumM4Polynomial" $ do
  let prog d = unlines
        [ "data Color = Red | Green | Blue"
        , "data Object = Null | Obj color::Color"
        , "data Scene = Empty | SCons obj::Object, rest::Scene depth " ++ show d
        , "neural readScene :: (Symbol -> Scene)"
        , "numRed s = if isEmpty s then 0.0 else (if isObj (obj s) then (if isRed (color (obj s)) then 1.0 else 0.0) else 0.0) + numRed (rest s)"
        , "main sym = let scene = readScene sym in if numRed scene > 1.5 then 1 else 0"
        ]
  let sizeAt :: Int -> IO Int
      sizeAt d = case tryParseProgram "m4" (prog d) of
        Left e  -> assertFailure ("parse error at depth " ++ show d ++ ": " ++ show e)
        Right p -> case compile defaultCompilerConfig p of
          Left e   -> assertFailure ("compile error at depth " ++ show d ++ ": " ++ show e)
          Right ir -> return (length (show ir))
  s10 <- sizeAt 10
  s30 <- sizeAt 30
  assertBool ("depth-30 counting-fold IR is not polynomially bounded (2^depth would give a ~10^6 ratio): s10="
              ++ show s10 ++ " s30=" ++ show s30 ++ " ratio=" ++ show (fromIntegral s30 / fromIntegral s10 :: Double))
    (s30 < 30 * s10)

-- | The same value-grouped DP acceptance, on the BOOL path ('planGroupBool').
-- A recursive Bool predicate reaches its recursive call through one disjoint
-- world per @Object@ constructor (here: @obj@ is @Null@, or it is @Obj@ with a
-- non-Red colour), so before grouping the polarity world sets multiplied by
-- the constructor count at every level -- measured at 2.0x per level for a
-- 2-constructor Object and 3.0x for a 3-constructor one. Grouping collapses
-- each polarity into one summed mass per level, restoring the distributive
-- law. Same size proxy and same depth pair as 'test_planEnumM4Polynomial'.
--
-- Note this predicate is deliberately the Bool twin of the M4 counting fold
-- above: same data declarations, same per-level branch structure, but the
-- result is a Bool rather than a counted value, so it routes through
-- 'planInvertBool'/'planSpecializeBool' instead of 'planEnumValues'.
--
-- The depth pair is 8/12 rather than M4's 10/30 ON PURPOSE. Measured on this
-- program, the ungrouped Bool path costs 57 s and 36 MB of emitted code at
-- depth 12 and exceeds a 6 GB cap at depth 16 -- so at M4's depth 30 a
-- regression would OOM-kill the whole test process (it did, when this test
-- was first written that way) and take every other test's result with it.
-- At 8/12 a regression instead fails red in about a minute. The margin is
-- still wide: measured emitted-code ratio is 1.44x grouped against 23x
-- ungrouped, so the 6x threshold has ~4x headroom on both sides.
test_planEnumBoolCtorPolynomial :: TestTree
test_planEnumBoolCtorPolynomial = testCase "planEnumBoolCtorPolynomial" $ do
  let prog d = unlines
        [ "data Color = Red | Green | Blue"
        , "data Object = Null | Obj color::Color"
        , "data Scene = Empty | SCons obj::Object, rest::Scene depth " ++ show d
        , "neural readScene :: (Symbol -> Scene)"
        , "existsRed s = if isEmpty s then False else (if isObj (obj s) then (if isRed (color (obj s)) then True else existsRed (rest s)) else existsRed (rest s))"
        , "main sym = let scene = readScene sym in if existsRed scene then 1 else 0"
        ]
  let sizeAt :: Int -> IO Int
      sizeAt d = case tryParseProgram "boolctor" (prog d) of
        Left e  -> assertFailure ("parse error at depth " ++ show d ++ ": " ++ show e)
        Right p -> case compile defaultCompilerConfig p of
          Left e   -> assertFailure ("compile error at depth " ++ show d ++ ": " ++ show e)
          Right ir -> return (length (show ir))
  s8  <- sizeAt 8
  s12 <- sizeAt 12
  assertBool ("depth-12 recursive Bool-predicate IR is not polynomially bounded (ungrouped c^depth measures ~23x here, grouped ~1.4x): s8="
              ++ show s8 ++ " s12=" ++ show s12 ++ " ratio=" ++ show (fromIntegral s12 / fromIntegral s8 :: Double))
    (s12 < 6 * s8)

-- | Fused joint-state DP acceptance. Two predicates over one scene are
-- exponential (two readers turn 'psMerge' off); folding them into ONE
-- traversal that threads a joint automaton state through deterministic
-- arguments restores the single reader, and the grouping DP then collapses
-- each level to one world per reachable state.
--
-- This is the shape 'foldConstIn' was extended for: the @==@ InjF emits its
-- operands as let-bindings (@let a = 0 in let b = 1 in a == b@), so with a
-- constant-only fold the state test was undecidable, every (value, world) pair
-- was unmergeable, and this program OOM-ed by depth 8. Measured before/after
-- at depth 6: 10.6 MB -> 226 KB.
test_planEnumFusedJointStatePolynomial :: TestTree
test_planEnumFusedJointStatePolynomial = testCase "planEnumFusedJointStatePolynomial" $ do
  let prog d = unlines
        [ "data Color = Red | Green | Blue"
        , "data Size = Small | Large"
        , "data Object = Nil | Obj color::Color, size::Size"
        , "data Scene = Empty | SCons obj::Object, rest::Scene depth " ++ show d
        , "neural readScene :: (Symbol -> Scene)"
        , "go s red lg = if isEmpty s"
        , "  then (if red then 1 else (if lg == 1 then 2 else 0))"
        , "  else (if isNil (obj s)"
        , "    then go (rest s) red lg"
        , "    else (if isRed (color (obj s))"
        , "      then (if isLarge (size (obj s))"
        , "              then (if lg == 0 then go (rest s) True 1 else go (rest s) True 2)"
        , "              else go (rest s) True lg)"
        , "      else (if isLarge (size (obj s))"
        , "              then (if lg == 0 then go (rest s) red 1 else go (rest s) red 2)"
        , "              else go (rest s) red lg)))"
        , "main sym = let scene = readScene sym in go scene False 0"
        ]
  let sizeAt :: Int -> IO Int
      sizeAt d = case tryParseProgram "joint" (prog d) of
        Left e  -> assertFailure ("parse error at depth " ++ show d ++ ": " ++ show e)
        Right p -> case compile defaultCompilerConfig p of
          Left e   -> assertFailure ("compile error at depth " ++ show d ++ ": " ++ show e)
          Right ir -> return (length (show ir))
  s4 <- sizeAt 4
  s8 <- sizeAt 8
  assertBool ("depth-8 fused joint-state IR is not polynomially bounded (unmergeable pairs OOM-ed here before foldConstIn): s4="
              ++ show s4 ++ " s8=" ++ show s8 ++ " ratio=" ++ show (fromIntegral s8 / fromIntegral s4 :: Double))
    (s8 < 6 * s4)

-- | Milestone-3 refusal rule, kept precise: a world that couples a continuous
-- plan leaf pairwise and also bounds it, or couples it twice, is a correlated
-- orthant probability -- quadrature the language excludes by design. The plan
-- engine must decline at compile time with the orthant diagnostic (surfaced
-- through the set-witness refusal) rather than emit wrong code.
planOverCouplingRefusalTests :: TestTree
planOverCouplingRefusalTests = testGroup "plan-guided M3 over-coupling refusal"
  [ testCase "coupled leaf additionally bounded refuses with the orthant diagnostic" $
      expectOrthantRefusal
        "neural readPair :: (Symbol -> (Float, Float))\nmain sym = let p = readPair sym in if fst p > snd p then (if fst p > 0.5 then 2 else 1) else 0\n"
  , testCase "leaf coupled twice refuses with the orthant diagnostic" $
      expectOrthantRefusal
        "neural readTri :: (Symbol -> (Float, (Float, Float)))\nmain sym = let p = readTri sym in if fst p > fst (snd p) then (if fst p > snd (snd p) then 2 else 1) else 0\n"
  ]

expectOrthantRefusal :: String -> IO ()
expectOrthantRefusal src = do
  let prog = either (\e -> error ("parse failed: " ++ show e)) id (tryParseProgram "test" src)
  r <- try (evaluate (either (error . show) (length . show) (compile defaultCompilerConfig prog)))
  case r of
    Left (ErrorCall msg) -> assertBool
      ("expected the orthant-probability diagnostic, got: " ++ msg)
      ("orthant" `isInfixOf` msg)
    Right _ -> assertFailure "expected a compile-time refusal, but compilation succeeded"

-- | Count occurrences of @IRVar name@ in an expression.
countIRVar :: String -> IRExpr -> Int
countIRVar name (IRVar n) | n == name = 1
countIRVar name e = sum (map (countIRVar name) (getIRSubExprs e))

-- The optimizer must treat a nullary generator reference (IRVar "..._gen",
-- effectful) differently from a pure local reference. These white-box tests pin
-- the single `isPure` mechanism (task ir-effectful-var-purity) at both duplicating
-- sites: optimizeLetIns (inlining) and CSE (sharing).
optimizerPurityTests :: TestTree
optimizerPurityTests = testGroup "optimizer purity (ir-effectful-var-purity)"
  -- isPure classifies a generator reference and a sample as effectful, a plain
  -- local as pure.
  [ testCase "isPure classifies effectful vs pure references" $ do
      assertBool "coin_gen is effectful" (not (isPure (IRVar "coin_gen")))
      assertBool "nn_auto_gen is effectful" (not (isPure (IRVar "nn_auto_gen")))
      assertBool "IRSample is effectful" (not (isPure (IRSample IRNormal)))
      assertBool "plain local is pure" (isPure (IRVar "d"))
      assertBool "op over locals is pure" (isPure (IROp OpPlus (IRVar "d") (IRConst (VFloat 1))))
      assertBool "op containing a generator ref is effectful"
        (not (isPure (IROp OpPlus (IRVar "coin_gen") (IRConst (VFloat 1)))))
  -- A let binding a generator reference must NOT be inlined into its two uses:
  -- that would re-draw the sample. The let survives and coin_gen still occurs once.
  , testCase "optimizeLetIns keeps a multi-use generator binding shared" $ do
      let expr = IRLetIn "d" (IRVar "coin_gen")
                   (IROp OpPlus (IRVar "d") (IRVar "d"))
          opt  = postProcess defaultCompilerConfig expr
      assertEqual "coin_gen sampled exactly once" 1 (countIRVar "coin_gen" opt)
  -- A pure bare-variable binding, by contrast, is copy-propagated into both uses
  -- (the binding disappears) -- the behaviour the old IRConst-only rule blocked.
  , testCase "optimizeLetIns copy-propagates a pure variable binding" $ do
      let expr = IRLetIn "d" (IRVar "x")
                   (IROp OpPlus (IRVar "d") (IRVar "x"))
          opt  = postProcess defaultCompilerConfig expr
      assertEqual "d fully inlined" 0 (countIRVar "d" opt)
      assertEqual "x appears at both uses" 2 (countIRVar "x" opt)
  -- CSE must NOT collapse two occurrences of an expression built from a generator
  -- reference into one shared binding: that would fuse two independent draws.
  , testCase "CSE does not share a repeated generator-referencing subexpression" $ do
      let sub  = IROp OpMult (IRVar "coin_gen") (IRConst (VFloat 2))
          expr = IROp OpPlus sub sub
          opt  = postProcess defaultCompilerConfig expr
      assertEqual "both draws survive" 2 (countIRVar "coin_gen" opt)
  -- ...whereas a repeated pure subexpression is shared as usual (one binding, one
  -- occurrence of each pure leaf), confirming the refusal above is specific to
  -- effectfulness, not a blanket disabling of CSE.
  , testCase "CSE still shares a repeated pure subexpression" $ do
      let sub  = IROp OpMult (IRVar "x") (IRConst (VFloat 2))
          expr = IROp OpPlus sub sub
          opt  = postProcess defaultCompilerConfig expr
      assertEqual "x read once through the shared binding" 1 (countIRVar "x" opt)
  ]

-- ---------------------------------------------------------------------------
-- Stochastic calls and shared conditions (task stochastic-call-cse-unsound)
-- ---------------------------------------------------------------------------

-- | The @_gen@ half of an environment is not referentially transparent: calling
-- it twice is meant to draw twice. Every optimizer rewrite that either /shares/
-- two occurrences of an expression (CSE) or /drops/ one of several syntactically
-- equal copies ('distributeIf') must therefore consult the purity analysis, and
-- that analysis has to see through a whole-program call graph -- a call into a
-- recursive generate group holds no 'IRSample' of its own, only a reference to a
-- group whose body has one.
--
-- The reported repros were a branching-recursive generate function
-- (@Node (genT thetas) (genT thetas)@ collapsing to one shared subtree) and a
-- two-argument version of the same shape emitting a partially applied call. Both
-- are covered today -- by 'deterministicGens' feeding 'isPureGiven', and by
-- CSE's refusal to hoist a partial application -- so these rows are the
-- regression pins rather than a new fix. The 'distributeIf' rows are the one
-- live hole the same audit found: it kept a single copy of a condition the
-- tuple evaluated once per leaf.
stochasticCallTests :: TestTree
stochasticCallTests = testGroup "stochastic calls (stochastic-call-cse-unsound)"
  -- The whole-program analysis, directly. A generate group is deterministic
  -- exactly when nothing it can reach draws.
  [ testCase "deterministicGens classifies a call graph" $ do
      let det = deterministicGens
            [ genGroup "stoch" (IRSample IRUniform)
            , genGroup "pureG" (IRConst (VFloat 1.0))
            , genGroup "selfRec" (IRApply (IRVar "selfRec_gen") (IRConst (VFloat 1.0)))
            , genGroup "caller" (IRApply (IRVar "stoch_gen") (IRConst (VFloat 1.0)))
            , genGroup "neuralCaller" (IRApply (IRVar "nn_auto_gen") (IRConst (VFloat 1.0)))
            ]
      assertBool "a body that samples is not deterministic" (not (Set.member "stoch_gen" det))
      assertBool "a sample-free body is deterministic" (Set.member "pureG_gen" det)
      assertBool "self-recursion alone does not refute determinism"
        (Set.member "selfRec_gen" det)
      assertBool "calling a stochastic group is not deterministic"
        (not (Set.member "caller_gen" det))
      assertBool "calling a generator with no visible group is not deterministic"
        (not (Set.member "neuralCaller_gen" det))
  -- Repro 2 of the task, at IR level: two saturated calls into a stochastic,
  -- self-recursive generate group are two independent draws and must both survive.
  , testCase "CSE keeps both calls into a stochastic generate group" $ do
      let call = IRApply (IRVar "genT_gen") (IRVar "thetas")
          body = IRIf (IROp OpLessThan (IRSample IRUniform) (IRConst (VFloat 0.6)))
                      (IRConst (VFloat 0.0))
                      (IRTCons call call)
      assertEqual "both recursive draws survive" 2
        (countIRVar "genT_gen" (optimizedGen "genT" [genGroup "genT" body]))
  -- ...and the positive control: the identical shape with a *deterministic*
  -- callee is shared, so the refusal above is about effects, not about calls.
  , testCase "CSE still shares calls into a deterministic generate group" $ do
      let call = IRApply (IRVar "detT_gen") (IRVar "thetas")
          body = IRIf (IROp OpLessThan (IRVar "thetas") (IRConst (VFloat 0.6)))
                      (IRConst (VFloat 0.0))
                      (IRTCons call call)
          env  = [ genGroup "caller" body
                 , genGroup "detT" (IRConst (VFloat 1.0)) ]
      assertEqual "the deterministic call is read once through a shared binding" 1
        (countIRVar "detT_gen" (optimizedGen "caller" env))
  -- distributeIf keeps one copy of a condition the tuple evaluated once per
  -- leaf, so an effectful condition would have its draws fused --
  -- @(if Uniform < 0.5 then 0 else 1, if Uniform < 0.5 then 0 else 1)@ would
  -- stop producing the mixed outcomes altogether
  -- (testCases/tupleSharedCondIndependentDraws).
  , testCase "distributeIf refuses to fuse an effectful shared condition" $ do
      let cond = IROp OpLessThan (IRSample IRUniform) (IRConst (VFloat 0.5))
          arm x y = IRIf cond (IRConst (VInt x)) (IRConst (VInt y))
          tup = IRTCons (arm 0 1) (arm 0 1)
      assertEqual "the tuple is left alone" tup (distributeIf noDetGens False tup)
      assertEqual "...also under the -O3 constant-merging variant" tup
        (distributeIf noDetGens True tup)
  -- The pure direction still distributes, so the gate above is not a blanket
  -- disabling of the rewrite.
  , testCase "distributeIf still hoists a pure shared condition" $ do
      let cond = IROp OpLessThan (IRVar "x") (IRConst (VFloat 0.5))
          arm x y = IRIf cond (IRConst (VInt x)) (IRConst (VInt y))
          tup = IRTCons (arm 0 1) (arm 2 3)
      assertEqual "condition hoisted in front of the tuple"
        (IRIf cond (IRTCons (IRConst (VInt 0)) (IRConst (VInt 2)))
                   (IRTCons (IRConst (VInt 1)) (IRConst (VInt 3))))
        (distributeIf noDetGens False tup)
  -- A condition that calls a generate group is judged by the whole-program
  -- analysis, not by the name alone: the same tuple is refused when the callee
  -- samples and hoisted when it does not.
  , testCase "distributeIf judges a generator condition by deterministicGens" $ do
      let cond = IROp OpLessThan (IRApply (IRVar "c_gen") (IRVar "t")) (IRConst (VFloat 0.5))
          arm x y = IRIf cond (IRConst (VInt x)) (IRConst (VInt y))
          tup = IRTCons (arm 0 1) (arm 2 3)
          envWith b = OptEnv (deterministicGens [genGroup "c" b]) Set.empty
      assertEqual "a stochastic callee blocks the hoist" tup
        (distributeIf (envWith (IRSample IRUniform)) False tup)
      assertBool "a deterministic callee does not"
        (distributeIf (envWith (IRConst (VFloat 1.0))) False tup /= tup)
  -- Repro 1 of the task: the two calls differ in their *second* argument, so the
  -- shared @genS_gen thetas@ prefix is a partial application. Hoisting it emits
  -- a call with the wrong arity (the scalar backends flatten an application
  -- spine into one call site), which crashed the generated Python with a
  -- TypeError. Both calls must stay written out in full.
  , testCase "CSE does not hoist a shared partial-application prefix" $ do
      let call a = IRApply (IRApply (IRVar "genS_gen") (IRVar "thetas")) a
          body = IRIf (IROp OpLessThan (IRSample IRUniform) (IRConst (VFloat 0.6)))
                      (IRVar "cont")
                      (call (IRCons (IRConst (VInt 1)) (call (IRVar "cont"))))
          opt = optimizedGen "genS" [genGroup "genS" body]
      assertEqual "both call sites keep their own head" 2 (countIRVar "genS_gen" opt)
      assertBool "no binding holds a partially applied generator"
        (not (any hoistedGenPrefix (irLetBindings opt)))
  ]
  where
    noDetGens = OptEnv Set.empty Set.empty
    genGroup n body = IRFunGroup { groupName = n, genFun = Just (body, "")
                                 , probFun = Nothing, integFun = Nothing
                                 , writeLogitsFun = Nothing, normalFun = Nothing
                                 , groupDoc = "", sampleDomain = Nothing }
    -- Optimize a whole environment (so 'deterministicGens' sees the call graph)
    -- and hand back the named group's generate body.
    optimizedGen n groups =
      case optimizeEnv defaultCompilerConfig (IREnv groups [] []) of
        IREnv groups' _ _ ->
          case [b | g <- groups', groupName g == n, Just (b, _) <- [genFun g]] of
            (b:_) -> b
            []    -> error ("optimizedGen: no generate body for " ++ n)
    irLetBindings e = [v | IRLetIn _ v _ <- flatten e]
    flatten e = e : concatMap flatten (getIRSubExprs e)
    -- @genS_gen@ is binary here, so a one-argument spine bound to a let is
    -- necessarily the partial application repro 1 crashed on.
    hoistedGenPrefix (IRApply (IRVar n) _) = isEffectfulVar n
    hoistedGenPrefix _                     = False

-- ---------------------------------------------------------------------------
-- Batched-mode refusals with no corpus trigger (design pytorch-tensorizer)
-- ---------------------------------------------------------------------------

-- | The corpus-driven rows in "End2EndTesting" ('End2EndTesting.batchedRefusalTests')
-- cover every batched fragment refusal a real @.ppl@ can reach. A handful cannot
-- be reached from any program, because another guard always fires first — most
-- notably the non-scalar 'MultiValue' gate on 'IREnumSum'/'IRIsPossible': every
-- Either/ADT-shaped read-logits network emits an 'IRIsLeft', or trips the ADT-declaration
-- bail, long before a composite enumeration could reach the emitter. That
-- ordering makes the gate correct today but leaves it with no positive control,
-- so a refactor could silently delete it — and deleting it emits Python naming
-- runtime constructors (@Left@, @ConsInferenceList@, ADT constructors) that
-- exist only in the *scalar* @pythonLib.py@, dying with a @NameError@ instead of
-- being refused. These rows call the guards directly on hand-built 'IRExpr'
-- values, and include the accepting direction so a gate that refused everything
-- would not pass.
batchedRefusalUnitTests :: TestTree
batchedRefusalUnitTests = testGroup "batched refusal (synthetic IR)" $
  -- Composite MultiValues: both MultiValue-carrying nodes must refuse each.
  [ testCase (nodeName ++ " over " ++ mvName ++ " is refused") $
      assertRefusal needle (mkNode mv)
  | (nodeName, needle, mkNode) <-
      [ ("IREnumSum",    "enumeration sum (IREnumSum)",
         \mv -> IREnumSum "v" mv (IRVar "v"))
      , ("IRIsPossible", "membership check (IRIsPossible)",
         \mv -> IRIsPossible mv (IRVar "sample")) ]
  , (mvName, mv) <-
      [ ("MultiTuple",     MultiTuple (MultiDiscretes [VInt 0, VInt 1]) (MultiDiscretes [VBool True]))
      , ("MultiEither",    MultiEither (MultiDiscretes [VInt 0]) (MultiDiscretes [VInt 1]))
      , ("MultiADT",       MultiADT [("A", [MultiDiscretes [VInt 0]]), ("B", [])])
      , ("MultiDiscretes with a tuple value",
                           MultiDiscretes [VTuple (VInt 0) (VInt 1), VTuple (VInt 1) (VInt 0)])
      , ("MultiDiscretes with an Either value",
                           MultiDiscretes [VEither (Left (VInt 0)), VEither (Right (VInt 1))])
      , ("MultiContinuous", MultiContinuous)
      , ("empty MultiDiscretes", MultiDiscretes []) ]
  ] ++
  -- The accepting direction: a flat scalar enumeration is in the fragment.
  [ testCase (nodeName ++ " over a flat scalar MultiDiscretes is accepted") $
      assertAccepted (mkNode (MultiDiscretes [VInt 0, VInt 7]))
        >> assertAccepted (mkNode (MultiDiscretes [VBool True, VBool False]))
        >> assertAccepted (mkNode (MultiDiscretes [VFloat 0.5]))
  | (nodeName, mkNode) <-
      [ ("IREnumSum",    \mv -> IREnumSum "v" mv (IRVar "v"))
      , ("IRIsPossible", \mv -> IRIsPossible mv (IRVar "sample")) ]
  ] ++
  -- Further 'reason' rows with no corpus trigger.
  [ testCase "IRMap is refused" $
      assertRefusal "list map (IRMap)"
        (IRMap (IRLambda "x" (IRVar "x")) (IRVar "xs"))
  , testCase "the VAnyExcept marginal sentinel is refused" $
      assertRefusal "marginal ANY-except sentinel (IRConst VAnyExcept)"
        (IROp OpEq (IRVar "sample") (IRConst (VAnyExcept [IRConst (VInt 0)])))
  , testCase "a residual IRConformsTo (not at the root) is refused" $
      -- prepBatchedBody strips only a *root* query-type guard; one nested
      -- anywhere else would reach the emitter, which has no case for it.
      assertRefusal "type-conformance check (IRConformsTo)"
        (IROp OpAnd (IRVar "b") (IRConformsTo TFloat (IRVar "sample")))
  , testCase "a residual isAny check is refused" $
      -- pruneAny rewrites these away, so reaching the guard with one means the
      -- pruning pass was bypassed or regressed.
      assertRefusal "marginal (ANY) check (IRUnaryOp OpIsAny)"
        (IRUnaryOp OpIsAny (IRVar "sample"))
  , testCase "an inner lambda is refused" $
      assertRefusal "inner lambda (IRLambda)"
        (IROp OpPlus (IRVar "x") (IRApply (IRLambda "y" (IRVar "y")) (IRVar "x")))
  , testCase "Either dispatch is accepted (the tag is part of the signature)" $
      -- Heterogeneous M2: within a bucket the constructor tag is uniform, so
      -- `isinstance(x, Left)` is a Python bool and the arm accessor the emitted
      -- code takes is always the legal one.
      mapM_ assertAccepted
        [ IRLeft (IRVar "x"), IRRight (IRVar "x")
        , IRFromLeft (IRVar "e"), IRFromRight (IRVar "e")
        , IRIsLeft (IRVar "e"), IRIsRight (IRVar "e")
        , IRConst (VEither (Left (VFloat 1.0))) ]
  , testCase "a value-dependent select between Either arms is refused" $
      assertRefusal "arms have different structure"
        (IRSelect (IROp OpGreaterThan (IRVar "x") (IRConst (VFloat 0.0)))
                  (IRLeft (IRVar "x")) (IRRight (IRVar "x")))
  , testCase "an offender nested deep in a let-spine is still found" $
      -- 'batchedGuard' walks the whole tree, not just the root.
      assertRefusal "list map (IRMap)"
        (IRLetIn "a" (IRConst (VFloat 1.0))
          (IRLetIn "b" (IROp OpPlus (IRVar "a") (IRMap (IRLambda "x" (IRVar "x")) (IRVar "xs"))) (IRVar "b")))
  -- Heterogeneous batching, M1: the list *spine* operations are in the fragment
  -- (within a shape bucket they are uniform Python structure over [B] leaves),
  -- but the branch that would have to *choose* between two structures is not --
  -- torch.where has nothing to select with. Bucketing removes the shape-directed
  -- ones; a value-dependent one is a genuine refusal.
  , testCase "SoA list access (head/tail/cons, empty-list constant) is accepted" $
      mapM_ assertAccepted
        [ IRHead (IRVar "xs")
        , IRTail (IRVar "xs")
        , IRCons (IRVar "x") (IRConst (VList EmptyList))
        , IROp OpEq (IRVar "xs") (IRConst (VList EmptyList)) ]
  , testCase "a non-empty list constant is still refused" $
      -- It carries per-element data, not structure: the batched runtime has no
      -- reader for it (task batched-bool-enum-index).
      assertRefusal "constant with no batched representation (VList"
        (IROp OpEq (IRVar "xs") (IRConst (VList (ListCont (VBool True) EmptyList))))
  , testCase "a value-dependent select between two structures is refused" $
      assertRefusal "arms have different structure"
        (IRSelect (IROp OpGreaterThan (IRVar "x") (IRConst (VFloat 0.0)))
                  (IRCons (IRVar "x") (IRConst (VList EmptyList)))
                  (IRConst (VList EmptyList)))
  , testCase "a shape-directed if between two structures is accepted" $
      -- The same shape, but branching on an emptiness probe: uniform within a
      -- bucket, so it stays ordinary Python control flow.
      assertAccepted
        (IRIf (IROp OpEq (IRVar "xs") (IRConst (VList EmptyList)))
              (IRConst (VList EmptyList))
              (IRCons (IRVar "x") (IRConst (VList EmptyList))))
  -- Generate-only recursion ('hasGenCycle'): unreachable from the corpus,
  -- because a recursive program's *prob* path trips 'checkCallGraph' first
  -- (e.g. dice). Driven through 'generateFunctionsBatched' on a group that has
  -- only a generate method, so there is no prob/integ root to check at all.
  , testCase "a self-recursive generate body is refused" $
      case generateFunctionsBatched False (recGenEnv (IRVar "rec_gen")) of
        Right _  -> assertFailure "batched mode accepted a self-recursive generate body"
        Left msg -> assertBool ("wrong diagnostic for recursive generate: " ++ msg)
                      ("generate function recurses" `isInfixOf` msg)
  , testCase "a non-recursive generate body of the same shape is accepted" $
      case generateFunctionsBatched False (recGenEnv (IRSample IRNormal)) of
        Right _  -> return ()
        Left msg -> assertFailure ("batched mode refused a plain generate body: " ++ msg)
  -- Task batched-ctor-test-not-structural-eager-accessor: a constructor tag is
  -- part of the bucket signature (M2), exactly as an Either tag is, so
  -- `is<Ctor>` is a shape-directed condition and its `if` stays lazy Python
  -- control flow. Emitting it as a torch.where instead evaluates both arms, and
  -- the masked-away one reaches a sibling constructor's field accessor.
  , testCase "an ADT constructor test is a structural condition" $ do
      let env = adtEnv [ADTDecl { dataName = "Opt"
                                , constructors = [("Nada", []), ("Just1", [("v", TFloat)])]
                                , adtDepth = Nothing }]
      assertBool "isNada(x) is not classified as structural"
        (structural env (IRApply (IRVar "isNada") (IRVar "x")))
      assertBool "isJust1(x) is not classified as structural"
        (structural env (IRApply (IRVar "isJust1") (IRVar "x")))
      assertBool "a name bound to a constructor test is not structural"
        (structural env (IRLetIn "t" (IRApply (IRVar "isNada") (IRVar "x")) (IRVar "t")))
      assertBool "an unrelated is-prefixed call must not be structural"
        (not (structural env (IRApply (IRVar "isClose") (IRVar "x"))))
      assertBool "a per-element comparison must not be structural"
        (not (structural env (IROp OpGreaterThan (IRVar "x") (IRConst (VFloat 0.0)))))
  , testCase "a constructor-tested arm is emitted lazily, not as a torch.where" $
      -- The accessor in the taken arm belongs to `Just1`, so evaluating it
      -- eagerly on a `Nada` would raise. It must sit inside an `if:` block.
      case generateFunctionsBatched False (nullaryCtorEnv' (IRVar "sample")) of
        Left msg -> assertFailure ("batched mode refused a constructor-guarded accessor: " ++ msg)
        Right ls -> do
          assertBool ("constructor test not emitted as an if statement: " ++ unlines ls)
            (any ("if isJust1(sample):" `isInfixOf`) ls)
          assertBool ("accessor still evaluated eagerly under torch.where: " ++ unlines ls)
            (not (any (\l -> "torch.where" `isInfixOf` l && "v(sample)" `isInfixOf` l) ls))
  -- Task batched-nullary-adt-ctor-emitted-as-bare-class: the compiler refers to
  -- a nullary constructor by a bare 'IRVar', so an emitter that prints the name
  -- verbatim yields the *class*, which never satisfies an @is\<Ctor\>@ predicate
  -- and never compares equal to an instance. The scalar backend instantiates it
  -- (its @callableNames@); the batched one has to do the same.
  , testCase "a nullary ADT constructor is emitted as an instantiation" $
      case generateFunctionsBatched False (nullaryCtorEnv (IRVar "Nada")) of
        Left msg -> assertFailure ("batched mode refused a nullary constructor reference: " ++ msg)
        Right ls -> do
          assertBool ("nullary constructor emitted as a bare class: " ++ unlines ls)
            (any ("(Nada)()" `isInfixOf`) ls)
          assertBool ("nullary constructor still emitted bare somewhere: " ++ unlines ls)
            (not (any (\l -> "isNada(Nada)" `isInfixOf` l) ls))
  , testCase "an applied ADT constructor is left as a call, not instantiated twice" $
      -- Only the *nullary* clause fires: @Just1 x@ is already a call.
      case generateFunctionsBatched False (nullaryCtorEnv (IRApply (IRVar "Just1") (IRVar "sample"))) of
        Left msg -> assertFailure ("batched mode refused an applied constructor: " ++ msg)
        Right ls -> assertBool ("applied constructor mis-emitted: " ++ unlines ls)
                      (any ("Just1(sample)" `isInfixOf`) ls)
  , testCase "a list-building recursive generate degrades to a stub, not a refusal" $
      -- The one narrow exception to the hard whole-program refusal rule: a
      -- generate whose recursion *builds a list* has per-element depth (design
      -- heterogeneous-batch-inference Component 4), but refusing the whole
      -- program for it would take the program's bucketable prob/integ down too.
      case generateFunctionsBatched False (recGenEnv (IRCons (IRSample IRNormal) (IRVar "rec_gen"))) of
        Left msg -> assertFailure ("batched mode refused a list-valued recursive generate "
                                   ++ "instead of stubbing it: " ++ msg)
        Right ls -> assertBool ("stub does not raise NotImplementedError: " ++ unlines ls)
                      (any ("NotImplementedError" `isInfixOf`) ls)
  -- Task batched-cse-lifts-fromleft-above-its-guard: CSE routinely names a
  -- structural condition through the `let cse_0 = (if isLeft(sample) then
  -- True else False) in ...` idiom. Before this fix `structural` had no case
  -- for 'IRIf', so the *value* bound to `cse_0` was judged non-structural
  -- (even though its own condition, 'IRIsLeft', is recognised) and `bindS`
  -- dropped `cse_0` from the structural environment. Every later use of
  -- `cse_0` as a guard then fell through to the eager torch.where emission,
  -- reaching an arm-legal `fromLeft` accessor on a `Right` sample.
  , testCase "a let-bound alias of a structural if-then-else is structural" $ do
      let env = adtEnv []
          isLeftBool = IRIf (IRIsLeft (IRVar "sample"))
                             (IRConst (VBool True)) (IRConst (VBool False))
      assertBool "the isLeft(sample) if-then-else idiom is not itself structural"
        (structural env isLeftBool)
      assertBool "a name bound to it is not classified as structural"
        (structural env (IRLetIn "cse_0" isLeftBool (IRVar "cse_0")))
      assertBool "a per-element if-then-else must not be structural"
        (not (structural env (IRIf (IROp OpGreaterThan (IRVar "x") (IRConst (VFloat 0.0)))
                                    (IRConst (VBool True)) (IRConst (VBool False)))))
  , testCase "an arm-legal accessor guarded by a let-bound structural alias stays lazy" $
      -- `fromLeft(sample)` is legal only under `cse_0`; emitting the guard as
      -- torch.where would evaluate it unconditionally, on every bucket.
      case generateFunctionsBatched False (structuralAliasEnv (IRVar "sample")) of
        Left msg -> assertFailure ("batched mode refused a structural-alias-guarded accessor: " ++ msg)
        Right ls -> do
          assertBool ("structural alias not emitted as an if statement: " ++ unlines ls)
            (any ("if cse_0:" `isInfixOf`) ls)
          assertBool ("accessor still evaluated eagerly under torch.where: " ++ unlines ls)
            (not (any (\l -> "torch.where" `isInfixOf` l && "fromLeft(sample)" `isInfixOf` l) ls))
  ]
  where
    -- A one-group environment declaring a mixed-arity ADT, whose prob method
    -- tests the given constructor reference. The ADT itself is only *consumed*
    -- (the method answers a float), which is the one shape that reaches a
    -- constructor through the batched path -- an ADT-valued query is refused.
    nullaryCtorEnv ctorRef = IREnv
      [IRFunGroup { groupName = "main"
                  , probFun = Just (IRLambda "sample"
                      (IRIf (IRApply (IRVar "isNada") ctorRef)
                            (IRConst (VFloat 1.0)) (IRConst (VFloat 0.0))), "")
                  , genFun = Nothing, integFun = Nothing
                  , writeLogitsFun = Nothing, normalFun = Nothing, groupDoc = ""
                  , sampleDomain = Nothing }]
      [ADTDecl { dataName = "Opt"
               , constructors = [("Nada", []), ("Just1", [("v", TFloat)])]
               , adtDepth = Nothing }]
      []
    -- The same declaration, with a method whose accessor is legal only in the
    -- constructor-tested arm.
    nullaryCtorEnv' q = IREnv
      [IRFunGroup { groupName = "main"
                  , probFun = Just (IRLambda "sample"
                      (IRIf (IRApply (IRVar "isJust1") q)
                            (IRApply (IRVar "v") q) (IRConst (VFloat 0.0))), "")
                  , genFun = Nothing, integFun = Nothing
                  , writeLogitsFun = Nothing, normalFun = Nothing, groupDoc = ""
                  , sampleDomain = Nothing }]
      [ADTDecl { dataName = "Opt"
               , constructors = [("Nada", []), ("Just1", [("v", TFloat)])]
               , adtDepth = Nothing }]
      []
    -- No ADT needed: an Either-typed prob body whose accessor is legal only
    -- under a *let-bound alias* of the structural isLeft(sample) test -- the
    -- exact shape 'IROptimizer's CSE produces (`let cse_0 = (if isLeft(sample)
    -- then True else False) in ...`).
    structuralAliasEnv q = IREnv
      [IRFunGroup { groupName = "main"
                  , probFun = Just (IRLambda "sample"
                      (IRLetIn "cse_0"
                          (IRIf (IRIsLeft q) (IRConst (VBool True)) (IRConst (VBool False)))
                          (IRIf (IRVar "cse_0") (IRFromLeft q) (IRConst (VFloat 0.0)))), "")
                  , genFun = Nothing, integFun = Nothing
                  , writeLogitsFun = Nothing, normalFun = Nothing, groupDoc = ""
                  , sampleDomain = Nothing }]
      [] []
    -- A one-group environment whose only method is generate, with the given
    -- body (either self-referential or not).
    recGenEnv body = IREnv
      [IRFunGroup { groupName = "rec", genFun = Just (body, "")
                  , probFun = Nothing, integFun = Nothing
                  , writeLogitsFun = Nothing, normalFun = Nothing, groupDoc = ""
                  , sampleDomain = Nothing }]
      [] []
    -- 'batchedGuard' is called on the raw term, *not* through 'prepBatchedBody':
    -- these rows check the guard itself, and prepping would rewrite away the very
    -- nodes some of them are about (pruneAny turns an OpIsAny check into a plain
    -- constant, which is legitimately in the fragment).
    assertRefusal needle e = case batchedGuard (adtEnv []) "g" "forward" e of
      Right () -> assertFailure ("batchedGuard accepted a node it must refuse; expected: " ++ needle)
      Left msg -> assertBool ("batched refusal does not mention " ++ show needle
                              ++ "; actual diagnostic: " ++ msg) (needle `isInfixOf` msg)
    assertAccepted e = case batchedGuard (adtEnv []) "g" "forward" e of
      Right () -> return ()
      Left msg -> assertFailure ("batchedGuard refused a node inside the fragment: " ++ msg)

-- ---------------------------------------------------------------------------
-- Decomposability gate: shared enumerated latent (design decomposability-gate-shared-latent)
-- ---------------------------------------------------------------------------

-- | Same pipeline as 'prepTypedFC' (parse, enum tags, RType, modality/pType),
-- minus the FC certificate this gate has no use for.
prepTypedProgSrc :: String -> Program
prepTypedProgSrc = fst . prepTypedFC

prepTypedProgFile :: FilePath -> IO Program
prepTypedProgFile path = prepTypedProgSrc <$> readFile path

-- | The outermost candidate binary-enumerable-InjF verdict found in 'main'
-- (first entry of 'injFLatentVerdicts', which walks pre-order). Every
-- fixture below has exactly one node of interest.
mainOuterVerdict :: Program -> Bool
mainOuterVerdict prog = case lookup "main" (functions prog) of
  Nothing -> error "no main function"
  Just mainExpr -> case injFLatentVerdicts mainExpr of
    ((_, verdict) : _) -> verdict
    []                 -> error "no candidate binary InjF node found in main"

-- ---------------------------------------------------------------------------
-- Cardinality guard for marginal materialization
-- (task materialization-cardinality-guard)
-- ---------------------------------------------------------------------------

-- | The tags of the outermost binary InjF node in 'main', and of its two
-- operands -- the exact three domains the materializer asks the guard about.
mainInjFTags :: Program -> ([Tag], [Tag], [Tag])
mainInjFTags prog = case lookup "main" (functions prog) of
  Nothing -> error "no main function"
  Just mainExpr -> case [ (getTypeInfo e, getTypeInfo l, getTypeInfo r)
                        | e@(Expr _ (InjF _ [l, r])) <- collect mainExpr ] of
    ((ti, lti, rti) : _) -> (tags ti, tags lti, tags rti)
    []                   -> error "no binary InjF node found in main"
  where collect e = e : concatMap collect (getSubExprs e)

-- | The tags of 'main''s body itself (after stripping the parameter lambdas).
mainBodyTags :: Program -> [Tag]
mainBodyTags prog = case lookup "main" (functions prog) of
  Nothing -> error "no main function"
  Just mainExpr -> tags (getTypeInfo (strip mainExpr))
  where strip (Expr _ (Lambda _ b)) = strip b
        strip e = e

materializationGuardTests :: TestTree
materializationGuardTests = testGroup "Cardinality guard for marginal materialization"
  [ testCase "permits mNistAdd: sum domain, both operand domains, and the operand grid" $ do
      prog <- prepTypedProgFile "testCases/mNistAdd.ppl"
      let (nodeTags, leftTags, rightTags) = mainInjFTags prog
          bound = defaultMaterializationCardinality
      case (materializationDomain bound nodeTags,
            materializationDomain bound leftTags,
            materializationDomain bound rightTags) of
        (Just nodeVals, Just leftVals, Just rightVals) -> do
          assertEqual "readMNist(a) ++ readMNist(b) enumerates 0..18" 19 (length nodeVals)
          assertEqual "left digit domain" 10 (length leftVals)
          assertEqual "right digit domain" 10 (length rightVals)
          assertBool "the 10x10 operand grid must be affordable to unroll"
            (withinMaterializationBudget bound (length leftVals * length rightVals))
        other -> assertFailure ("guard refused mNistAdd's domains: " ++ show other)
  , testCase "refuses a deliberately large domain at the default bound" $ do
      -- A real program, annotated by the real enum pass: the declared neural
      -- domain alone is over budget, so its marginal must not be tabulated.
      let big = [0 .. defaultMaterializationCardinality + 1] :: [Int]
          src = "neural readBig :: (Symbol -> Int) of ["
                  ++ intercalate ", " (map show big) ++ "]\nmain a = readBig(a)"
          prog = prepTypedProgSrc src
      assertEqual "domain of 10002 values is over the 10000 budget"
        Nothing (materializationDomain defaultMaterializationCardinality (mainBodyTags prog))
  , testCase "the boundary is pinned, not incidental" $ do
      let atBound  = [DiscreteValues (MultiDiscretes (map (VInt . fromIntegral) [1 .. 10 :: Int]))]
      assertBool "|domain| == bound materializes"
        (materializationDomain 10 atBound /= Nothing)
      assertEqual "|domain| == bound + 1 does not"
        Nothing (materializationDomain 9 atBound)
  , testCase "total: unannotated, continuous and unresolved domains all refuse" $ do
      let bound = defaultMaterializationCardinality
      assertEqual "no DiscreteValues tag at all"
        Nothing (materializationDomain bound [])
      assertEqual "a tag carrying no domain (IsConditional only)"
        Nothing (materializationDomain bound [IsConditional])
      assertEqual "a continuous leaf has no finite enumeration"
        Nothing (materializationDomain bound [DiscreteValues MultiContinuous])
      assertEqual "a partly-continuous tuple enumerates only a discrete residue"
        Nothing (materializationDomain bound
                  [DiscreteValues (MultiTuple (MultiDiscretes [VInt 0]) MultiContinuous)])
      assertEqual "an unresolved auto-placeholder is not a domain"
        Nothing (materializationDomain bound [DiscreteValues MultiAuto])
      assertEqual "an unresolved recursive type reference is not a domain"
        Nothing (materializationDomain bound [DiscreteValues (MultiTypeRef "T")])
      assertEqual "an empty enumeration is not a domain"
        Nothing (materializationDomain bound [DiscreteValues (MultiDiscretes [])])
  , testCase "a non-positive budget is the off-switch" $ do
      prog <- prepTypedProgFile "testCases/mNistAdd.ppl"
      let (nodeTags, _, _) = mainInjFTags prog
      assertEqual "cardinality 0 refuses everything"
        Nothing (materializationDomain 0 nodeTags)
  ]

-- ---------------------------------------------------------------------------
-- Tier 0 marginal materialization (task materialize-discrete-marginals)
-- ---------------------------------------------------------------------------

-- | Materialization off, via the cardinality guard's own off-switch.
noMaterializationConfig :: CompilerConfig
noMaterializationConfig = defaultCompilerConfig { materializationCardinality = 0 }

-- | A literal mock-NN parameter: the digit distribution, padded to the ten
-- logits @readMNist@'s partition plan expects (see MockNN's @(2, [..])@ form).
mockDigits :: [Double] -> IRValue
mockDigits ps = VTuple (VInt 2) (constructVList (map VFloat (take 10 (ps ++ repeat 0.0))))

-- | p(main = sample) of a corpus program under a given config, as a Double.
probUnder :: CompilerConfig -> Program -> [IRValue] -> IRValue -> IO Double
probUnder conf prog params sample = case runProb conf prog params sample of
  Right (VProbDim pr _) -> return pr
  other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- | cdf(main <= sample) of a corpus program under a given config.
cumulUnder :: CompilerConfig -> Program -> [IRValue] -> IRValue -> IO Double
cumulUnder conf prog params sample = case runInteg conf prog params sample of
  Right (VProbDim pr _) -> return pr
  other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- | Does the compiled program contain materialized marginal cells?
compilesWithCells :: CompilerConfig -> Program -> IO Bool
compilesWithCells conf prog = case compile conf prog of
  Left err -> assertFailure ("compilation failed: " ++ show err)
  Right ir -> return ("mat_cell" `isInfixOf` show ir)

digits3, digits4 :: [IRValue]
digits3 = [mockDigits [0.7, 0.3], mockDigits [0.6, 0.4], mockDigits [0.5, 0.5]]
digits4 = digits3 ++ [mockDigits [0.5, 0.5]]

materializationTests :: TestTree
materializationTests = testGroup "Tier 0 marginal materialization"
  [ testCase "fires on a three-term chain, and the guard's off-switch stops it" $ do
      prog <- loadCorpusProgram "mNistAdd3"
      onCells  <- compilesWithCells defaultCompilerConfig prog
      offCells <- compilesWithCells noMaterializationConfig prog
      assertBool "a 3-term chain's left operand must be tabulated" onCells
      assertBool "cardinality 0 must fall back to point-query re-descent" (not offCells)
  , testCase "does NOT fire on a two-term chain: neither operand is nested" $ do
      -- Tabulating the queried node itself would be a pessimization (its point
      -- query costs |D_left|, its table |D_left| * |D_node|), so a flat program's
      -- emitted IR must be untouched -- byte for byte, not just numerically.
      prog <- loadCorpusProgram "mNistAdd"
      cells <- compilesWithCells defaultCompilerConfig prog
      assertBool "a flat two-term add must not be materialized" (not cells)
      case (compile defaultCompilerConfig prog, compile noMaterializationConfig prog) of
        (Right onIR, Right offIR) ->
          assertEqual "two-term add: emitted IR identical with and without materialization"
            (show offIR) (show onIR)
        _ -> assertFailure "compilation failed"
  , testCase "materialized == re-descended, value for value (probability)" $ do
      -- The tables are built by evaluating the InjF forward over the operand
      -- grid, accumulating in the same order the enumeration loop does, so this
      -- is exact equality rather than a tolerance comparison.
      prog3 <- loadCorpusProgram "mNistAdd3"
      prog4 <- loadCorpusProgram "mNistAdd4"
      forM_ [(prog3, digits3, [0 .. 5]), (prog4, digits4, [0 .. 6])] $ \(prog, params, qs) ->
        forM_ qs $ \q -> do
          matP <- probUnder defaultCompilerConfig    prog params (VInt q)
          refP <- probUnder noMaterializationConfig  prog params (VInt q)
          assertEqual ("p(" ++ show q ++ ") must not move") refP matP
  , testCase "materialized == re-descended, value for value (cumulative)" $ do
      prog3 <- loadCorpusProgram "mNistAdd3"
      forM_ [0 .. 4] $ \q -> do
        matC <- cumulUnder defaultCompilerConfig   prog3 digits3 (VInt q)
        refC <- cumulUnder noMaterializationConfig prog3 digits3 (VInt q)
        assertEqual ("cdf(" ++ show q ++ ") must not move") refC matC
  , testCase "topK: materialization prunes exactly what the in-loop cutoff prunes" $ do
      -- The required relationship, stated as a property: table-local pruning
      -- drops no more mass than accProb pruning would. It holds by identity --
      -- accProb is only modified at an IfThenElse, so every level of an enum
      -- chain shares one accProb, and the per-term guard is the same test on
      -- the same value. A threshold that visibly bites (0.15 against digit
      -- masses of 0.7/0.3/0.5) is the interesting case, not a vacuous one.
      prog <- loadCorpusProgram "mNistAdd3"
      forM_ [0.0, 0.15, 0.3] $ \thresh -> do
        let onConf  = defaultCompilerConfig   { topKThreshold = Just thresh }
            offConf = noMaterializationConfig { topKThreshold = Just thresh }
        forM_ [0 .. 4] $ \q -> do
          matP <- probUnder onConf  prog digits3 (VInt q)
          refP <- probUnder offConf prog digits3 (VInt q)
          assertEqual ("topK " ++ show thresh ++ ", p(" ++ show q ++ ")") refP matP
  , testCase "log space: materialized == re-descended" $ do
      prog <- loadCorpusProgram "mNistAdd3"
      forM_ [0 .. 4] $ \q -> do
        matP <- probUnder (defaultCompilerConfig   { logSpace = True }) prog digits3 (VInt q)
        refP <- probUnder (noMaterializationConfig { logSpace = True }) prog digits3 (VInt q)
        assertEqual ("logSpace p(" ++ show q ++ ")") refP matP
  , testCase "branch counting is unaffected by materialization" $ do
      -- The enumeration paths already discard a sub-result's branch count (they
      -- read the probability only), so a tabulated operand must not change the
      -- node's own count either.
      prog <- loadCorpusProgram "mNistAdd3"
      forM_ [0 .. 4] $ \q -> do
        let bcConf' c = c { SPLL.IntermediateRepresentation.countBranches = True }
        matR <- return (runProb (bcConf' defaultCompilerConfig)   prog digits3 (VInt q))
        refR <- return (runProb (bcConf' noMaterializationConfig) prog digits3 (VInt q))
        case (matR, refR) of
          (Right (VProbDimBC mp _ mbc), Right (VProbDimBC rp _ rbc)) -> do
            assertEqual ("p(" ++ show q ++ ") under -c") rp mp
            assertEqual ("branch count at " ++ show q) rbc mbc
          other -> assertFailure ("expected branch-counted tuples, got: " ++ show other)
  ]

-- | p(main = sample) under the given family's extra probability-mode group
-- ("main_map" for 'SRMaxProduct'), as a Double. Mirrors 'probUnder', but reads
-- the extra group 'IRCompiler.hs's 'extraFunGroups' compiles alongside the
-- ordinary one rather than "main" itself -- see 'SPLL.Semiring.semiringSuffix'
-- for the name mapping.
extraProbUnder :: SemiringFamily -> CompilerConfig -> Program -> [IRValue] -> IRValue -> IO Double
extraProbUnder fam conf prog params sample = case compile conf { extraSemirings = [fam] } prog of
  Left err -> assertFailure ("compilation failed: " ++ show err)
  Right ir -> case runProbNamedC prog ir ("main_" ++ semiringSuffix fam) params sample of
    Right (VProbDim pr _) -> return pr
    other -> assertFailure ("expected a probability tuple from the extra group, got: " ++ show other)

-- | Task semiring-parametric-marginals: the max-product (MAP) semiring, which
-- swaps 'prodP'/'mixP'/'enumSumP''s mixture-combine (⊕) from sum/log-sum-exp to
-- max, computing the probability of a query value's single most likely
-- derivation instead of the total over every derivation. Each case below is
-- independently hand-derived (not cross-checked against the compiler's own
-- sum-product output beyond the "single derivation, no divergence expected"
-- sanity checks), and each pins one of the three structurally different sites
-- the mixture-combine reaches -- 'mixWith' (an ordinary 'IfThenElse'),
-- 'enumSumP' via the double-enumeration ("enumerate-both") path, and 'enumSumP'
-- via Tier 0's materialized-marginal convolution ('convolveTables') -- since
-- MAP reuses the identical machinery at each and a bug can be specific to one.
semiringMapTests :: TestTree
semiringMapTests = testGroup "Semiring: max-product (MAP)"
  [ testCase "does not change the ordinary (sum-product) group at all" $ do
      -- extraSemirings is documented purely additive -- requesting the MAP
      -- group alongside the ordinary one must not perturb "main" itself.
      let src = "main = if Uniform < 0.9 then (if Uniform < 0.5 then 2.0 else 3.0) else (if Uniform < 0.1 then 2.0 else 4.0)"
      prog <- case tryParseProgram "<test>" src of
        Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
        Right p  -> return p
      forM_ [2.0, 3.0, 4.0] $ \q -> do
        plain <- probUnder defaultCompilerConfig prog [] (VFloat q)
        withExtra <- probUnder (defaultCompilerConfig { extraSemirings = [SRMaxProduct] }) prog [] (VFloat q)
        assertEqual ("main's own p(" ++ show q ++ ") must be unaffected by extraSemirings") plain withExtra
  , testCase "IfThenElse mixture (mixWith): overlapping derivations, MAP takes the max" $ do
      -- 2.0 is reachable two ways: the 0.9-branch's 0.5-subbranch (0.9*0.5 =
      -- 0.45) and the 0.1-branch's 0.1-subbranch (0.1*0.1 = 0.01). Sum-product
      -- sums them (0.46); MAP is the winning derivation alone (0.45). 3.0 and
      -- 4.0 each have exactly one derivation, so MAP must equal sum-product
      -- there -- the case that would catch an accidentally-always-different MAP.
      let src = "main = if Uniform < 0.9 then (if Uniform < 0.5 then 2.0 else 3.0) else (if Uniform < 0.1 then 2.0 else 4.0)"
      prog <- case tryParseProgram "<test>" src of
        Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
        Right p  -> return p
      p2 <- extraProbUnder SRMaxProduct defaultCompilerConfig prog [] (VFloat 2.0)
      p3 <- extraProbUnder SRMaxProduct defaultCompilerConfig prog [] (VFloat 3.0)
      p4 <- extraProbUnder SRMaxProduct defaultCompilerConfig prog [] (VFloat 4.0)
      assertBool ("p_map(2.0) = 0.45, got " ++ show p2) (abs (p2 - 0.45) < 1e-9)
      assertBool ("p_map(3.0) = 0.45, got " ++ show p3) (abs (p3 - 0.45) < 1e-9)
      assertBool ("p_map(4.0) = 0.09, got " ++ show p4) (abs (p4 - 0.09) < 1e-9)
  , testCase "double-enumeration (enumSumP, applyUnique-uniquified): MAP over both orderings" $ do
      -- testCases/applyEnumOperandPair.ppl's own shape: sel fl ++ sel fl, both
      -- operands the SAME latent, exercised via the enumerate-both path (task
      -- enumerable-injf-operand-loses-tag-across-apply). p(1) sums two ways to
      -- get 1 (fl selects the 0-slot on one side and the 1-slot on the other),
      -- each independently 0.5*0.5 = 0.25 under this path's own (documented)
      -- as-if-independent treatment -- so sum-product's p(1) = 0.5 and MAP's
      -- p(1) = 0.25, the max of the two equal-probability orderings. p(0)/p(2)
      -- have one ordering each, so MAP must match sum-product exactly there --
      -- the regression canary for the 'uniqueify'/'IRLambda' binder bug found
      -- and fixed during this task (a NameError in the emitted Python, not a
      -- wrong number, so this also stands as an "it compiles and runs at all"
      -- check for the code path 'IRBuiltin'-based direct tensor emission for
      -- 'ROpMax' added).
      let src = unlines
            [ "sel x = if x then 1 else 0"
            , "fl = Uniform < 0.5"
            , "main = sel fl ++ sel fl"
            ]
      prog <- case tryParseProgram "<test>" src of
        Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
        Right p  -> return p
      p0sp <- probUnder defaultCompilerConfig prog [] (VInt 0)
      p1sp <- probUnder defaultCompilerConfig prog [] (VInt 1)
      p2sp <- probUnder defaultCompilerConfig prog [] (VInt 2)
      assertBool "sum-product p(0) = 0.25 (corpus expectation)" (abs (p0sp - 0.25) < 1e-9)
      assertBool "sum-product p(1) = 0.5 (corpus expectation)"  (abs (p1sp - 0.5)  < 1e-9)
      assertBool "sum-product p(2) = 0.25 (corpus expectation)" (abs (p2sp - 0.25) < 1e-9)
      p0 <- extraProbUnder SRMaxProduct defaultCompilerConfig prog [] (VInt 0)
      p1 <- extraProbUnder SRMaxProduct defaultCompilerConfig prog [] (VInt 1)
      p2 <- extraProbUnder SRMaxProduct defaultCompilerConfig prog [] (VInt 2)
      assertBool ("p_map(0) = 0.25, got " ++ show p0) (abs (p0 - 0.25) < 1e-9)
      assertBool ("p_map(1) = 0.25, got " ++ show p1) (abs (p1 - 0.25) < 1e-9)
      assertBool ("p_map(2) = 0.25, got " ++ show p2) (abs (p2 - 0.25) < 1e-9)
  , testCase "Tier 0 materialized convolution (convolveTables): MAP over a 3-term independent sum" $ do
      -- sel fl1 + sel fl2 + sel fl3, three INDEPENDENT Bernoulli(0.9/0.5/0.5)
      -- latents summed via a nested enumerable chain -- exactly the shape Tier
      -- 0 tabulates ("fires on a three-term chain" above, mNistAdd3's
      -- non-neural sibling). Hand-derived binomial-type probabilities:
      --   p(0) = 0.1*0.5*0.5 = 0.025                 (one derivation)
      --   p(1) = 0.9*0.5*0.5 + 0.1*0.5*0.5 + 0.1*0.5*0.5 = 0.275 (three)
      --   p(2) = 0.9*0.5*0.5 + 0.9*0.5*0.5 + 0.1*0.5*0.5 = 0.475 (three)
      --   p(3) = 0.9*0.5*0.5 = 0.225                  (one derivation)
      -- MAP takes the max of each value's derivation set: p(0) and p(3) have
      -- only one derivation each (MAP = sum-product there); p(1)'s and p(2)'s
      -- three derivations include one dominant 0.225 term each, strictly below
      -- their sum-product totals -- the case that pins 'IRCompiler.hs's
      -- 'convolveTables' actually reading 'srReduceOp' (it was hardcoded to
      -- ROpAdd/ROpLogSumExp before this task, silently ignoring the active
      -- semiring for every materialized cell).
      let src = unlines
            [ "sel x = if x then 1 else 0"
            , "fl1 = Uniform < 0.9"
            , "fl2 = Uniform < 0.5"
            , "fl3 = Uniform < 0.5"
            , "main = (sel fl1 ++ sel fl2) ++ sel fl3"
            ]
      prog <- case tryParseProgram "<test>" src of
        Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
        Right p  -> return p
      cells <- compilesWithCells defaultCompilerConfig prog
      assertBool "this 3-term independent chain must actually be materialized (Tier 0)" cells
      let expectedSumProduct = [0.025, 0.275, 0.475, 0.225]
          expectedMap        = [0.025, 0.225, 0.225, 0.225]
      forM_ (zip3 [0 :: Int ..] expectedSumProduct expectedMap) $ \(q, esp, emap) -> do
        sp <- probUnder defaultCompilerConfig prog [] (VInt q)
        mp <- extraProbUnder SRMaxProduct defaultCompilerConfig prog [] (VInt q)
        assertBool ("sum-product p(" ++ show q ++ ") = " ++ show esp ++ ", got " ++ show sp)
                   (abs (sp - esp) < 1e-9)
        assertBool ("p_map(" ++ show q ++ ") = " ++ show emap ++ ", got " ++ show mp)
                   (abs (mp - emap) < 1e-9)
  ]

-- | The consumer-grade decomposability walk. Unlike 'injFLatentVerdicts' it
-- binds bare lambda parameters -- see 'materializationVerdicts'.
materializationVerdictTests :: TestTree
materializationVerdictTests = testGroup "Decomposability gate: materialization consumer"
  [ testCase "a nested chain whose operands share a latent is flagged" $ do
      -- The gate's whole job, at the shape a materializer would break: the
      -- OUTER ++ combines two independent things (the inner chain, and w),
      -- while the INNER one's operands are both u and must not be tabulated
      -- separately. The program's other binary InjFs are the two `<` nodes.
      prog <- prepTypedProgFile "testCases/sharedLatentNestedChain.ppl"
      let verdicts = Map.elems (materializationVerdicts prog)
      assertEqual "four binary InjF nodes: 2 comparisons, the outer ++, the inner ++"
        4 (length verdicts)
      assertEqual "exactly one of them -- the inner ++ -- may share a latent"
        1 (length (filter id verdicts))
  , testCase "mNistAdd3/4: every node independent, so every level may be tabulated" $ do
      forM_ ["mNistAdd3", "mNistAdd4"] $ \name -> do
        prog <- prepTypedProgFile ("testCases/" ++ name ++ ".ppl")
        assertBool (name ++ ": digit reads through deterministic symbols are independent")
          (not (or (Map.elems (materializationVerdicts prog))))
  , testCase "a latent threaded through a function parameter is never a candidate" $ do
      -- Inside a callee a parameter is typed Deterministic (it is fixed by the
      -- enumeration the caller compiles to), and Analysis propagates no
      -- DiscreteValues tag through it -- so `x ++ x` in a callee fails
      -- 'isCandidateBinaryEnumInjF' on both counts and never reaches the
      -- materializer. Asserted at the consumer level rather than on the
      -- verdict, because the verdict is not what keeps this node out.
      -- Raw parse, not 'prepTypedProgSrc': 'compile' runs the annotation
      -- pipeline itself, and annotating an already-annotated program doubles
      -- its tags.
      let prog = either (error . show) id
            (tryParseProgram "test"
              ("twice x = x ++ x\n"
               ++ "main = let u = Uniform < 0.3 in twice (if u then 1 else 0)"))
      cells <- compilesWithCells defaultCompilerConfig prog
      assertBool "a parameter-fed chain must not be tabulated" (not cells)
  ]

decomposabilityGateTests :: TestTree
decomposabilityGateTests = testGroup "Decomposability gate: shared enumerated latent"
  [ testCase "canary: letThreadEnumerable's shared u is flagged" $ do
      prog <- prepTypedProgFile "testCases/letThreadEnumerable.ppl"
      assertBool "u used on both sides of ++ must be flagged as shared" (mainOuterVerdict prog)
  , testCase "sharedLatentCallChain: latent crosses a two-level call boundary" $ do
      prog <- prepTypedProgFile "testCases/sharedLatentCallChain.ppl"
      assertBool "shared through the inner/contrib call chain" (mainOuterVerdict prog)
  , testCase "sharedLatentTupleSlot: latent reaches both uses via a tuple slot" $ do
      prog <- prepTypedProgFile "testCases/sharedLatentTupleSlot.ppl"
      assertBool "shared through the (u, 1) tuple argument" (mainOuterVerdict prog)
  , testCase "sharedLatentThreeUses: transitively closed across 3 occurrences" $ do
      prog <- prepTypedProgFile "testCases/sharedLatentThreeUses.ppl"
      assertBool "a pairwise-only check would miss 3-way sharing; must be transitively closed"
        (mainOuterVerdict prog)
  , testCase "sharedLatentNestedLet: dependency threads through a derived let binding" $ do
      prog <- prepTypedProgFile "testCases/sharedLatentNestedLet.ppl"
      assertBool "v = contrib u 1 must still carry u's identity forward" (mainOuterVerdict prog)
  , testCase "sharedLatentOneSideOnly: gate permits genuinely independent operands" $ do
      prog <- prepTypedProgFile "testCases/sharedLatentOneSideOnly.ppl"
      assertBool "u and v are distinct lets; must NOT be flagged as shared"
        (not (mainOuterVerdict prog))
  , testCase "sharedLatentPlusFresh: identical-looking draws bound to distinct lets are independent" $ do
      prog <- prepTypedProgFile "testCases/sharedLatentPlusFresh.ppl"
      assertBool "u and v draw from the same distribution shape but are distinct latents"
        (not (mainOuterVerdict prog))
  , testCase "two independent raw draws with no let are never flagged" $ do
      let prog = prepTypedProgSrc
            "main = (if Uniform < 0.3 then 1 else 0) ++ (if Uniform < 0.3 then 1 else 0)"
      assertBool "two textually-identical but distinct raw draws are independent"
        (not (mainOuterVerdict prog))
  ]

-- design sum-type-showcase: the Level 0-4 showcase corpus pins frozen numbers
-- in its .tst files. Those numbers are only the *right* numbers if the
-- identities the series is meant to demonstrate actually hold, so the
-- identities themselves are checked here rather than left implicit in a
-- decimal expansion.
sumTypeShowcaseTests :: TestTree
sumTypeShowcaseTests = testGroup "sumTypeShowcase"
  [ test_showcasePoeIsProductOfExperts
  , test_showcasePoeThreeSensors
  , test_showcasePoePosteriorRenormalizes
  , test_showcaseConstructorMarginalsSumToOne
  , test_observeContinuousRenormalizes
  ]

-- | Parse a corpus program, failing the test (rather than the whole run) on a
-- parse error.
loadCorpusProgram :: String -> IO Program
loadCorpusProgram baseName = do
  let path = "testCases/" ++ baseName ++ ".ppl"
  src <- readFile path
  case tryParseProgram path src of
    Left err -> assertFailure ("Parse error in " ++ path ++ ": " ++ show err)
    Right p  -> return p

-- | The probability of one query point of a compiled corpus program.
showcaseProb :: Program -> [IRValue] -> IRValue -> IO Double
showcaseProb prog params sample = fst <$> showcaseProbDim prog params sample

-- | 'showcaseProb', keeping the dimension: whether a marginal came back as a
-- discrete mass or as a density is part of what makes it right, and the
-- number alone does not say.
showcaseProbDim :: Program -> [IRValue] -> IRValue -> IO (Double, Double)
showcaseProbDim prog params sample = case runProb defaultCompilerConfig prog params sample of
  Right (VProbDim p d) -> return (p, d)
  other -> assertFailure ("expected a probability tuple, got: " ++ show other)

-- | A mock-network symbol in random-logit mode (see MockNN): the logits depend
-- only on the partition plan and this seed, never on the network's name, so a
-- single one-network reference program stands in for every expert declared
-- with the same @of@ clause.
mockSymbol :: Int -> IRValue
mockSymbol seed = VTuple (VInt 0) (VInt seed)

-- | One expert's class distribution: a bare @main s = expertNN s@ over the
-- same three-class enumeration the showcase PoE programs declare.
expertClassProb :: IO (Int -> Int -> IO Double)
expertClassProb = do
  let src = unlines
        [ "neural expertNN :: (Symbol -> Int) of [0, 1, 2]"
        , "main s = expertNN s" ]
  prog <- case tryParseProgram "expert-reference" src of
    Left err -> assertFailure ("Parse error in the expert reference program: " ++ show err)
    Right p  -> return p
  return (\seed k -> showcaseProb prog [mockSymbol seed] (VInt k))

-- | Level 4: fusing two sensors by observing their agreement is a *product* of
-- experts, not a mixture -- p(Just k) = P_cam(k) * P_depth(k). The evidence
-- Z = p(Just ANY) is that product summed over the support, and the rejected
-- mass p(Nothing) is its complement.
test_showcasePoeIsProductOfExperts :: TestTree
test_showcasePoeIsProductOfExperts = testCase "showcasePoeIsProductOfExperts" $ do
  prog <- loadCorpusProgram "showcase_poe_discrete"
  expert <- expertClassProb
  let params = [mockSymbol 42, mockSymbol 43]
  joints <- mapM (\k -> showcaseProb prog params (VEither (Right (VInt k)))) [0, 1, 2]
  expected <- mapM (\k -> (*) <$> expert 42 k <*> expert 43 k) [0, 1, 2]
  mapM_ (\(k, got, want) ->
          assertBool ("p(Just " ++ show k ++ ") = " ++ show got
                      ++ " is not P_cam(k)*P_depth(k) = " ++ show want)
            (abs (got - want) < 1e-9))
        (zip3 [0 :: Int, 1, 2] joints expected)
  z <- showcaseProb prog params (VEither (Right VAny))
  assertBool ("p(Just ANY) = " ++ show z ++ " is not the sum of the fused masses "
              ++ show (sum joints)) (abs (z - sum joints) < 1e-9)
  nothing <- showcaseProb prog params (VEither (Left VUnit))
  assertBool ("p(Nothing) = " ++ show nothing ++ " and p(Just ANY) = " ++ show z
              ++ " do not sum to one") (abs (nothing + z - 1) < 1e-9)

-- | Level 4, chained: a compound agreement predicate is the userspace spelling
-- of @observeFurther@, and fuses a third expert into the same product.
test_showcasePoeThreeSensors :: TestTree
test_showcasePoeThreeSensors = testCase "showcasePoeThreeSensors" $ do
  prog <- loadCorpusProgram "showcase_poe_three_sensors"
  expert <- expertClassProb
  let params = [mockSymbol 42, mockSymbol 43, mockSymbol 44]
  joints <- mapM (\k -> showcaseProb prog params (VEither (Right (VInt k)))) [0, 1, 2]
  expected <- mapM (\k -> (\a b c -> a * b * c) <$> expert 42 k <*> expert 43 k <*> expert 44 k)
                   [0, 1, 2]
  mapM_ (\(k, got, want) ->
          assertBool ("p(Just " ++ show k ++ ") = " ++ show got
                      ++ " is not the triple product " ++ show want)
            (abs (got - want) < 1e-9))
        (zip3 [0 :: Int, 1, 2] joints expected)

-- | Level 4 with a prior: the fused masses are unnormalized (they are a
-- prior times two likelihoods), and dividing by the evidence p(Just ANY)
-- turns them into a posterior over the support.
test_showcasePoePosteriorRenormalizes :: TestTree
test_showcasePoePosteriorRenormalizes = testCase "showcasePoePosteriorRenormalizes" $ do
  prog <- loadCorpusProgram "showcase_poe_with_prior"
  let params = [mockSymbol 42, mockSymbol 43]
  joints <- mapM (\k -> showcaseProb prog params (VEither (Right (VInt k)))) [0, 1, 2]
  z <- showcaseProb prog params (VEither (Right VAny))
  assertBool ("the evidence " ++ show z ++ " is not a proper subprobability")
    (z > 0 && z < 1)
  let posterior = map (/ z) joints
  assertBool ("the renormalized posterior " ++ show posterior ++ " does not sum to one")
    (abs (sum posterior - 1) < 1e-9)
  nothing <- showcaseProb prog params (VEither (Left VUnit))
  assertBool ("p(Nothing) = " ++ show nothing ++ " and the evidence " ++ show z
              ++ " do not sum to one") (abs (nothing + z - 1) < 1e-9)

-- | Levels 0-3: whatever a sum-typed program does, its two constructor
-- marginals partition the whole mass. This holds for a constant, for a
-- branch, for a neural Either, for continuous inner types (where the point
-- query is a dim-1 density but the marginal is a dim-0 mass), and for the
-- userspace @observe@ idiom -- where it is exactly
-- @p(Nothing) + p(Just ANY) = 1@.
test_showcaseConstructorMarginalsSumToOne :: TestTree
test_showcaseConstructorMarginalsSumToOne = testCase "showcaseConstructorMarginalsSumToOne" $
  mapM_ check
    [ ("showcase_either_const", [])
    , ("showcase_either_branch", [])
    , ("showcase_either_neural", [mockSymbol 42])
    , ("showcase_either_fromLeft", [mockSymbol 42])
    , ("showcase_either_marginal_discrete", [mockSymbol 42])
    , ("showcase_either_marginal_continuous", [])
    , ("showcase_either_marginal_injf", [])
    , ("showcase_observe_trivial", [])
    , ("showcase_observe_discrete_filter", [mockSymbol 42])
    -- Continuous base: the Just marginal is a CDF mass over the truncation
    -- interval, not a density -- see 'test_observeContinuousRenormalizes'.
    , ("showcase_observe_inequality", [])
    ]
  where
    check (name, params) = do
      prog <- loadCorpusProgram name
      l <- showcaseProb prog params (VEither (Left VAny))
      r <- showcaseProb prog params (VEither (Right VAny))
      assertBool (name ++ ": p(Left ANY) = " ++ show l ++ " and p(Right ANY) = " ++ show r
                  ++ " do not sum to one") (abs (l + r - 1) < 1e-9)

-- | Standard normal CDF, same erf identity 'IRInterpreter.irCDF' uses. Shared
-- library, so this is not an independent reimplementation of the *numerics* --
-- it is not meant to be: what 'test_observeContinuousRenormalizes' pins is the
-- STRUCTURE of the denominator (a CDF difference over the observed interval),
-- and the numerics of a single normal CDF are pinned by the corpus elsewhere.
normalCDF :: Double -> Double
normalCDF x = 0.5 * (1 + erf (x / sqrt 2))

-- | On a CONTINUOUS @observe@, @p(Just ANY)@ is the denominator that
-- normalizes the kept arm (task set-witness-any-in-constructor-slot). For
-- @let v = Normal in if v in I then right v else left ()@ the identity is
--
-- >   p(Right x) / p(Right ANY)  ==  phi(x) / (Phi(hi) - Phi(lo))    for x in I
--
-- i.e. exactly the truncated-Normal density on @I@ -- for the one-sided
-- program, @2*phi(x)*1[x>0]@.
--
-- Kept as a direct HUnit assertion rather than as more .tst rows because the
-- harness checks each query point in isolation, whereas the content here is
-- the RELATION between two of them: a dim-1 density divided by a dim-0 mass.
-- The dimensions are asserted too, since that is what separates the three ways
-- the wildcard could have been handled -- dropping the point constraint and
-- keeping the interval (dim 0, correct), keeping the point (dim 1, what the
-- crash was reaching for), or marginalising the whole observation away
-- (dim 0 but mass 1, the full-ANY short-circuit's answer).
--
-- The two-sided program earns its place by having a denominator that is a CDF
-- *difference*: the one-sided 0.5 is also what several wrong answers produce.
test_observeContinuousRenormalizes :: TestTree
test_observeContinuousRenormalizes = testCase "observeContinuousRenormalizes" $
  mapM_ check
    [ ("showcase_observe_inequality", 0.0, 1 / 0, [0.25, 1.0, 2.0], [-0.25, -3.0])
    , ("observeTwoSidedInterval",     0.0, 1.0,   [0.25, 0.5, 0.75], [-0.25, 1.5])
    ]
  where
    stdNormalPdf x = exp (negate (x * x) / 2) / sqrt (2 * pi)
    check (name, lo, hi, inside, outside) = do
      prog <- loadCorpusProgram name
      (z, zDim) <- showcaseProbDim prog [] (VEither (Right VAny))
      let expectedZ = normalCDF hi - normalCDF lo
      assertBool (name ++ ": p(Just ANY) = " ++ show z ++ ", expected the interval mass "
                   ++ show expectedZ) (abs (z - expectedZ) < 1e-9)
      assertEqual (name ++ ": p(Just ANY) must be a discrete mass, not a density") 0.0 zDim
      forM_ inside $ \x -> do
        (px, pxDim) <- showcaseProbDim prog [] (VEither (Right (VFloat x)))
        assertEqual (name ++ ": p(Just " ++ show x ++ ") must stay a density") 1.0 pxDim
        assertBool (name ++ ": p(Just " ++ show x ++ ")/p(Just ANY) = " ++ show (px / z)
                     ++ " is not the truncated density " ++ show (stdNormalPdf x / expectedZ))
                   (abs (px / z - stdNormalPdf x / expectedZ) < 1e-9)
      forM_ outside $ \x -> do
        (px, _) <- showcaseProbDim prog [] (VEither (Right (VFloat x)))
        assertEqual (name ++ ": p(Just " ++ show x ++ ") outside the observed interval") 0.0 px

internalsTests :: TestTree
internalsTests = testGroup "Internals"
  [ testProperties "properties" $(allProperties)
  , testGroup "tensor builtins" tensorBuiltinTests
  , classConstraintTests
  , forwardChainingCertTests
  , witnessedBindingTests
  , anyRefusalTests
  , testGroup "writeLogits"
      [ test_writeLogitsTupleGaussianParams
      , test_writeLogitsDiscreteSumsToOne
      , test_writeLogitsGaussianSigmaPositive
      , test_writeLogitsUsesStandaloneRegistration
      , test_writeLogitsMainAutoDerivedBool
      , test_writeLogitsMainIntViaRegistry
      , test_writeLogitsMainNotRepresentable
      , test_writeLogitsMainAndReadLogitsShareType
      , test_writeLogitsAuxEither
      , test_writeLogitsRoundtripNoop
      , test_writeLogitsBoolExactProbs
      , test_nnHoistedOutOfEnumSum
      ]
  , test_missingMainFunction
  , test_farTailEitherDensityNotZeroed
  , test_underflowedTailKeepsDimension
  , test_structurallyImpossibleSampleIsFlagged
  , test_observeRenormalizesViaJustAny
  , test_uniformOffSupportIsImpossible
  , test_injFImageIsImpossible
  , test_letBoundEitherDestructureUsesSample
  , test_setWitnessMergesComplementaryTupleFields
  , autoNeuralDerivationTests
  , enumContinuousRefusalTests
  , test_planEnumThreadedTopKAndBC
  , test_branchCountingDoesNotMultiplyIR
  , test_recursiveListMissedCSE
  , test_planEnumBoolCtorPolynomial
  , planOverCouplingRefusalTests
  , test_tstBackendsHeader
  , optimizerPurityTests
  , stochasticCallTests
  , batchedRefusalUnitTests
  , decomposabilityGateTests
  , materializationGuardTests
  , materializationTests
  , semiringMapTests
  , materializationVerdictTests
  , planEnumStructuralADTTests
  , planEnumStructuralPartialTests
  , sumTypeShowcaseTests
  ]

-- | Tests heavy enough (multiple full compiles of a depth-3/depth-10+ plan
-- enumeration program) to noticeably slow day-to-day `stack test`, and
-- unlikely to catch regressions outside plan-guided-lazy-enumeration work.
-- Opt in with NEST_SLOW_TESTS=1 (see Spec.hs's Slow group).
--
-- 'test_planEnumM4Polynomial' (depth 30), 'test_planEnumFusedJointStatePolynomial'
-- (depth-6 fused automaton) and 'test_planEnumStructuralGrouped' (depth-5
-- structural inversion) moved here from the fast 'internalsTests' group: each
-- pins asymptotic IR-size behaviour of an already-shipped milestone rather than
-- day-to-day compiler surface, and together they cost ~70s of the ~114s a plain
-- `stack test` used to take. 'test_planEnumBoolCtorPolynomial' stays in the fast
-- group -- its depth pair (8/12) was deliberately chosen to fail in about a
-- minute rather than OOM (see its own comment), and it is cheap (well under 1s).
slowInternalsTests :: TestTree
slowInternalsTests = testGroup "Internals (slow)"
  [ test_planEnumRecTopKAndBC
  , test_planEnumM4Polynomial
  , test_planEnumFusedJointStatePolynomial
  , test_planEnumStructuralGrouped
  ]

-- ===========================================================================
-- Tensor builtins: the general-rank interpreter semantics (ir-tensor-values)
-- ===========================================================================

-- The compiler only ever builds rank-1 tensors today (an enumeration is one
-- axis), and every backend emits rank 1 only. The interpreter, as the reference
-- semantics, implements the general rank -- so these are what keep that code
-- live and pin the layout convention the rest of the compiler is written
-- against. Without them the stride arithmetic would be unreachable code.

-- | Evaluate a closed IR expression with no neural networks or globals.
evalClosedIR :: IRExpr -> Either String IRValue
evalClosedIR = generateDet [] [] (IREnv [] [] []) []

vfs :: [Double] -> [IRValue]
vfs = map VFloat

-- | A rank-2 tensor is flat and row-major, outermost axis first: shape [2,3]
-- over 1..6 means row 0 is [1,2,3]. Reducing axis 0 adds down the columns,
-- reducing axis 1 adds along the rows -- and the two disagree, which is the
-- point of pinning it.
test_tensorRank2Reduce :: TestTree
test_tensorRank2Reduce = testCase "tensorRank2Reduce" $ do
  let t = IRBuiltin (BTensor [EFixed 2, EFixed 3]) (map (IRConst . VFloat) [1,2,3,4,5,6])
  evalClosedIR (IRBuiltin (BReduce ROpAdd 0) [t])
    @?= Right (VTensor [EFixed 3] (vfs [5, 7, 9]))
  evalClosedIR (IRBuiltin (BReduce ROpAdd 1) [t])
    @?= Right (VTensor [EFixed 2] (vfs [6, 15]))

-- | Reducing the last remaining axis yields a scalar, not a rank-0 tensor:
-- rank 0 is not an inhabited shape (design tensors-in-core-language §2.3).
test_tensorReduceToScalar :: TestTree
test_tensorReduceToScalar = testCase "tensorReduceToScalar" $ do
  let t = IRBuiltin (BTensor [EFixed 3]) (map (IRConst . VFloat) [1,2,3])
  evalClosedIR (IRBuiltin (BReduce ROpAdd 0) [t]) @?= Right (VFloat 6)
  let t2 = IRBuiltin (BTensor [EFixed 2, EFixed 2]) (map (IRConst . VFloat) [1,2,3,4])
  evalClosedIR (IRBuiltin (BReduce ROpAdd 0) [IRBuiltin (BReduce ROpAdd 1) [t2]])
    @?= Right (VFloat 10)

-- | Indexing drops the indexed axis, and which axis it drops matters.
test_tensorRank2Index :: TestTree
test_tensorRank2Index = testCase "tensorRank2Index" $ do
  let t = IRBuiltin (BTensor [EFixed 2, EFixed 3]) (map (IRConst . VFloat) [1,2,3,4,5,6])
  -- row 1
  evalClosedIR (IRBuiltin (BIndex 0) [t, IRConst (VInt 1)])
    @?= Right (VTensor [EFixed 3] (vfs [4, 5, 6]))
  -- column 2
  evalClosedIR (IRBuiltin (BIndex 1) [t, IRConst (VInt 2)])
    @?= Right (VTensor [EFixed 2] (vfs [3, 6]))
  -- a rank-1 index is a scalar
  let t1 = IRBuiltin (BTensor [EFixed 3]) (map (IRConst . VFloat) [7,8,9])
  evalClosedIR (IRBuiltin (BIndex 0) [t1, IRConst (VInt 2)]) @?= Right (VFloat 9)

-- | A map preserves shape and touches every element, at any rank.
test_tensorMapPreservesShape :: TestTree
test_tensorMapPreservesShape = testCase "tensorMapPreservesShape" $ do
  let t = IRBuiltin (BTensor [EFixed 2, EFixed 2]) (map (IRConst . VFloat) [1,2,3,4])
      doubled = IRBuiltin BMap
        [IRLambda "x" (IROp OpMult (IRVar "x") (IRConst (VFloat 2))), t]
  evalClosedIR doubled @?= Right (VTensor [EFixed 2, EFixed 2] (vfs [2, 4, 6, 8]))

-- | log-sum-exp reduces with the right identity, and absorbs the log-space
-- zero (-inf) rather than producing a NaN through exp(-inf - -inf).
test_tensorLogSumExpZero :: TestTree
test_tensorLogSumExpZero = testCase "tensorLogSumExpZero" $ do
  let t = IRBuiltin (BTensor [EFixed 2])
            [IRConst (VFloat (-1/0)), IRConst (VFloat (-1/0))]
  evalClosedIR (IRBuiltin (BReduce ROpLogSumExp 0) [t]) @?= Right (VFloat (-1/0))
  let t2 = IRBuiltin (BTensor [EFixed 2]) [IRConst (VFloat (-1/0)), IRConst (VFloat 0)]
  evalClosedIR (IRBuiltin (BReduce ROpLogSumExp 0) [t2]) @?= Right (VFloat 0)

-- | An empty axis reduces to the operator's identity rather than failing.
test_tensorEmptyReduce :: TestTree
test_tensorEmptyReduce = testCase "tensorEmptyReduce" $ do
  let t = IRBuiltin (BTensor [EFixed 0]) []
  evalClosedIR (IRBuiltin (BReduce ROpAdd 0) [t]) @?= Right (VFloat 0)
  evalClosedIR (IRBuiltin (BReduce ROpLogSumExp 0) [t]) @?= Right (VFloat (-1/0))

tensorBuiltinTests :: [TestTree]
tensorBuiltinTests =
  [ test_tensorRank2Reduce
  , test_tensorReduceToScalar
  , test_tensorRank2Index
  , test_tensorMapPreservesShape
  , test_tensorLogSumExpZero
  , test_tensorEmptyReduce
  ]
