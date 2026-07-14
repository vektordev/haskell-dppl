{-# LANGUAGE TemplateHaskell #-}

module TestInternals (
  internalsTests
) where

import SPLL.Lang.Lang
import SPLL.Lang.Types

import ArbitrarySPLL

import Test.QuickCheck
import SPLL.Typing.RInfer (tryAddRTypeInfo, RTypeError(..))
import SPLL.Typing.RType (ClassConstraint(..), TVarR(..), RType(..))
import SPLL.Prelude
import SPLL.Parser (tryParseProgram)
import SPLL.Analysis (annotateEnumsProg)
import SPLL.Typing.Infer (addTypeInfo)
import SPLL.Typing.ForwardChaining (FCData, annotateProg, progToFCData, isInvertibleLambda, isWitnessedLambda)
import qualified Data.Set as Set
import SPLL.AutoNeural (PartitionPlan(..), makePartitionPlan)
import qualified SPLL.AutoNeural as AutoNeural (getSize)
import SPLL.IntermediateRepresentation
import IRInterpreter (generateDet)
import Data.Foldable (toList)
import Data.List (isInfixOf)
import Control.Exception (try, evaluate, ErrorCall(..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertEqual, assertFailure)
import TestCaseParser (Backend(..), allBackends, parseTestCasesFromString)
import Test.Tasty.QuickCheck (testProperties)
import System.Random (StdGen)
import Control.Monad.Random (Rand)


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
-- parameters.  The encoder is expected to recover those parameters directly from the
-- compiled SPLL distribution rather than reading the raw NN logit-vector slots.
--
-- Expected encode output: [mu1, sigma1, mu2, sigma2] = [2.0, 1.5, -1.0, 0.5]
-- regardless of which sample is passed in.
--
-- makeEncodeTopLevel handles TuplePlan by delegating each Continuous sub-plan to
-- the per-component normal function (main_normal_fst / main_normal_snd), which
-- returns (mu, sigma) derived from the compiled SPLL program rather than the raw
-- NN logit vector.
test_encodeTupleGaussianParams :: TestTree
test_encodeTupleGaussianParams = testCase "encodeTupleGaussianParams" $ do
  let src = unlines
        [ "neural tupleNN :: (Symbol -> (Float, Float))"
        , "main = (1.5 * Normal + 2.0, 0.5 * Normal + (-1.0))"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  -- Closed-form program: no outer params, so runEncode takes an empty arg list.
  -- The encode lives on main (the value producer), derived from its (Float, Float) output.
  case runEncode defaultCompilerConfig prog "main" [] of
    Left err -> assertFailure ("runEncode failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
      assertEqual "encode length" 4 (length items)
      -- The encoder must recover the actual distribution parameters,
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

-- Property: for a discrete-output program, the encode output (probability vector) should
-- sum to approximately 1.0 for any mock NN sym input.
-- Tests with the discrete nonidentity program: main sym = if discreteNN sym == 0 then 2 else 0
-- Output type Int with values [0,1,2], so encode returns [P(0), P(1), P(2)] which must sum to 1.
test_encodeDiscreteSumsToOne :: TestTree
test_encodeDiscreteSumsToOne = testCase "encodeDiscreteSumsToOne" $ do
  let src = unlines
        [ "neural discreteNN :: (Symbol -> Int) of [0, 1, 2]"
        , "main sym = if discreteNN sym == 0 then 2 else 0"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  -- Try several different mock syms; each should give a prob vector summing to 1.
  let mockSyms = [ VTuple (VInt 0) (VInt s) | s <- [0, 1, 42, 100, 999] ]
  mapM_ (\sym -> case runEncode defaultCompilerConfig prog "main" [sym] of
    Left err -> assertFailure ("runEncode failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
          total = sum [ x | VFloat x <- items ]
      assertBool ("encode probs should sum to ~1.0, got " ++ show total)
                 (abs (total - 1.0) < 1.0e-4)
    Right other -> assertFailure ("expected VList, got: " ++ show other)
    ) mockSyms

-- Property: for the Gaussian identity program, encode always returns exactly 2 elements
-- and sigma > 0, regardless of mock sym.
test_encodeGaussianSigmaPositive :: TestTree
test_encodeGaussianSigmaPositive = testCase "encodeGaussianSigmaPositive" $ do
  let src = unlines
        [ "neural gaussNN :: (Symbol -> Float)"
        , "main sym = gaussNN sym"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let mockSyms = [ VTuple (VInt 0) (VInt s) | s <- [0, 1, 7, 42] ]
  mapM_ (\sym -> case runEncode defaultCompilerConfig prog "main" [sym] of
    Left err -> assertFailure ("runEncode failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
      assertEqual "encode length for Gaussian" 2 (length items)
      case items of
        [_, VFloat sigma] ->
          assertBool ("sigma should be positive, got " ++ show sigma) (sigma > 0)
        _ -> assertFailure ("expected [mu, sigma], got: " ++ show items)
    Right other -> assertFailure ("expected VList, got: " ++ show other)
    ) mockSyms

-- A standalone "neural encode :: Int of [...]" declaration registers a PartitionPlan
-- annotation for Int without declaring any callable network. main's Int output picks up
-- that registry entry, so main's own encode group produces the registered number of slots
-- (3) even though Int is not auto-derivable on its own.
test_encodeUsesStandaloneRegistration :: TestTree
test_encodeUsesStandaloneRegistration = testCase "encodeUsesStandaloneRegistration" $ do
  let src = unlines
        [ "neural encode :: Int of [0, 1, 2]"
        , "neural decA :: (Symbol -> Int)"
        , "main sym = decA sym"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let sym = VTuple (VInt 0) (VInt 42)
  case runEncode defaultCompilerConfig prog "main" [sym] of
    Left err          -> assertFailure ("runEncode main failed: " ++ err)
    Right (VList lst) -> assertEqual "main encode length" 3 (length (toList lst))
    Right other       -> assertFailure ("expected VList, got: " ++ show other)

-- A program with no neural declarations at all, whose main has an auto-derivable output
-- type (Bool), still gets an encodeFun on its own "main" group (task
-- encode-main-auto-derived). The encode is a probability vector over [True, False],
-- queried from main_prob, so it must sum to ~1.0.
test_encodeMainAutoDerivedBool :: TestTree
test_encodeMainAutoDerivedBool = testCase "encodeMainAutoDerivedBool" $ do
  let src = unlines
        [ "main = if Uniform < 0.3 then True else False"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  case runEncode defaultCompilerConfig prog "main" [] of
    Left err -> assertFailure ("runEncode main failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
          total = sum [ x | VFloat x <- items ]
      assertEqual "encode length over [True, False]" 2 (length items)
      assertBool ("encode probs should sum to ~1.0, got " ++ show total)
                 (abs (total - 1.0) < 1.0e-4)
    Right other -> assertFailure ("expected VList, got: " ++ show other)

-- Registry-first: main's Int output is not auto-derivable, but the decoder's "of [0,1,2]"
-- registers a PartitionPlan for Int into encodeDecls (the of-clause sugar). So main's own
-- group gets an encodeFun, sliced by that registry entry (length 3) — the registry ∪
-- auto-derive rule from the parent design (encode-partitionplan-decoupling). The decoder
-- group itself hosts no encode (it is an NN1 reader).
test_encodeMainIntViaRegistry :: TestTree
test_encodeMainIntViaRegistry = testCase "encodeMainIntViaRegistry" $ do
  let src = unlines
        [ "neural decA :: (Symbol -> Int) of [0, 1, 2]"
        , "main sym = decA sym"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let sym = VTuple (VInt 0) (VInt 42)
      encodeLen target = case runEncode defaultCompilerConfig prog target [sym] of
        Left err          -> assertFailure ("runEncode " ++ target ++ " failed: " ++ err) >> return (-1)
        Right (VList lst) -> return (length (toList lst))
        Right other       -> assertFailure ("expected VList, got: " ++ show other) >> return (-1)
  lenMain <- encodeLen "main"
  assertEqual "main encode length (registry Int)" 3 lenMain
  -- The decoder group is an NN1 reader and hosts no encode.
  case runEncode defaultCompilerConfig prog "decA_auto" [sym] of
    Left _  -> return ()
    Right v -> assertFailure ("decA_auto should host no encode, got: " ++ show v)

-- A program with no neural declarations whose main has a type that is neither
-- auto-derivable nor in the registry (a list) gets NO encodeFun — the addition is purely
-- additive and degrades to a clean "no encode function" error rather than crashing.
test_encodeMainNotRepresentable :: TestTree
test_encodeMainNotRepresentable = testCase "encodeMainNotRepresentable" $ do
  let src = unlines
        [ "main = (Normal : (Normal : []))"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  case runEncode defaultCompilerConfig prog "main" [] of
    Left err -> assertBool ("error should mention main has no encode function, got: " ++ err)
                           ("main" `isInfixOf` err)
    Right v  -> assertFailure ("expected main to have no encodeFun, got: " ++ show v)

-- main's output type is auto-derivable (Bool); main carries its own encodeFun even when a
-- decoder declaration shares that type. The decoder group itself hosts no encode (it is an
-- NN1 reader), so only "main" is addressable for encode.
test_encodeMainAndDecoderShareType :: TestTree
test_encodeMainAndDecoderShareType = testCase "encodeMainAndDecoderShareType" $ do
  let src = unlines
        [ "neural decB :: (Symbol -> Bool)"
        , "main sym = if decB sym then True else False"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let sym = VTuple (VInt 0) (VInt 42)
  case runEncode defaultCompilerConfig prog "main" [sym] of
    Left err          -> assertFailure ("runEncode main failed: " ++ err)
    Right (VList lst) -> assertEqual "main encode length over [True, False]" 2 (length (toList lst))
    Right other       -> assertFailure ("expected VList, got: " ++ show other)
  -- The decoder group is an NN1 reader and hosts no encode.
  case runEncode defaultCompilerConfig prog "decB_auto" [sym] of
    Left _  -> return ()
    Right v -> assertFailure ("decB_auto should host no encode, got: " ++ show v)

-- An *auxiliary* (non-main) function with sum-type output gets a correct, non-stub Either
-- encode via its OWN prob function (classify_prob) — proving the old null-probFnName stub
-- arms are gone (they emitted all-zero vectors). The flag slot is a real P(Left) = P(cond).
-- (task encode-per-function-endpoints, encode_aux_either)
test_encodeAuxEither :: TestTree
test_encodeAuxEither = testCase "encodeAuxEither" $ do
  let src = unlines
        [ "neural encode :: Either Int Bool of ([0] | _)"
        , "classify s = if Uniform < s then left 0 else right True"
        , "main s = classify s"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  case runEncode defaultCompilerConfig prog "classify" [VFloat 0.4] of
    Left err -> assertFailure ("runEncode classify failed: " ++ err)
    Right (VList lst) -> do
      let items = toList lst
      assertEqual "Either encode length (flag + Int[0] + Bool[True,False])" 4 (length items)
      case items of
        (VFloat flag : _) -> do
          assertBool ("flag should be a real P(Left) ~= 0.4, not a zero stub, got " ++ show flag)
                     (abs (flag - 0.4) < 1.0e-3)
        _ -> assertFailure ("expected a VFloat flag slot, got: " ++ show items)
    Right other -> assertFailure ("expected VList, got: " ++ show other)

-- encode(decode(L)) ≈ normalise(L): for an identity `main sym = nnB sym` over a Bool decoder,
-- encode reproduces the (normalised) decoder distribution. Spiking the mock NN toward a value
-- shifts the encoded distribution toward that value, and the slots always sum to 1 — i.e.
-- decoding then re-encoding is a no-op on the normalised logit vector. (encode_roundtrip_noop)
test_encodeRoundtripNoop :: TestTree
test_encodeRoundtripNoop = testCase "encodeRoundtripNoop" $ do
  let src = unlines
        [ "neural nnB :: (Symbol -> Bool)"
        , "main sym = nnB sym"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let spike v = VTuple (VInt 1) (VTuple v (VInt 0))
      encSlots sym = case runEncode defaultCompilerConfig prog "main" [sym] of
        Left err          -> assertFailure ("runEncode main failed: " ++ err) >> return []
        Right (VList lst) -> return [ x | VFloat x <- toList lst ]
        Right other       -> assertFailure ("expected VList, got: " ++ show other) >> return []
  slotsTrue  <- encSlots (spike (VBool True))
  slotsFalse <- encSlots (spike (VBool False))
  assertEqual "Bool encode length" 2 (length slotsTrue)
  assertBool ("True-spiked slots should sum to ~1, got " ++ show slotsTrue)
             (abs (sum slotsTrue - 1.0) < 1.0e-4)
  assertBool ("False-spiked slots should sum to ~1, got " ++ show slotsFalse)
             (abs (sum slotsFalse - 1.0) < 1.0e-4)
  assertBool ("decode→encode should track the input: True-spiked P(True) > 0.5, got " ++ show (head slotsTrue))
             (head slotsTrue > 0.5)
  assertBool ("decode→encode should track the input: False-spiked P(True) < 0.5, got " ++ show (head slotsFalse))
             (head slotsFalse < 0.5)

-- Sibling positive case to the encoder-decl rejection (TestRejection/encoderDecl): with the
-- (Bool -> Symbol) encoder declaration gone, Bool auto-derives and main's own encode yields
-- the exact [P(True), P(False)] vector — confirming the registration job survives via honest
-- syntax / auto-derivation.
test_encodeBoolExactProbs :: TestTree
test_encodeBoolExactProbs = testCase "encodeBoolExactProbs" $ do
  let src = "main = if Uniform < 0.4 then True else False"
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  case runEncode defaultCompilerConfig prog "main" [] of
    Left err -> assertFailure ("runEncode main failed: " ++ err)
    Right (VList lst) -> case [ x | VFloat x <- toList lst ] of
      [pT, pF] -> do
        assertBool ("P(True) should be ~0.4, got " ++ show pT) (abs (pT - 0.4) < 1.0e-4)
        assertBool ("P(False) should be ~0.6, got " ++ show pF) (abs (pF - 0.6) < 1.0e-4)
      other -> assertFailure ("expected [P(True), P(False)], got: " ++ show other)
    Right other -> assertFailure ("expected VList, got: " ++ show other)

-- | True if `name` is directly applied (IRApply (IRVar name) _) anywhere inside
-- an IREnumSum body.  Used to check that NN forward calls are hoisted out of loops.
nnCallInsideEnumSum :: String -> IRExpr -> Bool
nnCallInsideEnumSum name (IREnumSum _ _ body) = containsDirectNNApply name body
nnCallInsideEnumSum name expr = any (nnCallInsideEnumSum name) (getIRSubExprs expr)

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
          let Just (probExpr, _) = probFun (lookupIREnv "main" irEnv)
          assertBool "readMNist forward call should be hoisted outside IREnumSum" $
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
-- cases to a subset of the three End2End backends; no header means all three.
test_tstBackendsHeader :: TestTree
test_tstBackendsHeader = testCase "tstBackendsHeader" $ do
  let parse = parseTestCasesFromString "header.tst"
  case parse "p(0.5)=(1.0, 1.0)\n" of
    Left err -> assertFailure err
    Right (bs, tcs) -> do
      assertEqual "no header defaults to all backends" allBackends bs
      assertEqual "test case count without header" 1 (length tcs)
  case parse "backends: interpreter\np(0.5)=(1.0, 1.0)\n" of
    Left err -> assertFailure err
    Right (bs, tcs) -> do
      assertEqual "interpreter-only routing" [Interpreter] bs
      assertEqual "test case count with header" 1 (length tcs)
  case parse "backends: julia, python\ncdf(0.5)=(0.5, 0.0)\n" of
    Left err -> assertFailure err
    Right (bs, _) -> assertEqual "two-backend routing" [Julia, Python] bs

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
applyLeftCN prog = head [ chainName (getTypeInfo l) | Apply _ l _ <- allNodes prog ]

constNodeCN :: Program -> ChainName
constNodeCN prog = head [ chainName (getTypeInfo c) | c@(Constant _ _) <- allNodes prog ]

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
  head [ chainName (getTypeInfo l) | l@(Lambda _ n _) <- allNodes prog, n == v ]

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
expectMarginalRefusal src sample var = do
  let prog = either (\e -> error ("parse failed: " ++ show e)) id (tryParseProgram "test" src)
  r <- try (case runProb defaultCompilerConfig prog [] sample of
              Left cerr -> return (Left cerr)
              Right v   -> evaluate (length (show v)) >> return (Right v))
  case r of
    Left (ErrorCall msg) -> do
      assertBool ("expected the marginal-refusal diagnostic, got: " ++ msg)
        ("cannot compute marginal" `isInfixOf` msg)
      assertBool ("diagnostic should name the binding '" ++ var ++ "', got: " ++ msg)
        (("'" ++ var ++ "'") `isInfixOf` msg)
    Right (Left cerr) -> assertFailure ("expected runtime refusal, got compile error: " ++ show cerr)
    Right (Right v) -> assertFailure ("expected runtime refusal, got value: " ++ show v)

internalsTests :: TestTree
internalsTests = testGroup "Internals"
  [ testProperties "properties" $(allProperties)
  , classConstraintTests
  , forwardChainingCertTests
  , witnessedBindingTests
  , anyRefusalTests
  , testGroup "encode"
      [ test_encodeTupleGaussianParams
      , test_encodeDiscreteSumsToOne
      , test_encodeGaussianSigmaPositive
      , test_encodeUsesStandaloneRegistration
      , test_encodeMainAutoDerivedBool
      , test_encodeMainIntViaRegistry
      , test_encodeMainNotRepresentable
      , test_encodeMainAndDecoderShareType
      , test_encodeAuxEither
      , test_encodeRoundtripNoop
      , test_encodeBoolExactProbs
      , test_nnHoistedOutOfEnumSum
      ]
  , test_missingMainFunction
  , autoNeuralDerivationTests
  , test_tstBackendsHeader
  ]
