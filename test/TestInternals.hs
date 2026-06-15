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
import SPLL.AutoNeural (PartitionPlan(..), makePartitionPlan)
import qualified SPLL.AutoNeural as AutoNeural (getSize)
import SPLL.IntermediateRepresentation
import IRInterpreter (generateDet)
import Data.Foldable (toList)
import Data.List (isInfixOf)
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
  case runEncode defaultCompilerConfig prog "tupleNN_auto" [] of
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
  mapM_ (\sym -> case runEncode defaultCompilerConfig prog "discreteNN_auto" [sym] of
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
  mapM_ (\sym -> case runEncode defaultCompilerConfig prog "gaussNN_auto" [sym] of
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

-- A program with two decoder declarations gives two encode groups, decA_auto and
-- decB_auto, both scoped to the same target type (Int). decA's "of [0,1,2]" registers
-- a PartitionPlan annotation for Int (via the of-clause sugar registry, see
-- SPLL.Lang.Types.encodeDecls); decB has no "of" clause of its own, so it picks up
-- that same registry entry. runEncode addresses each group independently by name,
-- and both produce 3-slot encodes since they share one PartitionPlan for Int.
test_encodeTwoDecodersByName :: TestTree
test_encodeTwoDecodersByName = testCase "encodeTwoDecodersByName" $ do
  let src = unlines
        [ "neural decA :: (Symbol -> Int) of [0, 1, 2]"
        , "neural decB :: (Symbol -> Int)"
        , "main sym = if decB sym == 0 then decA sym else 0"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let sym = VTuple (VInt 0) (VInt 42)
      encodeLen target = case runEncode defaultCompilerConfig prog target [sym] of
        Left err          -> assertFailure ("runEncode " ++ target ++ " failed: " ++ err) >> return (-1)
        Right (VList lst) -> return (length (toList lst))
        Right other       -> assertFailure ("expected VList, got: " ++ show other) >> return (-1)
  lenA <- encodeLen "decA_auto"
  lenB <- encodeLen "decB_auto"
  assertEqual "decA_auto encode length" 3 lenA
  assertEqual "decB_auto encode length" 3 lenB

-- A standalone "neural encode :: Int of [...]" declaration registers a PartitionPlan
-- annotation for Int without declaring any callable network. A decoder targeting Int
-- with no "of" clause of its own picks up that registry entry, so its encode group
-- still produces the registered number of slots.
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
  case runEncode defaultCompilerConfig prog "decA_auto" [sym] of
    Left err          -> assertFailure ("runEncode decA_auto failed: " ++ err)
    Right (VList lst) -> assertEqual "decA_auto encode length" 3 (length (toList lst))
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
-- group DOES get an encodeFun, sliced by that registry entry (length 3) — the registry ∪
-- auto-derive rule from the parent design (encode-partitionplan-decoupling). The decoder's
-- own <decl>_auto group is independently addressable and unaffected.
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
  lenDecA <- encodeLen "decA_auto"
  assertEqual "main encode length (registry Int)" 3 lenMain
  assertEqual "decA_auto encode length" 3 lenDecA

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

-- When main's output type is auto-derivable (Bool) AND a decoder declaration shares that
-- type, both groups carry an independently-correct encodeFun, each retrievable by name:
-- "main" (main's own output) and "decB_auto" (the decoder's). Both are 2-slot Bool plans.
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
      encodeLen target = case runEncode defaultCompilerConfig prog target [sym] of
        Left err          -> assertFailure ("runEncode " ++ target ++ " failed: " ++ err) >> return (-1)
        Right (VList lst) -> return (length (toList lst))
        Right other       -> assertFailure ("expected VList, got: " ++ show other) >> return (-1)
  lenMain <- encodeLen "main"
  lenDecB <- encodeLen "decB_auto"
  assertEqual "main encode length over [True, False]" 2 lenMain
  assertEqual "decB_auto encode length over [True, False]" 2 lenDecB

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
colorADT = ADTDecl "Color" [("Red", []), ("Green", []), ("Blue", [])]

test_autoDeriveNonRecursiveADT :: TestTree
test_autoDeriveNonRecursiveADT = testCase "autoDeriveNonRecursiveADT" $
  assertEqual "non-recursive enum ADT auto-derives all constructors"
    (Right (MultiADT [("Red", []), ("Green", []), ("Blue", [])]))
    (autoDeriveMultiValue [colorADT] (TADT "Color"))

treeADT :: ADTDecl
treeADT = ADTDecl "Tree"
  [ ("Leaf", [("val", TInt)])
  , ("Node", [("l", TADT "Tree"), ("r", TADT "Tree")])
  ]

test_autoDeriveRecursiveADTFails :: TestTree
test_autoDeriveRecursiveADTFails = testCase "autoDeriveRecursiveADTFails" $ case autoDeriveMultiValue [treeADT] (TADT "Tree") of
  Left err -> assertBool ("error should mention recursion: " ++ err) ("recursive" `isInfixOf` err)
  Right mv -> assertFailure ("expected auto-derive of recursive ADT to fail, got: " ++ show mv)

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

internalsTests :: TestTree
internalsTests = testGroup "Internals"
  [ testProperties "properties" $(allProperties)
  , classConstraintTests
  , testGroup "encode"
      [ test_encodeTupleGaussianParams
      , test_encodeDiscreteSumsToOne
      , test_encodeGaussianSigmaPositive
      , test_encodeTwoDecodersByName
      , test_encodeUsesStandaloneRegistration
      , test_encodeMainAutoDerivedBool
      , test_encodeMainIntViaRegistry
      , test_encodeMainNotRepresentable
      , test_encodeMainAndDecoderShareType
      , test_nnHoistedOutOfEnumSum
      ]
  , test_missingMainFunction
  , autoNeuralDerivationTests
  , test_tstBackendsHeader
  ]
