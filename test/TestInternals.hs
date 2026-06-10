{-# LANGUAGE TemplateHaskell #-}

module TestInternals (
  test_internals,
  classConstraintTests,
  test_encodeTupleGaussianParams,
  test_encodeDiscreteSumsToOne,
  test_encodeGaussianSigmaPositive,
  test_nnHoistedOutOfEnumSum,
  test_missingMainFunction,
  autoNeuralDerivationTests
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
import Test.HUnit
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
test_plusFloat :: Test
test_plusFloat = TestCase $
  assertBool "plus TFloat TFloat should typecheck" $
    typechecks (Program [("main", constF 1.0 #+# constF 2.0)] [] [])

-- plus on two int constants should succeed
test_plusInt :: Test
test_plusInt = TestCase $
  assertBool "plusI TInt TInt should typecheck" $
    typechecks (Program [("main", constI 1 #<+># constI 2)] [] [])

-- Bool + Bool should be rejected with a ClassConstraintViolation
test_plusBoolReject :: Test
test_plusBoolReject = TestCase $ do
  let src = unlines
        [ "coin = if Uniform < 0.5 then True else False"
        , "main = coin + coin"
        ]
  case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err)
    Right prog -> case tryAddRTypeInfo prog of
      Left (ClassConstraintViolation _ _) -> return ()
      other -> assertFailure ("Expected ClassConstraintViolation, got: " ++ show other)

classConstraintTests :: Test
classConstraintTests = TestList
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
test_encodeTupleGaussianParams :: Test
test_encodeTupleGaussianParams = TestCase $ do
  let src = unlines
        [ "neural tupleNN :: (Symbol -> (Float, Float))"
        , "main = (1.5 * Normal + 2.0, 0.5 * Normal + (-1.0))"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  -- Closed-form program: no outer params, so runEncode takes an empty arg list.
  case runEncode defaultCompilerConfig prog [] of
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
test_encodeDiscreteSumsToOne :: Test
test_encodeDiscreteSumsToOne = TestCase $ do
  let src = unlines
        [ "neural discreteNN :: (Symbol -> Int) of [0, 1, 2]"
        , "main sym = if discreteNN sym == 0 then 2 else 0"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  -- Try several different mock syms; each should give a prob vector summing to 1.
  let mockSyms = [ VTuple (VInt 0) (VInt s) | s <- [0, 1, 42, 100, 999] ]
  mapM_ (\sym -> case runEncode defaultCompilerConfig prog [sym] of
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
test_encodeGaussianSigmaPositive :: Test
test_encodeGaussianSigmaPositive = TestCase $ do
  let src = unlines
        [ "neural gaussNN :: (Symbol -> Float)"
        , "main sym = gaussNN sym"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let mockSyms = [ VTuple (VInt 0) (VInt s) | s <- [0, 1, 7, 42] ]
  mapM_ (\sym -> case runEncode defaultCompilerConfig prog [sym] of
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
test_nnHoistedOutOfEnumSum :: Test
test_nnHoistedOutOfEnumSum = TestCase $ do
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
test_missingMainFunction :: Test
test_missingMainFunction = TestCase $ do
  let prog = Program [("notMain", constF 1.0)] [] []
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
test_autoDeriveFloat :: Test
test_autoDeriveFloat = TestCase $
  assertEqual "Float auto-derives to MultiContinuous"
    (Right MultiContinuous) (autoDeriveMultiValue [] TFloat)

test_autoDeriveBool :: Test
test_autoDeriveBool = TestCase $
  assertEqual "Bool auto-derives to [True, False]"
    (Right (MultiDiscretes [VBool True, VBool False])) (autoDeriveMultiValue [] TBool)

test_autoDeriveIntFails :: Test
test_autoDeriveIntFails = TestCase $ case autoDeriveMultiValue [] TInt of
  Left err -> assertBool ("error should mention Int: " ++ err) ("Int" `isInfixOf` err)
  Right mv -> assertFailure ("expected auto-derive of Int to fail, got: " ++ show mv)

test_autoDeriveTuple :: Test
test_autoDeriveTuple = TestCase $
  assertEqual "Tuple of (Bool, Float) auto-derives componentwise"
    (Right (MultiTuple (MultiDiscretes [VBool True, VBool False]) MultiContinuous))
    (autoDeriveMultiValue [] (Tuple TBool TFloat))

colorADT :: ADTDecl
colorADT = ADTDecl "Color" [("Red", []), ("Green", []), ("Blue", [])] Nothing

test_autoDeriveNonRecursiveADT :: Test
test_autoDeriveNonRecursiveADT = TestCase $
  assertEqual "non-recursive enum ADT auto-derives all constructors"
    (Right (MultiADT [("Red", []), ("Green", []), ("Blue", [])]))
    (autoDeriveMultiValue [colorADT] (TADT "Color"))

treeADT :: ADTDecl
treeADT = ADTDecl "Tree"
  [ ("Leaf", [("val", TInt)])
  , ("Node", [("l", TADT "Tree"), ("r", TADT "Tree")])
  ] Nothing

test_autoDeriveRecursiveADTFails :: Test
test_autoDeriveRecursiveADTFails = TestCase $ case autoDeriveMultiValue [treeADT] (TADT "Tree") of
  Left err -> assertBool ("error should mention recursion: " ++ err) ("recursive" `isInfixOf` err)
  Right mv -> assertFailure ("expected auto-derive of recursive ADT to fail, got: " ++ show mv)

-- AutoNeural: makePartitionPlan resolves "Nothing" and "_" (MultiAuto) via auto-derivation,
-- and "Real" (MultiContinuous) directly to a Continuous plan.
test_makePartitionPlanNothingFloat :: Test
test_makePartitionPlanNothingFloat = TestCase $
  assertEqual "Nothing for Float resolves to Continuous"
    Continuous (makePartitionPlan [] TFloat Nothing)

test_makePartitionPlanNothingTuple :: Test
test_makePartitionPlanNothingTuple = TestCase $
  assertEqual "Nothing for (Bool, Float) resolves componentwise"
    (TuplePlan (Discretes TBool (MultiDiscretes [VBool True, VBool False])) Continuous)
    (makePartitionPlan [] (Tuple TBool TFloat) Nothing)

test_makePartitionPlanWildcardMatchesNothing :: Test
test_makePartitionPlanWildcardMatchesNothing = TestCase $
  assertEqual "explicit '_' placeholders resolve the same as Nothing"
    (makePartitionPlan [] (Tuple TBool TFloat) Nothing)
    (makePartitionPlan [] (Tuple TBool TFloat) (Just (MultiTuple MultiAuto MultiContinuous)))

test_makePartitionPlanMixedExplicitAuto :: Test
test_makePartitionPlanMixedExplicitAuto = TestCase $
  assertEqual "an explicit Int enumeration alongside an auto-derived ('_') Float"
    (TuplePlan (Discretes TInt (MultiDiscretes [VInt 0, VInt 1, VInt 2])) Continuous)
    (makePartitionPlan [] (Tuple TInt TFloat) (Just (MultiTuple (MultiDiscretes [VInt 0, VInt 1, VInt 2]) MultiAuto)))

autoNeuralDerivationTests :: Test
autoNeuralDerivationTests = TestList
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

return []

-- Like $(forAllProperties), but stays quiet about properties that pass
-- (no per-property "=== prop_X ===\n+++ OK, passed N tests." block) and only
-- prints the full QuickCheck report for properties that fail.
runPropsQuiet :: Args -> [(String, Property)] -> IO Bool
runPropsQuiet args ps = do
  results <- mapM runOne ps
  putStrLn $ "  " ++ show (length (filter id results)) ++ "/" ++ show (length ps) ++ " properties passed"
  return (and results)
  where
    runOne (name, p) = do
      r <- quickCheckWithResult args { chatty = False } p
      if isSuccess r
        then return True
        else do
          putStrLn $ "=== " ++ name ++ " ==="
          putStr (output r)
          return False

test_internals :: IO Bool
test_internals = runPropsQuiet stdArgs { maxSuccess = 100 } $(allProperties)
