{-# LANGUAGE TemplateHaskell #-}

module TestInternals (
  test_internals,
  classConstraintTests,
  test_encodeTupleGaussianParams
) where

import SPLL.Lang.Lang
import SPLL.Lang.Types

import ArbitrarySPLL

import Test.QuickCheck
import SPLL.Typing.RInfer (tryAddRTypeInfo, RTypeError(..))
import SPLL.Typing.RType (ClassConstraint(..), TVarR(..), RType(..))
import SPLL.Prelude
import SPLL.Parser (tryParseProgram)
import SPLL.AutoNeural (PartitionPlan(..), makeEncodeRec)
import qualified SPLL.AutoNeural as AutoNeural (getSize)
import SPLL.IntermediateRepresentation
import IRInterpreter (generateDet)
import Data.Foldable (toList)
import Test.HUnit


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
-- CURRENT STATUS: FAILING — makeEncodeTopLevel falls through to makeEncodeRec for
-- TuplePlan, which reads NN logit-vector slots instead of invoking the SPLL
-- normal-params function for each component.  This test is a forward specification:
-- it should pass once makeEncodeTopLevel handles TuplePlan by delegating each
-- Continuous sub-plan to the compiled main_normal (or equivalent per-component)
-- function rather than to the raw NN output.
test_encodeTupleGaussianParams :: Test
test_encodeTupleGaussianParams = TestCase $ do
  let src = unlines
        [ "neural tupleNN :: (Symbol -> (Float, Float))"
        , "main sym = (1.5 * Normal + 2.0, 0.5 * Normal + (-1.0))"
        ]
  prog <- case tryParseProgram "<test>" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let mockSym = VTuple (VInt 0) (VInt 0)  -- random mock NN, seed 0 (irrelevant for closed-form)
  let sample  = VTuple (VFloat 2.0) (VFloat (-1.0))
  case runEncode defaultCompilerConfig prog mockSym sample of
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

return []
test_internals = $(forAllProperties) (quickCheckWithResult stdArgs { maxSuccess = 100 })
