{-# LANGUAGE TemplateHaskell #-}

module TestInternals (
  test_internals,
  classConstraintTests,
  test_encodeDiscreteTuple,
  test_encodeFromDistribution
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

-- Directly test makeEncodeRec for a TuplePlan of two Discretes plans.
-- Binds l_x_neural_out to a known 5-element vector and verifies the encoder
-- reads back every slot unchanged (identity property for discrete plans).
test_encodeDiscreteTuple :: Test
test_encodeDiscreteTuple = TestCase $ do
  let plan = TuplePlan
               (Discretes TInt  (MultiDiscretes [VInt 0, VInt 1, VInt 2]))
               (Discretes TBool (MultiDiscretes [VBool True, VBool False]))
  let knownVec = constructVList [VFloat 0.3, VFloat 0.4, VFloat 0.3, VFloat 0.7, VFloat 0.3]
  -- sample is irrelevant: Discretes encoder reads vector slots regardless of sample value
  let encodeExpr = IRLetIn "l_x_neural_out" (IRConst knownVec)
                     (makeEncodeRec [] plan 0 (IRConst (VTuple (VInt 0) (VBool True))))
  case generateDet [] (IREnv [] []) [] encodeExpr of
    Left err -> assertFailure ("encode evaluation failed: " ++ err)
    Right (VList result) -> do
      let items = toList result
      assertEqual "encoded list length" (AutoNeural.getSize plan) (length items)
      let checkSlot i expected = case items !! i of
            VFloat actual ->
              assertBool ("slot " ++ show i ++ ": expected " ++ show expected
                          ++ ", got " ++ show actual)
                         (abs (actual - expected) < 1.0e-9)
            other -> assertFailure ("slot " ++ show i ++ " is not VFloat: " ++ show other)
      checkSlot 0 0.3
      checkSlot 1 0.4
      checkSlot 2 0.3
      checkSlot 3 0.7
      checkSlot 4 0.3
    Right other -> assertFailure ("expected VList, got: " ++ show other)

classConstraintTests :: Test
classConstraintTests = TestList
  [ test_plusFloat
  , test_plusInt
  , test_plusBoolReject
  ]

-- Read tupleDiscreteDistrib.ppl, compute the marginal probability of each
-- discrete value using runProb, and verify that makeEncodeRec reads each
-- slot back exactly.  The key property: for a Discretes plan the encoder
-- is a pure read-back of the logit vector, so its output must equal the
-- vector we constructed from the program's own probability function.
test_encodeFromDistribution :: Test
test_encodeFromDistribution = TestCase $ do
  src  <- readFile "testCases/tupleDiscreteDistrib.ppl"
  prog <- case tryParseProgram "tupleDiscreteDistrib.ppl" src of
    Left err -> assertFailure ("Parse failed: " ++ show err) >> return undefined
    Right p  -> return p
  let plan = TuplePlan
               (Discretes TInt  (MultiDiscretes [VInt 0, VInt 1, VInt 2]))
               (Discretes TBool (MultiDiscretes [VBool True, VBool False]))
  -- joint(a, b) = P(main = (a, b))
  let joint a b = case runProb defaultCompilerConfig prog [] (VTuple a b) of
        Right (VTuple (VFloat p) _) -> p
        other -> error $ "runProb returned unexpected shape: " ++ show other
  -- Marginals by summing the other component
  let intVals  = [VInt 0, VInt 1, VInt 2]
  let boolVals = [VBool True, VBool False]
  let pInt  i = sum [joint (VInt  i) b | b <- boolVals]
  let pBool b = sum [joint a (VBool b) | a <- intVals]
  -- Build the logit vector from marginal probabilities
  let vec = constructVList [ VFloat (pInt 0), VFloat (pInt 1), VFloat (pInt 2)
                           , VFloat (pBool True), VFloat (pBool False) ]
  -- Run makeEncodeRec with this vector and an arbitrary sample
  let encodeExpr = IRLetIn "l_x_neural_out" (IRConst vec)
                     (makeEncodeRec [] plan 0 (IRConst (VTuple (VInt 0) (VBool True))))
  case generateDet [] (IREnv [] []) [] encodeExpr of
    Left err -> assertFailure ("Encode evaluation failed: " ++ err)
    Right (VList result) -> do
      let items = toList result
      assertEqual "encoded list length" (AutoNeural.getSize plan) (length items)
      let check i expected = case items !! i of
            VFloat actual ->
              assertBool ("slot " ++ show i ++ ": expected " ++ show expected
                          ++ " got " ++ show actual)
                         (abs (actual - expected) < 1.0e-6)
            other -> assertFailure ("slot " ++ show i ++ " not VFloat: " ++ show other)
      check 0 (pInt 0)       -- P(a=0)    = 0.5
      check 1 (pInt 1)       -- P(a=1)    = 0.25
      check 2 (pInt 2)       -- P(a=2)    = 0.25
      check 3 (pBool True)   -- P(b=True) = 0.7
      check 4 (pBool False)  -- P(b=False)= 0.3
    Right other -> assertFailure $ "expected VList, got: " ++ show other

return []
test_internals = $(forAllProperties) (quickCheckWithResult stdArgs { maxSuccess = 100 })
