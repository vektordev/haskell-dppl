--{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

import Test.QuickCheck hiding (verbose)
import System.Exit (exitWith, ExitCode(ExitFailure))

import SPLL.Examples
--import Lib
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Typing.Typing
import SPLL.Typing.RInfer
import SPLL.Analysis
import SPLL.IntermediateRepresentation
import SPLL.IRCompiler
import SPLL.Validator
import IRInterpreter
import Data.Maybe (fromJust, catMaybes)
import Control.Monad.Random.Lazy (Random, RandomGen, Rand, evalRandIO)
import SPLL.Typing.Infer
--import ArbitrarySPLL
import Options.Applicative
import Control.Exception.Base (SomeException, try)
import Test.QuickCheck.Monadic (monadicIO, run, assert)
import Test.QuickCheck.Property (failed, reason)
import Debug.Trace (trace, traceShowId, traceId, traceShow)
import SPLL.Lang.Lang (Value)
import Data.Foldable
import Data.Number.Erf (erf)
import Numeric.AD (grad', auto)
import Numeric.AD.Internal.Reverse (Reverse, Tape)
import Data.Reflection (Reifies)
import Data.Bifunctor (second)
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Parser
import TestParser
import TestInternals (test_internals, classConstraintTests, test_encodeDiscreteTuple, test_encodeFromDistribution)
import Test.HUnit (runTestTT)
import End2EndTesting
import TestCaseParser (parseProgram)
import SPLL.Prelude


-- Generalizing over different compilation stages, we can fit all "this typing is what the compiler would find" cases.
class Recompilable a where
  recompile :: a -> Either CompileError a

untypeP :: Program -> Program
untypeP (Program defs neuralDecl adts) = Program (map (\(a,b) -> (a, untypeE b)) defs) neuralDecl adts

untypeE :: Expr -> Expr
untypeE = tMap (const makeTypeInfo)

instance Recompilable Program where
  recompile = infer . untypeP

instance Recompilable Expr where
  recompile e = case infer $ makeMain $ untypeE e of
    Right (Program [("main", d)] _ _) -> Right d
    Left x -> Left x
    Right (Program _ _ _) -> error "unexpected error when recompiling Expr TypeInfo."

thetaTreeExample :: IRExpr
thetaTreeExample = IRConst (VThetaTree (ThetaTree [0, 1, 2, 3] [ThetaTree [4, 5, 6, 7] [], ThetaTree [8, 9, 10, 11] [], ThetaTree [12, 13, 14, 15] []]))

flatTree :: [Double] -> [IRExpr]
flatTree a = [IRConst (VThetaTree (ThetaTree a []))]

normalPDF :: Double -> Double
normalPDF x = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)

normalCDF :: Double -> Double
normalCDF x = (1/2)*(1 + erf (x/sqrt (2)))

correctProbValuesTestCases :: [(Program, IRValue, [IRExpr], (IRValue, IRValue))]
--correctProbValuesTestCases = [(testDiceAdd, VInt 2, [], (VFloat (1 / 36), VFloat 0))]
correctProbValuesTestCases = [ (uniformProg, VFloat 0.5, [], (VFloat 1.0, VFloat 1)),
                               (normalProg, VFloat 0.5, [], (VFloat $ normalPDF 0.5, VFloat 1)),
                               (uniformProgMult, VFloat (-0.25), [], (VFloat 2, VFloat 1)),
                               (normalProgMult, VFloat (-1), [], (VFloat (normalPDF (-2) * 2), VFloat 1)),
                               (normalProgMultPlus, VFloat (-2), [], (VFloat ((normalPDF (-1.5)) / 2), VFloat 1)),
                               (uniformNegPlus, VFloat (-4.5), [], (VFloat 1, VFloat 1)),
                               (testList, constructVList [VFloat 0.25, VFloat 0], [], (VFloat $ normalPDF 0 * 2, VFloat 2)),
                               (simpleTuple, VTuple (VFloat 0.25) (VFloat 0), [], (VFloat $ normalPDF 0 * 2, VFloat 2)),
                               (simpleTuple, VTuple (VFloat 0.25) VAny, [], (VFloat $ 2, VFloat 1)),
                               (simpleTuple, VTuple VAny (VFloat 0), [], (VFloat $ normalPDF 0, VFloat 1)),
                               (uniformIfProg, VFloat 0.5, [], (VFloat 0.5, VFloat 1)),
                               (constantProg, VFloat 2, [], (VFloat 1, VFloat 0)),
                               (uniformExp, VFloat $ exp 4.5, [], (VFloat $ 1 / exp 4.5, VFloat 1)),
                               (uniformExp, VFloat (-1), [], (VFloat 0, VFloat 0)),
                               (testInjF, VFloat 1.5, [], (VFloat 0.5, VFloat 1)),
                               (testInjF2, VFloat 3, [], (VFloat 0.5, VFloat 1)),
                               (testTheta, VFloat 1.5, flatTree [1.5], (VFloat 1, VFloat 0)),
                               (testTheta, VFloat 1.5, flatTree [1], (VFloat 0, VFloat 0)),
                               (testThetaTree, VFloat 11, [thetaTreeExample], (VFloat 1, VFloat 0)),
                               (testNot, VBool True, [], (VFloat 0.25, VFloat 0)),
                               (simpleCall, VFloat 0.5, [], (VFloat 1.0, VFloat 1)),
                               (testCallArg, VFloat 3.5, [], (VFloat 1.0, VFloat 1)),
                               (testInjFPlusLeft, VFloat 1.5, [], (VFloat 1.0, VFloat 1)),
                               (testInjFPlusRight, VFloat 1.5, [], (VFloat 1.0, VFloat 1)),
                               (testDim, VFloat 3, [], (VFloat 0.5, VFloat 0)),
                               (testDim, VFloat 0.4, [], (VFloat 0.25, VFloat 1)),
                               (testCoin, VInt 1, [], (VFloat 0.5, VFloat 0)),
                               (testCoin, VInt 3, [], (VFloat 0.0, VFloat 0)),
                               (testDice, VInt 2, [], (VFloat 0.16666666, VFloat 0)),
                               (testDice, VInt 7, [], (VFloat 0, VFloat 0)),
                               (testDiceAdd, VInt 2, [], (VFloat (1 / 36), VFloat 0)),
                               (testDiceAdd, VInt 7, [], (VFloat (6 / 36), VFloat 0)),
                               (testDiceAdd, VInt 1, [], (VFloat 0, VFloat 0)),
                               (testDimProb, VFloat 0.5, [], (VFloat 0.4, VFloat 0)),
                               (testDimProb, VFloat 0.0, [], (VFloat (0.6 * 0.39894228040143265), VFloat 1)),
                               (gaussLists, constructVList [VFloat 0, VFloat 0, VFloat 0], [IRConst $ VThetaTree (ThetaTree [0.5, 1, 0] [])], (VFloat $ (normalPDF 0) * (normalPDF 0) * (normalPDF 0) / 16, VFloat 3)),
                               --(testPartialInjF, VFloat 5.5, [], (VFloat 1, VFloat 1))]
                               (testInjFRenaming, VFloat 5.5, [], (VFloat 1, VFloat 1)),
                               (gaussLists, constructVList [VFloat 0, VFloat 0, VFloat 0], [IRConst $ VThetaTree (ThetaTree [0.5, 1, 0] [])], (VFloat $ (normalPDF 0) * (normalPDF 0) * (normalPDF 0) / 16, VFloat 3)),
                               (testLeft, VFloat 2, [], (VFloat 1.0, VFloat 0)),
                               (testLeft, VFloat 3, [], (VFloat 0, VFloat 0)),
                               (testEither, VEither (Left (VFloat 0.5)), [], (VFloat 0.5, VFloat 1)),
                               (testEither, VEither (Right (VInt 2)), [], (VFloat 0, VFloat 0)),
                               (testEither, VEither (Right (VInt 1)), [], (VFloat 0.5, VFloat 0)),
                               (testIsLeft, VFloat 1, [], (VFloat 0.4, VFloat 0)),
                               (testIsLeft, VFloat 2, [], (VFloat 0.6, VFloat 0)),
                               (testIsLeft, VFloat 0, [], (VFloat 0, VFloat 0)),
                               (testIsRight, VFloat 1, [], (VFloat 0.6, VFloat 0)),
                               (testIsRight, VFloat 2, [], (VFloat 0.4, VFloat 0)),
                               (testIsRight, VFloat 0, [], (VFloat 0, VFloat 0)),
                               (testFst, VFloat 0.5, [], (VFloat 1, VFloat 1)),
                               (testFstCall, VFloat 0.5, [], (VFloat 1, VFloat 1)),
                               (testFstDiscrete, VFloat 0.5, [], (VFloat 1, VFloat 1)),
                               (testHead, VFloat 0.5, [], (VFloat 1, VFloat 1)),
                               (testTail, VFloat 0.5, [], (VFloat 1, VFloat 1)),
                               (testInjFRenaming, VFloat 5.5, [], (VFloat 1, VFloat 1))]
                               --(testLambdaChoice, VFloat 1.5, [], (VFloat ((1 + normalPDF 0.5) / 2), VFloat 1))]

                              --(testLambdaParameter, VFloat 10, [], VFloat 1.0)]

correctIntegralValuesTestCases :: [(Program, IRValue, IRValue, [IRExpr], (IRValue, IRValue))]
correctIntegralValuesTestCases =[(uniformProg, VFloat 0, VFloat 1, [], (VFloat 1.0, VFloat 0)),
                                (uniformProg, VFloat (-1), VFloat 2, [], (VFloat 1.0, VFloat 0)),
                                (normalProg, VFloat (-5), VFloat 5, [], (VFloat $ normalCDF 5 - normalCDF (-5), VFloat 0)),
                                --(normalProg, VFloat 0, VFloat 0, [], (VFloat $ normalPDF 0, VFloat 0)),
                                (normalProgMult, VFloat (-5), VFloat 5, [], (VFloat $ normalCDF 10 - normalCDF (-10), VFloat 0)),
                                (normalProgMult, VFloat (-10), VFloat (-5), [], (VFloat $ normalCDF (-10) - normalCDF (-20), VFloat 0)),
                                (uniformNegPlus, VFloat (-5), VFloat (-4.5), [], (VFloat 0.5, VFloat 0)),
                                (uniformProgPlus, VFloat 4, VFloat 4.5, [], (VFloat 0.5, VFloat 0)),
                                (uniformIfProg, VFloat 0, VFloat 1, [], (VFloat 0.5, VFloat 0)),
                                (constantProg, VFloat 1, VFloat 3, [], (VFloat 1, VFloat 0)),
                                --,
                                (testInjF, VFloat 0, VFloat 1, [], (VFloat 0.5, VFloat 0)),
                                (testInjF2, VFloat 2, VFloat 3, [], (VFloat 0.5, VFloat 0)),
                                (testInjFPlusLeft, VFloat 1, VFloat 1.5, [], (VFloat 0.5, VFloat 0)),
                                (testInjFPlusRight, VFloat 1, VFloat 1.5, [], (VFloat 0.5, VFloat 0)),
                                (testTheta, VFloat 0.9, VFloat 1.1, flatTree [1], (VFloat 1, VFloat 0)),
                                (simpleCall, VFloat 0, VFloat 1, [], (VFloat 1.0, VFloat 0)),
                                (testCallArg, VFloat 3.5, VFloat 4.5, [], (VFloat 0.5, VFloat 0)),
                                (testCallLambda, VFloat 2, VFloat 3, [], (VFloat 1.0, VFloat 0)),
                                (testInjFRenaming, VFloat 5, VFloat 5.5, [], (VFloat 0.5, VFloat 0)),
                                (testIsLeft, VFloat 0, VFloat 3, [], (VFloat 1, VFloat 0)),
                                (testIsLeft, VFloat 1.5, VFloat 3, [], (VFloat 0.6, VFloat 0)),
                                (testIsRight, VFloat 0, VFloat 3, [], (VFloat 1, VFloat 0)),
                                (testIsRight, VFloat 1.5, VFloat 3, [], (VFloat 0.4, VFloat 0)),
                                (testFst, VFloat 0.4, VFloat 3, [], (VFloat 0.6, VFloat 0)),
                                (testHead, VFloat 0.4, VFloat 3, [], (VFloat 0.6, VFloat 0)),
                                (testTail, VFloat 0.4, VFloat 3, [], (VFloat 0.6, VFloat 0))]

invalidTestCases :: [Program]
invalidTestCases = [invalidDuplicateDecl1, invalidDuplicateDecl2, invalidDuplicateDecl3, invalidDuplicateDecl4, invalidDuplicateDecl5, invalidMissingDecl, invalidMissingInjF, invalidReservedName, invalidReservedName2, invalidWrongArgCount]

                                  --(testLambdaParameter, VFloat 9, VFloat 11, [], VFloat 1.0)]
                                  --(testCallLambdaAdvanced, VFloat 2, VFloat 3, [], VFloat 1.0),
                                  --(testLetIn, VFloat 1.5, VFloat 2, [], VFloat 0.5)]

prop_CheckValidPrograms :: Property
prop_CheckValidPrograms = forAll (elements correctProbValuesTestCases) checkValidPrograms

prop_CheckInvalidPrograms :: Property
prop_CheckInvalidPrograms = forAll (elements invalidTestCases) checkInvalidPrograms


prop_CheckProbTestCases :: Property
prop_CheckProbTestCases = forAll (elements correctProbValuesTestCases) checkProbTestCase

prop_CheckProbTestCasesSample :: Property
prop_CheckProbTestCasesSample = forAll (elements correctProbValuesTestCases) $ \tc@(_, _, _, (_, outDim)) ->
  case outDim of
    VFloat d | d >= 2 -> testSamplingProb 0.05 1000 8 tc  -- extra retries for 2D (max 256k samples)
    _                 -> testSamplingProb 0.05 1000 5 tc

prop_CheckIntegralTestCases :: Property
prop_CheckIntegralTestCases = forAll (elements correctIntegralValuesTestCases) checkIntegralTestCase

prop_CheckIntegralConverges :: Property
prop_CheckIntegralConverges = forAll (elements correctIntegralValuesTestCases) checkIntegralConverges

prop_CheckTopKInterprets :: Property
prop_CheckTopKInterprets = forAll (elements correctProbValuesTestCases) checkTopKInterprets

prop_CheckProbTestCasesWithBC :: Property
prop_CheckProbTestCasesWithBC = forAll (elements correctProbValuesTestCases) checkProbTestCasesWithBC

prop_TopK :: Property
prop_TopK = ioProperty $ do
  actualOutput0 <- evalRandIO $ irDensityTopK testTopK 0.1 (VFloat 0) []
  actualOutput1 <- evalRandIO $ irDensityTopK testTopK 0.1 (VFloat 1) []
  case (actualOutput0, actualOutput1) of
    (VTuple a (VFloat _), VTuple b (VFloat _)) -> return $ (b == VFloat 0.95) && (a == VFloat 0)
    _ -> return False

prop_any :: Property
prop_any = forAll (elements correctProbValuesTestCases) checkProbAny

-- DO NOT CHANGE THIS CODE WITHOUT ALSO CHANGING THE CODE IN THE README
prop_CheckReadmeCodeListing1 :: Property
prop_CheckReadmeCodeListing1 = ioProperty $ do
  let twoDice = Program [("main", dice 6 #<+># dice 6)] [] []
  case runGen defaultCompilerConfig twoDice [] of
    Left err -> return $ counterexample err False
    Right gen' -> do
      gen <- evalRandIO gen'
      case runProb defaultCompilerConfig twoDice [] gen of
        Left err -> return $ counterexample err False
        Right (VTuple (VFloat prob) (VFloat dim)) -> do
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

-- DO NOT CHANGE THIS CODE WITHOUT ALSO CHANGING THE CODE IN THE README
prop_CheckReadmeCodeListing2 :: Property
prop_CheckReadmeCodeListing2 = ioProperty $ do
  let dist = Program [("main", normal #*# constF 2 #+# constF 1)] [] []
  case runGen defaultCompilerConfig dist [] of
    Left err -> return $ counterexample err False
    Right gen' -> do 
      gen <- evalRandIO gen'
      case runProb defaultCompilerConfig dist [] gen of
        Left err -> return $ counterexample err False
        Right (VTuple (VFloat prob) (VFloat dim)) -> do
          -- Original Listing above, Tests below
          let (VFloat genF) = gen
          return $ (VFloat prob) `reasonablyClose` (VFloat (normalPDF ((genF - 1) / 2) / 2))

checkValidPrograms :: (Program, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkValidPrograms (p, _, _, _) = case validateProgram p of
  Right _ -> property True
  Left err -> counterexample err False

checkInvalidPrograms :: Program -> Property
checkInvalidPrograms p = case validateProgram p of
  Left _ -> property True
  Right _ -> counterexample "Program validates even though it should not" False


checkProbTestCase :: (Program, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkProbTestCase (p, inp, params, (out, VFloat outDim)) = ioProperty $ do
  actualOutput <- evalRandIO $ irDensity p inp params
  case actualOutput of
    VTuple a (VFloat d) -> return $ a `reasonablyClose` out .&&. d === outDim
    _ -> return $ counterexample "Return type was no tuple" False

checkIntegralTestCase :: (Program, IRValue, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkIntegralTestCase (p, low, high, params, (out, outDim)) = ioProperty $ do
  actualOutput <- evalRandIO $ irIntegral p low high params
  case actualOutput of
    VTuple a aDim -> return $ a `reasonablyClose` out .&&. aDim === outDim
    _ -> return $ counterexample "Return type was no tuple" False

--TODO better bounds for Integral
checkIntegralConverges :: (Program, IRValue, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkIntegralConverges (p, VFloat a, VFloat b, params, _) = ioProperty $ do
  actualOutput <- evalRandIO $ irIntegral p (VFloat (-9999999)) (VFloat 9999999) params
  case actualOutput of
    VTuple a (VFloat _) -> return $ a `reasonablyClose` VFloat 1
    _ -> return $ counterexample "Return type was no tuple" False
checkIntegralConverges _ = False ==> False

checkZeroWidthIntegral :: (Program, IRValue, IRValue, [IRExpr], IRValue) -> Property
checkZeroWidthIntegral (p, lower, _, params, _) = ioProperty $ do
  integralOutput <- evalRandIO $ irIntegral p lower lower params
  probOutput <- evalRandIO $ irDensity p lower params
  case (integralOutput, probOutput) of
    (VTuple a (VFloat _), VTuple b (VFloat _)) -> return $ a `reasonablyClose` b
    _ -> return $ counterexample "Return type was no tuple" False

checkTopKInterprets :: (Program, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkTopKInterprets (p, inp, params, _) = ioProperty $ do
  actualOutput <- evalRandIO $ irDensityTopK p 0.05 inp params
  return $ actualOutput `reasonablyClose` actualOutput  -- No clue what the correct value should be here. Just test that is interprets to any value

checkProbTestCasesWithBC :: (Program, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkProbTestCasesWithBC (p, inp, params, (out, VFloat outDim)) = ioProperty $ do
  actualOutput <- evalRandIO $ irDensityBC p inp params
  case actualOutput of
    VTuple a (VTuple (VFloat d) (VFloat _)) -> return $ a `reasonablyClose` out .&&. d === outDim
    _ -> return $ counterexample "Return type was no tuple" False

checkProbAny :: (Program, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkProbAny (p, _, params, _) = ioProperty $ do
  actualOutput <- evalRandIO $ irDensity p VAny params
  case actualOutput of
    VTuple a (VFloat d) -> return $ a === VFloat 1
    _ -> return $ counterexample "Return type was no tuple" False

--prop_CheckProbTestCases = foldr (\(p, inp, out) acc -> do
--  checkProbTestCase p inp out .&&. acc) (True===True) correctProbValuesTestCases

irDensityTopK :: RandomGen g => Program -> Double -> IRValue -> [IRExpr]-> Rand g IRValue
irDensityTopK p thresh s params = IRInterpreter.generateRand (neurals p) irEnv (sampleExpr:IRConst (VFloat 1.0):params) irExpr
  where Just (irExpr, _) = probFun (lookupIREnv "main" irEnv)
        sampleExpr = IRConst s
        irEnv = envToIR defaultCompilerConfig {topKThreshold = Just thresh} annotated
        annotated = (annotateAlgsProg . annotateConditionalProg) typedProg
        Right typedProg = addTypeInfo forwardChained
        forwardChained = annotateProg preAnnotated
        preAnnotated = annotateEnumsProg p

irDensityBC :: RandomGen g => Program -> IRValue -> [IRExpr]-> Rand g IRValue
irDensityBC p s params = IRInterpreter.generateRand (neurals p) irEnv (sampleExpr:params) irExpr
  where Just (irExpr, _) = probFun (lookupIREnv "main" irEnv)
        sampleExpr = IRConst s
        irEnv = envToIR defaultCompilerConfig {countBranches = True} annotated
        annotated = (annotateAlgsProg . annotateConditionalProg) typedProg
        Right typedProg = addTypeInfo forwardChained
        forwardChained = annotateProg preAnnotated
        preAnnotated = annotateEnumsProg p

irDensity :: RandomGen g => Program -> IRValue -> [IRExpr] -> Rand g IRValue
irDensity p s params = IRInterpreter.generateRand (neurals p) irEnv (sampleExpr:params) irExpr
  where Just (irExpr, _) = probFun (lookupIREnv "main" irEnv)
        sampleExpr = IRConst s
        irEnv = envToIR defaultCompilerConfig annotated
        annotated = (annotateAlgsProg . annotateConditionalProg) typedProg
        Right typedProg = addTypeInfo forwardChained
        forwardChained = annotateProg preAnnotated
        preAnnotated = annotateEnumsProg p

irIntegral :: RandomGen g => Program -> IRValue -> IRValue -> [IRExpr] -> Rand g IRValue
irIntegral p low high params = do
  highVal <- interpret highExpr
  lowVal <- interpret lowExpr
  case (highVal, lowVal) of
    (VTuple (VFloat highP) (VFloat highD),
     VTuple (VFloat lowP)  (VFloat lowD)) -> return $ VTuple (VFloat (highP - lowP)) (VFloat lowD)
    _ -> error "irIntegral: unexpected IRValue shape"
  where
    interpret x = IRInterpreter.generateRand (neurals p) irEnv (x:params) irExpr
    Just (irExpr, _) = integFun (lookupIREnv "main" irEnv)
    lowExpr = IRConst low
    highExpr = IRConst high
    irEnv = envToIR defaultCompilerConfig annotated
    annotated = (annotateAlgsProg . annotateConditionalProg) typedProg
    Right typedProg = addTypeInfo forwardChained
    forwardChained = annotateProg preAnnotated
    preAnnotated = annotateEnumsProg p

irGen :: RandomGen g => Program -> [IRExpr] -> Rand g IRValue
irGen p params = IRInterpreter.generateRand (neurals p) irEnv params irExpr
  where Just (irExpr, _) = genFun (lookupIREnv "main" irEnv)
        irEnv = envToIR defaultCompilerConfig annotated
        annotated = (annotateAlgsProg . annotateConditionalProg) typedProg
        Right typedProg = addTypeInfo forwardChained
        forwardChained = annotateProg preAnnotated
        preAnnotated = annotateEnumsProg p

reasonablyClose :: IRValue -> IRValue -> Property
reasonablyClose (VFloat a) (VFloat b) = counterexample (show a ++ "/=" ++ show b) (property $ abs (a - b) <= 1e-5)
reasonablyClose a b = a === b

--Sample PDF against expected PDF. Retiry specific number of times with double the samples each time
testSamplingProb :: Double -> Int -> Int -> (Program, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
testSamplingProb epsilon samples retries (p, VFloat inp, params, (VFloat out, VFloat outDim))  = ioProperty $ evalRandIO $ do
  endlessSamples <- sequence (repeat (irGen p params >>= \(VFloat x) -> return x)) -- Generates an endless stream of samples
  let samplesInRange = map (\x -> abs (x - inp) <= epsilon/2) endlessSamples
  let countInside = foldr (\b acc -> if b then acc + 1 else acc) 0 (take samples samplesInRange)
  let ratioInside = fromIntegral countInside / fromIntegral samples
  let estimatePDF = ratioInside / (epsilon ** outDim) -- outDim is either 1 or 0 here. For dimensionality 0 we dont need to divide by epsilon
  let valid = abs (estimatePDF - out) <= 0.1
  if valid then
    return $ property True
  else
    if retries > 0 then
      return $ testSamplingProb epsilon (samples * 2) (retries - 1) (p, VFloat inp, params, (VFloat out, VFloat outDim))
    else
      return $ counterexample ("Sampled PDF is: " ++ show estimatePDF ++ ", but should be: " ++ show out) (property valid)
testSamplingProb _ samples retries (p, VInt inp, params, (VFloat out, VFloat outDim))  = ioProperty $ evalRandIO $ do
  endlessSamples <- sequence (repeat (irGen p params >>= \(VInt x) -> return x)) -- Generates an endless stream of samples
  let samplesInRange = map (==inp) endlessSamples
  let countInside = foldr (\b acc -> if b then acc + 1 else acc) 0 (take samples samplesInRange)
  let ratioInside = fromIntegral countInside / fromIntegral samples
  let estimatePDF = ratioInside
  let valid = abs (estimatePDF - out) <= 0.1
  if valid then
    return $ property True
  else
    if retries > 0 then
      return $ testSamplingProb 0 (samples * 2) (retries - 1) (p, VInt inp, params, (VFloat out, VFloat outDim))
    else
      return $ counterexample ("Sampled PDF is: " ++ show estimatePDF ++ ", but should be: " ++ show out) (property valid)
testSamplingProb epsilon samples retries (p, VTuple (VFloat inp1) (VFloat inp2), params, (VFloat out, VFloat outDim)) = ioProperty $ evalRandIO $ do
  endlessSamples <- sequence (repeat (irGen p params >>= \(VTuple (VFloat x1) (VFloat x2)) -> return (x1, x2))) -- Generates an endless stream of samples
  let samplesInRange = map (\(x1, x2) -> (abs (x1 - inp1) <= epsilon/2) && (abs (x2 - inp2) <= epsilon/2)) endlessSamples   -- Use the maximum norm
  let countInside = foldr (\b acc -> if b then acc + 1 else acc) 0 (take samples samplesInRange)
  let ratioInside = fromIntegral countInside / fromIntegral samples
  let estimatePDF = ratioInside / (epsilon ** outDim) -- The maximum norm creates a outDim-dimensional hypercube. In this boring case its either a point, a line or a square depending on the dimension
  let valid = abs (estimatePDF - out) <= 0.1
  if valid then
    return $ property True
  else
    if retries > 0 then
      return $ testSamplingProb epsilon (samples * 2) (retries - 1) (p, VTuple (VFloat inp1) (VFloat inp2), params, (VFloat out, VFloat outDim))
    else
      return $ counterexample ("Sampled PDF is: " ++ show estimatePDF ++ ", but should be: " ++ show out) (property valid)
testSamplingProb epsilon samples retries (p, VList inp, params, (VFloat out, VFloat outDim))
  | all isVFloat inp = ioProperty $ evalRandIO $ do
  endlessSamples <- sequence (repeat (irGen p params >>= \(VList l) -> return l)) -- Generates an endless stream of samples
  let samplesInRange = map (\l -> length l == length inp && all (\(VFloat x, VFloat y) -> abs (x - y) <= epsilon/2 ) (zip l (toList inp))) (map toList endlessSamples)   -- Use the maximum norm
  let countInside = foldr (\b acc -> if b then acc + 1 else acc) 0 (take samples samplesInRange)
  let ratioInside = fromIntegral countInside / fromIntegral samples
  let estimatePDF = ratioInside / (epsilon ** outDim) -- The maximum norm creates a outDim-dimensional hypercube. In this boring case its either a point, a line or a square depending on the dimension
  let valid = abs (estimatePDF - out) <= 0.1
  if valid then
    return $ property True
  else
    if retries > 0 then
      return $ testSamplingProb epsilon (samples * 2) (retries - 1) (p, VList inp, params, (VFloat out, VFloat outDim))
    else
      return $ counterexample ("Sampled PDF is: " ++ show estimatePDF ++ ", but should be: " ++ show out) (property valid)
testSamplingProb _ _ _ _ = False ==> False




{-irInterpret :: RandomGen g => Program () Double -> [IRExpr] -> Rand g Value
irInterpret p params = IRInterpreter.generate irEnv irEnv [] params main
  where Just main = lookup "main_prob" irEnv
        irEnv = envToIR defaultCompilerConfig annotated
        annotated = map (\(a,b) -> (a, annotate b)) env
        env = progToEnv typedProg
        typedProg = addTypeInfo p
-}

{-
prop_CompilablesInterpretable :: Program () Double -> Property
prop_CompilablesInterpretable prog = ioProperty $ do 
  ci <- canInterpret prog
  return $ canCompile prog ==> ci

langDensity :: Program () Double -> Double -> Value
langDensity p sample = case Interpreter.runInferL [] witExpr [] (VFloat sample) of
  PDF prob -> VFloat prob
  DiscreteProbability prob -> VFloat prob
  where Program _ witExpr = addWitnessesProg typedProg
        typedProg = addTypeInfo p


-- Program sets for tests
examples :: [Program () Double]
examples = [makeMain variableLength, makeMain testGreater, makeMain testGaussianMixture, makeMain testIntractable]

{-
testsetA :: [Program TypeInfo Double]
testsetA = [variableLengthT, testLetTupleT, testLetXYT]
prop_RecompileA :: Property
prop_RecompileA = forAll (elements testsetA) testRecompile
-}
--testsetB :: [Expr TypeInfo Double]
--testsetB = [triMNist]
--prop_RecompileB :: Property
--prop_RecompileB = forAll (elements testsetB) testRecompile

compilables :: [Expr () Double]
compilables = [flipCoin, compilationExample, failureCase, testInconsistent, testGauss, testGaussianMixture, variableLength, testGreater, testGaussianMixture]
prop_CanCompile :: Property
prop_CanCompile = forAll (elements $ map makeMain compilables) canCompile

compilables2 :: [Program () Double]
compilables2 = [uniformProg, normalProg, uniformProgMult]
prop_CanCompile2 :: Property
prop_CanCompile2 = forAll (elements compilables2) canCompile

uncompilables :: [Expr () Double]
uncompilables = [testIntractable]

canCompile :: (Show a) => Program -> Bool
canCompile e = case infer e of
  Right _ -> True
  Left _ -> False

interpretables :: [Program () Double]
interpretables = [uniformProg, uniformProgMult]
prop_CanInterpret :: Property
prop_CanInterpret = forAll (elements interpretables) (\p -> monadicIO $ run (canInterpret p))

canInterpret :: Program () Double -> IO Bool
canInterpret p = do
  result <- try (evalRandIO (irInterpret p []))
  case result of
    Left (err :: SomeException) -> return False
    Right r -> return True


{-prop_interpretersEqualDensity :: Program () Double -> Double -> Property
prop_interpretersEqualDensity p sample = do
  let compilable = canCompile p
  if compilable then ioProperty $ do
      irValue <- evalRandIO $ irDensity p sample
      return $ irValue == langDensity p sample
  else
    property Discard -}

--testCompile :: Expr -> Property
--testCompile e = addWitnessesProg $ addTypeInfo $ makeMain e

testRecompile :: (Eq a, Show a, Recompilable a) => a -> Property
testRecompile inp = case recompile inp of
   Left err -> counterexample (show inp) (False === True)
   Right program -> program === inp

expressionsGen :: Gen (Expr () Double)
expressionsGen = elements (map fst expressions)

parametrizedGen :: Gen (Env () Double, Thetas Double)
parametrizedGen = do
  expr <- elements (map fst expressions)
  let maxIx = maximum $ catMaybes $ map maxThetaIx $ findThetas expr
  --  (\thExpr -> case thExpr of ThetaI _ x -> Just x otherExpr -> Nothing)
  thetas <- genThetas (maxIx + 1)
  return ([("main", expr)], thetas)

maxThetaIx :: Expr t a -> Maybe Int
maxThetaIx (ThetaI _ a x) = Just x
maxThetaIx _ = Nothing

genThetas :: Int -> Gen (Thetas Double)
genThetas = vector

findThetas :: Expr t a -> [Expr t a]
findThetas (ThetaI a b c) = [ThetaI a b c]
findThetas expr = concatMap findThetas x
  where x = getSubExprs expr

expressions :: [(Expr () Double, TypeInfo)]
expressions = [
    (testIf, makeTypeInfo {rType = TBool, pType = Integrate}),
    (testGreater, makeTypeInfo {rType = TBool, pType = Integrate}),
    (testGreater2, makeTypeInfo {rType = TBool, pType = Integrate})
  ]

epsilon :: (Show a, Ord a, Num a) => a -> a -> a -> Property
epsilon e x y =
  counterexample (show x ++ interpret res ++ show y) res
  where
    res = abs (x - y) < e
    interpret True  = " == "
    interpret False = " /= "

epsilonProb :: (Show a, Ord a, Num a) => a -> Probability a -> Probability a -> Property
epsilonProb e (DiscreteProbability x) (DiscreteProbability y) = epsilon e x y
epsilonProb e (PDF x) (PDF y) = epsilon e x y
epsilonProb _ x y = counterexample ("Mismatched probability types: " ++ show x ++ " " ++ show y) False

invariantDensity :: IO()
invariantDensity = undefined


propInfer :: (Eq a, Show a) => Program -> Program -> Property
propInfer a b = addWitnessesProg (addTypeInfo) === b

sumsToOne :: IO Result
sumsToOne = undefined
-}
-- Two-level nesting: inner true branch has global prob 0.12*0.12=0.0144 < thresh=0.1, so it is
-- pruned by global topK but would survive local topK (local condT=0.12 > 0.1).
prop_TopKNestedPrunesDeeper :: Property
prop_TopKNestedPrunesDeeper = ioProperty $ do
  let twoLevel = Program [("main",
        ifThenElse (bernoulli 0.12)
          (ifThenElse (bernoulli 0.12) (constF 1.0) (constF 0.0))
          (constF 2.0))] [] []
  topKResult <- evalRandIO $ irDensityTopK twoLevel 0.1 (VFloat 1.0) []
  exactResult <- evalRandIO $ irDensity twoLevel (VFloat 1.0) []
  case (topKResult, exactResult) of
    (VTuple (VFloat topKP) _, VTuple exactP _) ->
      return $ counterexample ("global topK P(1.0)=" ++ show topKP ++ ", expected 0") (topKP == 0.0)
             .&&. counterexample ("exact P(1.0) should be 0.0144") (exactP `reasonablyClose` VFloat 0.0144)
    _ -> return $ counterexample "Return type was no tuple" False

-- Cross-function: accProb passes through a _prob call boundary.
-- main = if bernoulli(0.12) then inner else 2.0
-- inner = if bernoulli(0.12) then 1.0 else 0.0
-- With thresh=0.1: main's true branch has accProb=0.12, inner receives it;
-- inner's true branch has global prob 0.12*0.12=0.0144 < 0.1 → pruned, P(1.0)=0.
prop_TopKCrossFunction :: Property
prop_TopKCrossFunction = ioProperty $ do
  let crossFunc = Program
        [ ("main",  ifThenElse (bernoulli 0.12) (var "inner") (constF 2.0))
        , ("inner", ifThenElse (bernoulli 0.12) (constF 1.0) (constF 0.0)) ]
        [] []
  topKResult <- evalRandIO $ irDensityTopK crossFunc 0.1 (VFloat 1.0) []
  exactResult <- evalRandIO $ irDensity crossFunc (VFloat 1.0) []
  case (topKResult, exactResult) of
    (VTuple (VFloat topKP) _, VTuple exactP _) ->
      return $ counterexample ("global topK P(1.0)=" ++ show topKP ++ ", expected 0") (topKP == 0.0)
             .&&. counterexample ("exact P(1.0) should be 0.0144") (exactP `reasonablyClose` VFloat 0.0144)
    _ -> return $ counterexample "Return type was no tuple" False

-- Threshold=0 never prunes any branch, so results must match exact inference.
prop_TopKZeroThreshMatchesExact :: Property
prop_TopKZeroThreshMatchesExact = forAll (elements correctProbValuesTestCases) checkTopKZeroMatchesExact

checkTopKZeroMatchesExact :: (Program, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkTopKZeroMatchesExact (p, inp, params, _) = ioProperty $ do
  topKResult <- evalRandIO $ irDensityTopK p 0.0 inp params
  exactResult <- evalRandIO $ irDensity p inp params
  case (topKResult, exactResult) of
    (VTuple topKP topKD, VTuple exactP exactD) ->
      return $ topKP `reasonablyClose` exactP .&&. topKD `reasonablyClose` exactD
    _ -> return $ counterexample "Return type was no tuple" False

-- Pruning can only zero out branches, never inflate probability above the exact value.
prop_TopKNeverInflates :: Property
prop_TopKNeverInflates = forAll (elements correctProbValuesTestCases) (checkTopKNeverInflates 0.1)

checkTopKNeverInflates :: Double -> (Program, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkTopKNeverInflates thresh (p, inp, params, _) = ioProperty $ do
  topKResult <- evalRandIO $ irDensityTopK p thresh inp params
  exactResult <- evalRandIO $ irDensity p inp params
  case (topKResult, exactResult) of
    (VTuple (VFloat topKP) _, VTuple (VFloat exactP) _) ->
      return $ counterexample (show topKP ++ " > " ++ show exactP) (topKP <= exactP + 1e-9)
    _ -> return $ counterexample "Return type was no tuple" False

-- BC counts both if-else leaf branches and InjF enumerable branches.
-- testDiceAdd = plusI(dice6, dice6): for P(sum=7), all 6 die combinations are valid,
-- so without topK BC=6.  With threshold=0.2 (>1/6), accProb*(1/6)<0.2 → all 6 pruned → BC=0.
prop_TopKFewerBranches :: Property
prop_TopKFewerBranches = ioProperty $ do
  topKBCResult <- evalRandIO $ irDensityTopKBC testDiceAdd 0.2 (VInt 7) []
  noBCResult   <- evalRandIO $ irDensityBC     testDiceAdd     (VInt 7) []
  case (topKBCResult, noBCResult) of
    (VTuple _ (VTuple _ (VFloat topKBC)), VTuple _ (VTuple _ (VFloat noBC))) ->
      return $ counterexample (show topKBC ++ " >= " ++ show noBC ++ " (topK should reduce branch count when a branch is pruned)") (topKBC < noBC)
    _ -> return $ counterexample "Return type was no tuple" False

-- Higher threshold prunes more InjF enum branches: BC(high_thresh) ≤ BC(low_thresh).
-- testDiceAdd at P(sum=7): each d6 face has P=1/6.
--   threshold=0.1 (<1/6): accProb*(1/6)>0.1 → all 6 branches kept → BC=6
--   threshold=0.2 (>1/6): accProb*(1/6)<0.2 → all 6 branches pruned → BC=0
prop_TopKMonotonicBranches :: Property
prop_TopKMonotonicBranches = ioProperty $ do
  bcLow  <- evalRandIO $ irDensityTopKBC testDiceAdd 0.1 (VInt 7) []
  bcHigh <- evalRandIO $ irDensityTopKBC testDiceAdd 0.2 (VInt 7) []
  case (bcLow, bcHigh) of
    (VTuple _ (VTuple _ (VFloat lowBC)), VTuple _ (VTuple _ (VFloat highBC))) ->
      return $ counterexample (show highBC ++ " > " ++ show lowBC ++ " (higher threshold should prune at least as much)") (highBC <= lowBC)
    _ -> return $ counterexample "Return type was no tuple" False

irDensityTopKBC :: RandomGen g => Program -> Double -> IRValue -> [IRExpr] -> Rand g IRValue
irDensityTopKBC p thresh s params = IRInterpreter.generateRand (neurals p) irEnv (sampleExpr:IRConst (VFloat 1.0):params) irExpr
  where Just (irExpr, _) = probFun (lookupIREnv "main" irEnv)
        sampleExpr = IRConst s
        irEnv = envToIR defaultCompilerConfig {topKThreshold = Just thresh, countBranches = True} annotated
        annotated = (annotateAlgsProg . annotateConditionalProg) typedProg
        Right typedProg = addTypeInfo forwardChained
        forwardChained = annotateProg preAnnotated
        preAnnotated = annotateEnumsProg p

-- BC for if-else: each leaf emits 1, IfThenElse uses formula cond+left+right-1.
-- A 3-leaf if-else (if b then (if b2 then uniform else 3.0) else 1.0) should give BC=3.
-- inner: cond(1)+uniform(1)+const3(1)-1=2; outer: cond(1)+2+const1(1)-1=3.
prop_BCLeafCountIfElse :: Property
prop_BCLeafCountIfElse = ioProperty $ do
  let prog = Program [("main", ifThenElse (bernoulli 0.5) (ifThenElse (bernoulli 0.5) uniform (constF 3.0)) (constF 1.0))] [] []
  result <- evalRandIO $ irDensityBC prog (VFloat 0.5) []
  case result of
    VTuple _ (VTuple _ (VFloat bc)) -> return $ counterexample ("Expected BC=3, got " ++ show bc) (bc == 3.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- dice 6 is a pure if-else tree with 6 leaves. BC should equal 6 for any query.
-- dice1=1; dice(n)=cond(1)+constI(n)(1)+dice(n-1)-1 = dice(n-1)+1; so dice(6)=6.
prop_BCDiceIfElse :: Property
prop_BCDiceIfElse = ioProperty $ do
  result <- evalRandIO $ irDensityBC testDice (VInt 3) []
  case result of
    VTuple _ (VTuple _ (VFloat bc)) -> return $ counterexample ("Expected BC=6, got " ++ show bc) (bc == 6.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- Consistency: dice6 as if-else (BC=6) and testDiceAdd as InjF (BC=6 for P(7)) agree.
prop_BCConsistency :: Property
prop_BCConsistency = ioProperty $ do
  diceResult    <- evalRandIO $ irDensityBC testDice    (VInt 3) []
  diceAddResult <- evalRandIO $ irDensityBC testDiceAdd (VInt 7) []
  case (diceResult, diceAddResult) of
    (VTuple _ (VTuple _ (VFloat diceBC)), VTuple _ (VTuple _ (VFloat diceAddBC))) ->
      return $ counterexample ("dice BC=" ++ show diceBC ++ ", diceAdd BC=" ++ show diceAddBC ++ " (expected both=6)") (diceBC == diceAddBC)
    _ -> return $ counterexample "Return type was no tuple" False

-- dice 6 has equal 1/6 marginal probability per face regardless of tree structure.
-- Global topK therefore either prunes all branches or none:
--   threshold=0.1 (<1/6): accumulated prob of every branch is ~1/6 > 0.1 → nothing pruned, P(3)=1/6
--   threshold=0.2 (>1/6): accumulated prob of every branch is ~1/6 < 0.2 → all pruned, P(3)=0
-- Local topK would behave differently because the raw bernoulli probabilities vary by depth.
prop_TopKDiceAllOrNothing :: Property
prop_TopKDiceAllOrNothing = ioProperty $ do
  low   <- evalRandIO $ irDensityTopK testDice 0.1 (VInt 3) []
  high  <- evalRandIO $ irDensityTopK testDice 0.2 (VInt 3) []
  exact <- evalRandIO $ irDensity     testDice     (VInt 3) []
  case (low, high, exact) of
    (VTuple lowP _, VTuple (VFloat hP) _, VTuple exactP _) ->
      return $ lowP `reasonablyClose` exactP
            .&&. counterexample ("threshold=0.2 should prune all branches: P=" ++ show hP) (hP == 0.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- testDiceAdd = plusI(dice, dice): InjF enumerates discrete values of the left arg.
-- Each d6 face has P=1/6; InjF branch filter is (accProb * pLeft > threshold).
--   threshold=0.1 (<1/6): 1.0*(1/6)=0.167 > 0.1 → all enum branches kept, P(7)=6/36
--   threshold=0.2 (>1/6): 1.0*(1/6)=0.167 < 0.2 → all enum branches pruned, P(7)=0
prop_TopKInjFEnum :: Property
prop_TopKInjFEnum = ioProperty $ do
  low   <- evalRandIO $ irDensityTopK testDiceAdd 0.1 (VInt 7) []
  high  <- evalRandIO $ irDensityTopK testDiceAdd 0.2 (VInt 7) []
  exact <- evalRandIO $ irDensity     testDiceAdd     (VInt 7) []
  case (low, high, exact) of
    (VTuple lowP _, VTuple (VFloat hP) _, VTuple exactP _) ->
      return $ lowP `reasonablyClose` exactP
            .&&. counterexample ("threshold=0.2 should prune all InjF enum branches: P=" ++ show hP) (hP == 0.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- Parses testCases/dice.ppl (d4, equal P=0.25 per face) and runs it through the full
-- parsing + compilation pipeline with topK enabled.
-- Note: runProb does not thread acc_prob, so we use irDensityTopK directly after parsing.
-- threshold=0.1 (<0.25): no branch is pruned; each face should have P=0.25.
prop_TopKEndToEnd :: Property
prop_TopKEndToEnd = ioProperty $ do
  prog <- parseProgram "testCases/dice.ppl"
  results <- mapM (\v -> evalRandIO $ irDensityTopK prog 0.1 (VFloat v) []) [1.0, 2.0, 3.0, 4.0]
  return $ conjoin
    [ case r of
        VTuple p _ -> p `reasonablyClose` VFloat 0.25
        x -> counterexample ("Unexpected result shape: " ++ show x) False
    | r <- results ]

-- testConditionalLambdaBC: named deterministic selector applied to a coin-flip argument.
-- Routes through IsConditional + toIREnumerate path in IRCompiler.
-- Argument has 2 discrete values; each iteration traverses one if-else arm → BC = 2.
prop_BCConditionalLambda :: Property
prop_BCConditionalLambda = ioProperty $ do
  result <- evalRandIO $ irDensityBC testConditionalLambdaBC (VFloat 1.0) []
  case result of
    VTuple _ (VTuple _ (VFloat bc)) ->
      return $ counterexample ("Expected BC=2, got " ++ show bc) (bc == 2.0)
    _ -> return $ counterexample ("Unexpected result shape: " ++ show result) False

-- killAll coverage: a program that calls a sub-function via Var with a non-trivial
-- change-of-variables correction.  testNormalScaledViaVar uses injF "mult" with factor
-- 2.0, whose inverse derivative is 1/2.  If killAll fails to rewrite the dim extraction
-- from the sub-function result (IRTFst(IRTSnd(IRVar x)) → IRTSnd(IRVar x)), dim would
-- be 0 and the CoV factor would be skipped, giving normalPDF(1.0) instead of
-- the correct normalPDF(1.0) * 0.5.
-- P(main = 2.0) = normalPDF(1.0) * 0.5.
prop_killAllVarExtraction :: Property
prop_killAllVarExtraction = ioProperty $ do
  result <- evalRandIO $ irDensity testNormalScaledViaVar (VFloat 2.0) []
  case result of
    VTuple (VFloat p) _ ->
      return $ counterexample ("Expected normalPDF(1)*0.5≈" ++ show (normalPDF 1.0 * 0.5) ++ ", got " ++ show p)
        (abs (p - normalPDF 1.0 * 0.5) < 1e-6)
    _ -> return $ counterexample ("Unexpected shape: " ++ show result) False

-- Enabling countBranches must not alter probability values, only add a third field.
-- Verify on testDice that P(X=3) is the same with and without branch counting.
prop_BCDoesNotChangeProbability :: Property
prop_BCDoesNotChangeProbability = ioProperty $ do
  withBC    <- evalRandIO $ irDensityBC testDice (VInt 3) []
  withoutBC <- evalRandIO $ irDensity   testDice (VInt 3) []
  case (withBC, withoutBC) of
    (VTuple (VFloat pBC) _, VTuple (VFloat pNone) _) ->
      return $ counterexample
        ("P with BC=" ++ show pBC ++ " /= P without BC=" ++ show pNone)
        (abs (pBC - pNone) < 1e-9)
    _ -> return $ counterexample
      ("Unexpected result shapes: " ++ show withBC ++ ", " ++ show withoutBC) False

-- stripBranchCount structural check: when countBranches=False the prob function
-- should return a pair (prob, dim), not a triple.  We verify this by checking that
-- the interpreter result has exactly two components (VTuple _ _) and not three
-- (VTuple _ (VTuple _ _)).
-- Also exercises the killAll IRVar path: testDice's main calls the dice sub-expression
-- via Var, so killAll must rewrite IRTFst(IRTSnd(IRVar x)) → IRTSnd(IRVar x).
prop_stripBranchCountReturnShape :: Property
prop_stripBranchCountReturnShape = ioProperty $ do
  withBC    <- evalRandIO $ irDensityBC testDice (VInt 3) []
  withoutBC <- evalRandIO $ irDensity   testDice (VInt 3) []
  let isTriple (VTuple _ (VTuple _ _)) = True
      isTriple _                       = False
  return $
    counterexample ("countBranches=True should return triple, got: " ++ show withBC)
      (isTriple withBC)
    .&&.
    counterexample ("countBranches=False should return pair, got: " ++ show withoutBC)
      (case withoutBC of { VTuple _ (VTuple _ _) -> False; VTuple _ _ -> True; _ -> False })

return []


runTests :: IO Bool
runTests = $(forAllProperties) (quickCheckWithResult stdArgs { maxSuccess = 100, maxDiscardRatio = 20 })

data TestOpts = TestOpts {
  disableSpec :: Bool,
  disableInternals :: Bool,
  disableParser :: Bool,
  disableEnd2End :: Bool
}

parseTestOpts :: Parser TestOpts
parseTestOpts = TestOpts
        <$> switch
            ( long "disableSpec"
            <> short 'S'
            <> help "Disables the tests in Spec")
        <*> switch
            ( long "disableInternals"
            <> short 'I'
            <> help "Disables the internal tests")
        <*> switch
            ( long "disableParser"
            <> short 'P'
            <> help "Disables the parser tests")
        <*> switch
            ( long "disableEnd2End"
            <> short 'E'
            <> help "Disables the end2end tests")

main :: IO ()
main = runSpecifiedTests =<< execParser opts
         where
           opts = info (parseTestOpts <**> helper)
             ( fullDesc
            <> progDesc "Compiles or computes probabilistic programs"
            <> header "Haskell DPPL" )

runSpecifiedTests :: TestOpts -> IO ()
runSpecifiedTests opts = do
  a <- if disableSpec opts then return True else runTests
  b <- if disableParser opts then return True else test_parser
  c <- if disableInternals opts then return True else test_internals
  _ <- runTestTT classConstraintTests
  _ <- runTestTT (test_encodeDiscreteTuple)
  _ <- runTestTT (test_encodeFromDistribution)
  d <- if disableEnd2End opts then return True else test_end2end
  let x = a && b && c && d
  if x then
    putStrLn "Test successful!"
  else do
    putStrLn "Test failed!"
    exitWith (ExitFailure 1) --Exit with error code to let the tests fail
  --mapM_ (quickCheck . not . canCompile) uncompilables
  --checkProgs [(variableLengthS, variableLengthT),
  --             (testLetS, testLetT),
  --             (testLetNonLetS, testLetNonLetT),
  --             (testLetDS, testLetDT),
  --             (testLetTupleS, testLetTupleT),
  --             (testLetXYS, testLetXYT)]
  -- quickCheck $ compilesTo [("main", fst $ head expressions)] (snd $ head expressions)
  -- quickCheck $ forAll expressionsGen (\expr -> compilesTo [("main", expr)] $ fromJust $ lookup expr expressions)
  -- quickCheck $ forAll parametrizedGen $ discreteProbAlignment 1000
  -- putStrLn "all tests done"
