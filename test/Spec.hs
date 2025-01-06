{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

import Test.QuickCheck
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
import IRInterpreter
import Data.Maybe (fromJust, catMaybes)
import Control.Monad.Random.Lazy (Random, RandomGen, Rand, evalRandIO)
import SPLL.Typing.Infer
import SPLL.Typing.Witnessing
import SpecExamples
--import ArbitrarySPLL
import Control.Exception.Base (SomeException, try)
import Test.QuickCheck.Monadic (monadicIO, run, assert)
import Test.QuickCheck.Property (failed, reason)
import Debug.Trace (trace, traceShowId, traceId)
import SPLL.Lang.Lang (Value)
import Control.Monad.Supply
import Data.Foldable
import Data.Number.Erf (erf)
import Numeric.AD (grad', auto)
import Numeric.AD.Internal.Reverse (Reverse, Tape)
import Data.Reflection (Reifies)
import Data.Bifunctor (second)
import SPLL.Parser
import TestParser
import TestInternals
import SPLL.Prelude


-- Generalizing over different compilation stages, we can fit all "this typing is what the compiler would find" cases.
class Recompilable a where
  recompile :: a -> Either CompileError a

untypeP :: Program -> Program
untypeP (Program defs neuralDecl) = Program (map (\(a,b) -> (a, untypeE b)) defs) neuralDecl

untypeE :: Expr -> Expr
untypeE = tMap (const makeTypeInfo)

instance Recompilable Program where
  recompile = infer . untypeP

instance Recompilable Expr where
  recompile e = case inferNoWit $ makeMain $ untypeE e of
    Right (Program [("main", d)] _) -> Right d
    Left x -> Left x
    Right (Program _ _) -> error "unexpected error when recompiling Expr TypeInfo."

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
                               (uniformNegPlus, VFloat (-4.5), [], (VFloat 1, VFloat 1)),
                               (testList, VList [VFloat 0.25, VFloat 0], [], (VFloat $ normalPDF 0 * 2, VFloat 2)),
                               (simpleTuple, VTuple (VFloat 0.25) (VFloat 0), [], (VFloat $ normalPDF 0 * 2, VFloat 2)),
                               (uniformIfProg, VFloat 0.5, [], (VFloat 0.5, VFloat 1)),
                               (constantProg, VFloat 2, [], (VFloat 1, VFloat 0)),
                               (uniformExp, VFloat $ exp 4.5, [], (VFloat $ 1 / exp 4.5, VFloat 1)),
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
                               (testDiceAdd, VInt 1, [], (VFloat 0, VFloat 0)),
                               (testDimProb, VFloat 0.5, [], (VFloat 0.4, VFloat 0)),
                               (testDimProb, VFloat 0.0, [], (VFloat (0.6 * 0.39894228040143265), VFloat 1)),
                               (gaussLists, VList [VFloat 0, VFloat 0, VFloat 0], [IRConst $ VThetaTree (ThetaTree [0.5, 1, 0] [])], (VFloat $ (normalPDF 0) * (normalPDF 0) * (normalPDF 0) / 16, VFloat 3))]

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
                                (testList, VList [VFloat 0, VFloat (-1)], VList [VFloat 0.25, VFloat 1], [], (VFloat $ (normalCDF 1 - normalCDF (-1)) * 0.5, VFloat 0)),
                                (simpleTuple, VTuple (VFloat 0) (VFloat (-1)), VTuple (VFloat 0.25) (VFloat 1), [], (VFloat $ (normalCDF 1 - normalCDF (-1)) * 0.5, VFloat 0)),
                                (simpleTuple, VTuple (VFloat 0) (VFloat 0), VTuple (VFloat 0.25) (VFloat 0), [], (VFloat $ normalPDF 0 * 0.5, VFloat 1)),
                                (simpleTuple, VTuple (VFloat 0) (VFloat 0), VTuple (VFloat 0) (VFloat 1), [], (VFloat $ (normalCDF 1 - normalCDF 0) * 2, VFloat 1)),
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
                                (gaussLists, VList [VFloat 0, VFloat 0, VFloat 0], VList [VFloat 1, VFloat 2, VFloat 3], [IRConst $ VThetaTree (ThetaTree [0.5, 1, 0] [])], (VFloat $ ((normalCDF 1) - (normalCDF 0)) * ((normalCDF 2) - (normalCDF 0)) * ((normalCDF 3) - (normalCDF 0)) / 16, VFloat 0))]

                                  --(testLambdaParameter, VFloat 9, VFloat 11, [], VFloat 1.0)]
                                  --(testCallLambdaAdvanced, VFloat 2, VFloat 3, [], VFloat 1.0),
                                  --(testLetIn, VFloat 1.5, VFloat 2, [], VFloat 0.5)]

noTopKConfig :: CompilerConfig
noTopKConfig = CompilerConfig Nothing False 0

prop_CheckProbTestCases :: Property
prop_CheckProbTestCases = forAll (elements correctProbValuesTestCases) checkProbTestCase

prop_CheckProbTestCasesSample :: Property
prop_CheckProbTestCasesSample = forAll (elements correctProbValuesTestCases) (testSamplingProb 0.05 10000 5)

prop_CheckIntegralTestCases :: Property
prop_CheckIntegralTestCases = forAll (elements correctIntegralValuesTestCases) checkIntegralTestCase

prop_CheckIntegralConverges :: Property
prop_CheckIntegralConverges = forAll (elements correctIntegralValuesTestCases) checkIntegralConverges

--Not yet working
prop_CheckZeroWidthIntegrals :: Property
prop_CheckZeroWidthIntegrals = forAll (elements [(testInjF, VFloat 0, VFloat 1, [], VFloat 0.5)]) checkZeroWidthIntegral

prop_CheckTopKInterprets :: Property
prop_CheckTopKInterprets = forAll (elements correctProbValuesTestCases) checkTopKInterprets

prop_CheckProbTestCasesWithBC :: Property
prop_CheckProbTestCasesWithBC = forAll (elements correctProbValuesTestCases) checkProbTestCasesWithBC

prop_CheckInjFEqual :: Property
prop_CheckInjFEqual = forAll (elements correctProbValuesTestCases) checkInjFEqual

prop_TopK :: Property
prop_TopK = ioProperty $ do
  actualOutput0 <- evalRandIO $ irDensityTopK testTopK 0.1 (VFloat 0) []
  actualOutput1 <- evalRandIO $ irDensityTopK testTopK 0.1 (VFloat 1) []
  case (actualOutput0, actualOutput1) of
    (VTuple a (VFloat _), VTuple b (VFloat _)) -> return $ (b == VFloat 0.95) && (a == VFloat 0)
    _ -> return False

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

checkInjFEqual :: (Program, IRValue, [IRExpr], (IRValue, IRValue)) -> Property
checkInjFEqual (p, inp, params, (_, _)) = ioProperty $ do
  actualOutput <- evalRandIO $ irDensityBC p inp params
  actualOutputInjF <- evalRandIO $ irDensityBC (preprocessToInjFProg p) inp params
  case (actualOutput, actualOutputInjF) of
    (VTuple a aDim, VTuple b bDim) -> return $ a `reasonablyClose` b .&&. aDim === bDim
    _ -> return $ counterexample "Return type was no tuple" False

--prop_CheckProbTestCases = foldr (\(p, inp, out) acc -> do
--  checkProbTestCase p inp out .&&. acc) (True===True) correctProbValuesTestCases

irDensityTopK :: RandomGen g => Program -> Double -> IRValue -> [IRExpr]-> Rand g IRValue
irDensityTopK p thresh s params = IRInterpreter.generateRand irEnv irEnv (sampleExpr:params) irExpr
  where Just irExpr = lookup "main_prob" irEnv
        sampleExpr = IRConst s
        irEnv = envToIR (CompilerConfig (Just thresh) False 0) annotated
        annotated = annotateAlgsProg typedProg
        typedProg = addTypeInfo preAnnotated
        preAnnotated = annotateEnumsProg p

irDensityBC :: RandomGen g => Program -> IRValue -> [IRExpr]-> Rand g IRValue
irDensityBC p s params = IRInterpreter.generateRand irEnv irEnv (sampleExpr:params) irExpr
  where Just irExpr = lookup "main_prob" irEnv
        sampleExpr = IRConst s
        irEnv = envToIR (CompilerConfig Nothing True 0) annotated
        annotated = annotateAlgsProg typedProg
        typedProg = addTypeInfo preAnnotated
        preAnnotated = annotateEnumsProg p

irDensity :: RandomGen g => Program -> IRValue -> [IRExpr] -> Rand g IRValue
irDensity p s params = IRInterpreter.generateRand irEnv irEnv (sampleExpr:params) irExpr
  where Just irExpr = lookup "main_prob" irEnv
        sampleExpr = IRConst s
        irEnv = envToIR noTopKConfig annotated
        annotated = annotateAlgsProg typedProg
        typedProg = addTypeInfo preAnnotated
        preAnnotated = annotateEnumsProg p

irIntegral :: RandomGen g => Program -> IRValue -> IRValue -> [IRExpr] -> Rand g IRValue
irIntegral p low high params = IRInterpreter.generateRand irEnv irEnv (lowExpr:highExpr:params) irExpr
  where Just irExpr = lookup "main_integ" irEnv
        lowExpr = IRConst low
        highExpr = IRConst high
        irEnv = envToIR noTopKConfig annotated
        annotated = annotateAlgsProg typedProg
        typedProg = addTypeInfo preAnnotated
        preAnnotated = annotateEnumsProg p

irGen :: RandomGen g => Program -> [IRExpr] -> Rand g IRValue
irGen p params = IRInterpreter.generateRand irEnv irEnv params irExpr
  where Just irExpr = lookup "main_gen" irEnv
        irEnv = envToIR noTopKConfig annotated
        annotated = annotateAlgsProg typedProg
        typedProg = addTypeInfo preAnnotated
        preAnnotated = annotateEnumsProg p

preprocessToInjFProg :: Program -> Program
preprocessToInjFProg p@Program{functions=f} = p{functions=map (second preprocessToInjF) f}

preprocessToInjF :: Expr -> Expr
preprocessToInjF (PlusF t a b) = InjF t "plus" [preprocessToInjF a, preprocessToInjF b]
preprocessToInjF (PlusI t a b) = InjF t "plusI" [preprocessToInjF a, preprocessToInjF b]
preprocessToInjF (MultF t a b) = InjF t "mult" [preprocessToInjF a, preprocessToInjF b]
preprocessToInjF (MultI t a b) = InjF t "multI" [preprocessToInjF a, preprocessToInjF b]
preprocessToInjF (NegF t a) = InjF t "neg" [preprocessToInjF a]
preprocessToInjF x = x

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
  let samplesInRange = map (\l -> length l == length inp && all (\(VFloat x, VFloat y) -> abs (x - y) <= epsilon/2 ) (zip l inp)) endlessSamples   -- Use the maximum norm
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
        irEnv = envToIR noTopKConfig annotated
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


{-prop_CDFGradIsPDF :: Property
prop_CDFGradIsPDF = forAll (elements correctIntegralValuesTestCases)(\(p, _, high, thetas, _) -> ioProperty $ do
    let irExpr = runSupply (toIRIntegrate main (IRConst $ VFloat (-9999999)) (IRConst high)) (+1) 1
        Just main = lookup "main" annotated
        irEnv = envToIR annotated
        annotated = map (\(a,b) -> (a, annotate b)) env
        env = progToEnv typedProg
        typedProg = addTypeInfo p
    grad' $ evalRandIO $ IRInterpreter.generate (autoEnv irEnv) irEnv thetas [] (autoIRExpr irExpr))

autoIRExpr :: (Num a, Reifies s Tape) => IRExpr -> IRExpr (Reverse s a)
autoIRExpr e = irMap auto e-}


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
return []


runTests :: IO Bool
runTests = $quickCheckAll


main :: IO ()
main = do
  a <- runTests
  b <- test_parser
  c <- test_internals
  let x = a && b && c
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
