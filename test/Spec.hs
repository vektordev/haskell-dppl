--{-# LANGUAGE EmptyCase #-}
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
--import Lib
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.IntermediateRepresentation
import SPLL.Validator
import Data.Maybe (fromJust, catMaybes)
import Control.Monad.Random.Lazy (Random, RandomGen, Rand, evalRandIO)
--import ArbitrarySPLL
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
import SPLL.Parser
import TestParser (parserTests)
import TestInternals (internalsTests)
import TestEncodeProperties (encodeTests)
import End2EndTesting (end2endTests)
import TestCaseParser (parseProgram)
import SPLL.Prelude
import qualified SPLL.CodeGenPyTorch
import Data.List (isInfixOf)


thetaTreeExample :: IRValue
thetaTreeExample = VThetaTree (ThetaTree [0, 1, 2, 3] [ThetaTree [4, 5, 6, 7] [], ThetaTree [8, 9, 10, 11] [], ThetaTree [12, 13, 14, 15] []])

flatTree :: [Double] -> [IRValue]
flatTree a = [VThetaTree (ThetaTree a [])]

normalPDF :: Double -> Double
normalPDF x = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)

normalCDF :: Double -> Double
normalCDF x = (1/2)*(1 + erf (x/sqrt (2)))

correctProbValuesTestCases :: [(Program, IRValue, [IRValue], (IRValue, IRValue))]
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
                               (gaussLists, constructVList [VFloat 0, VFloat 0, VFloat 0], [VThetaTree (ThetaTree [0.5, 1, 0] [])], (VFloat $ (normalPDF 0) * (normalPDF 0) * (normalPDF 0) / 16, VFloat 3)),
                               --(testPartialInjF, VFloat 5.5, [], (VFloat 1, VFloat 1))]
                               (testInjFRenaming, VFloat 5.5, [], (VFloat 1, VFloat 1)),
                               (gaussLists, constructVList [VFloat 0, VFloat 0, VFloat 0], [VThetaTree (ThetaTree [0.5, 1, 0] [])], (VFloat $ (normalPDF 0) * (normalPDF 0) * (normalPDF 0) / 16, VFloat 3)),
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

correctIntegralValuesTestCases :: [(Program, IRValue, IRValue, [IRValue], (IRValue, IRValue))]
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
prop_TopK = once $ ioProperty $ do
  let actualOutput0 = irDensity (topKConf 0.1) testTopK (VFloat 0) []
  let actualOutput1 = irDensity (topKConf 0.1) testTopK (VFloat 1) []
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

checkValidPrograms :: (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkValidPrograms (p, _, _, _) = case validateProgram p of
  Right _ -> property True
  Left err -> counterexample err False

checkInvalidPrograms :: Program -> Property
checkInvalidPrograms p = case validateProgram p of
  Left _ -> property True
  Right _ -> counterexample "Program validates even though it should not" False


checkProbTestCase :: (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkProbTestCase (p, inp, params, (out, VFloat outDim)) = ioProperty $ do
  let actualOutput = irDensity defaultCompilerConfig p inp params
  case actualOutput of
    VTuple a (VFloat d) -> return $ a `reasonablyClose` out .&&. d === outDim
    _ -> return $ counterexample "Return type was no tuple" False

checkIntegralTestCase :: (Program, IRValue, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkIntegralTestCase (p, low, high, params, (out, outDim)) = ioProperty $ do
  let actualOutput = irIntegral defaultCompilerConfig p low high params
  case actualOutput of
    VTuple a aDim -> return $ a `reasonablyClose` out .&&. aDim === outDim
    _ -> return $ counterexample "Return type was no tuple" False

--TODO better bounds for Integral
checkIntegralConverges :: (Program, IRValue, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkIntegralConverges (p, VFloat a, VFloat b, params, _) = ioProperty $ do
  let actualOutput = irIntegral defaultCompilerConfig p (VFloat (-9999999)) (VFloat 9999999) params
  case actualOutput of
    VTuple a (VFloat _) -> return $ a `reasonablyClose` VFloat 1
    _ -> return $ counterexample "Return type was no tuple" False
checkIntegralConverges _ = False ==> False

checkZeroWidthIntegral :: (Program, IRValue, IRValue, [IRValue], IRValue) -> Property
checkZeroWidthIntegral (p, lower, _, params, _) = ioProperty $ do
  let integralOutput = irIntegral defaultCompilerConfig p lower lower params
  let probOutput = irDensity defaultCompilerConfig p lower params
  case (integralOutput, probOutput) of
    (VTuple a (VFloat _), VTuple b (VFloat _)) -> return $ a `reasonablyClose` b
    _ -> return $ counterexample "Return type was no tuple" False

checkTopKInterprets :: (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKInterprets (p, inp, params, _) = ioProperty $ do
  let actualOutput = irDensity (topKConf 0.05) p inp params
  return $ actualOutput `reasonablyClose` actualOutput  -- No clue what the correct value should be here. Just test that is interprets to any value

checkProbTestCasesWithBC :: (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkProbTestCasesWithBC (p, inp, params, (out, VFloat outDim)) = ioProperty $ do
  let actualOutput = irDensity bcConf p inp params
  case actualOutput of
    VTuple a (VTuple (VFloat d) (VFloat _)) -> return $ a `reasonablyClose` out .&&. d === outDim
    _ -> return $ counterexample "Return type was no tuple" False

checkProbAny :: (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkProbAny (p, _, params, _) = ioProperty $ do
  let actualOutput = irDensity defaultCompilerConfig p VAny params
  case actualOutput of
    VTuple a (VFloat d) -> return $ a === VFloat 1
    _ -> return $ counterexample "Return type was no tuple" False

--prop_CheckProbTestCases = foldr (\(p, inp, out) acc -> do
--  checkProbTestCase p inp out .&&. acc) (True===True) correctProbValuesTestCases

-- All test compilation goes through the public SPLL.Prelude entry points, so the
-- tests exercise exactly the pipeline production uses. The CompilerConfig argument
-- selects the topK / branch-counting variants.
topKConf :: Double -> CompilerConfig
topKConf thresh = defaultCompilerConfig {topKThreshold = Just thresh}

topKBCConf :: Double -> CompilerConfig
topKBCConf thresh = (topKConf thresh) {countBranches = True}

bcConf :: CompilerConfig
bcConf = defaultCompilerConfig {countBranches = True}

irDensity :: CompilerConfig -> Program -> IRValue -> [IRValue] -> IRValue
irDensity conf p s params = either error id $ runProb conf p params s

irIntegral :: CompilerConfig -> Program -> IRValue -> IRValue -> [IRValue] -> IRValue
irIntegral conf p low high params = either error id $ do
  compiled <- compile conf p
  highVal <- runIntegC p compiled params high
  lowVal <- runIntegC p compiled params low
  case (highVal, lowVal) of
    (VTuple (VFloat highP) (VFloat _),
     VTuple (VFloat lowP)  (VFloat lowD)) -> return $ VTuple (VFloat (highP - lowP)) (VFloat lowD)
    _ -> Left "irIntegral: unexpected IRValue shape"

reasonablyClose :: IRValue -> IRValue -> Property
reasonablyClose (VFloat a) (VFloat b) = counterexample (show a ++ "/=" ++ show b) (property $ abs (a - b) <= 1e-5)
reasonablyClose a b = a === b

--Sample PDF against expected PDF. Retiry specific number of times with double the samples each time
testSamplingProb :: Double -> Int -> Int -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
testSamplingProb epsilon samples retries (p, VFloat inp, params, (VFloat out, VFloat outDim))  = ioProperty $ evalRandIO $ do
  let gen = either error id (runGen defaultCompilerConfig p params)
  endlessSamples <- sequence (repeat (gen >>= \(VFloat x) -> return x)) -- Generates an endless stream of samples
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
  let gen = either error id (runGen defaultCompilerConfig p params)
  endlessSamples <- sequence (repeat (gen >>= \(VInt x) -> return x)) -- Generates an endless stream of samples
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
  let gen = either error id (runGen defaultCompilerConfig p params)
  endlessSamples <- sequence (repeat (gen >>= \(VTuple (VFloat x1) (VFloat x2)) -> return (x1, x2))) -- Generates an endless stream of samples
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
  let gen = either error id (runGen defaultCompilerConfig p params)
  endlessSamples <- sequence (repeat (gen >>= \(VList l) -> return l)) -- Generates an endless stream of samples
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
prop_TopKNestedPrunesDeeper = once $ ioProperty $ do
  let twoLevel = Program [("main",
        ifThenElse (bernoulli 0.12)
          (ifThenElse (bernoulli 0.12) (constF 1.0) (constF 0.0))
          (constF 2.0))] [] []
  let topKResult = irDensity (topKConf 0.1) twoLevel (VFloat 1.0) []
  let exactResult = irDensity defaultCompilerConfig twoLevel (VFloat 1.0) []
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
prop_TopKCrossFunction = once $ ioProperty $ do
  let crossFunc = Program
        [ ("main",  ifThenElse (bernoulli 0.12) (var "inner") (constF 2.0))
        , ("inner", ifThenElse (bernoulli 0.12) (constF 1.0) (constF 0.0)) ]
        [] []
  let topKResult = irDensity (topKConf 0.1) crossFunc (VFloat 1.0) []
  let exactResult = irDensity defaultCompilerConfig crossFunc (VFloat 1.0) []
  case (topKResult, exactResult) of
    (VTuple (VFloat topKP) _, VTuple exactP _) ->
      return $ counterexample ("global topK P(1.0)=" ++ show topKP ++ ", expected 0") (topKP == 0.0)
             .&&. counterexample ("exact P(1.0) should be 0.0144") (exactP `reasonablyClose` VFloat 0.0144)
    _ -> return $ counterexample "Return type was no tuple" False

-- Threshold=0 never prunes any branch, so results must match exact inference.
prop_TopKZeroThreshMatchesExact :: Property
prop_TopKZeroThreshMatchesExact = forAll (elements correctProbValuesTestCases) checkTopKZeroMatchesExact

checkTopKZeroMatchesExact :: (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKZeroMatchesExact (p, inp, params, _) = ioProperty $ do
  let topKResult = irDensity (topKConf 0.0) p inp params
  let exactResult = irDensity defaultCompilerConfig p inp params
  case (topKResult, exactResult) of
    (VTuple topKP topKD, VTuple exactP exactD) ->
      return $ topKP `reasonablyClose` exactP .&&. topKD `reasonablyClose` exactD
    _ -> return $ counterexample "Return type was no tuple" False

-- Pruning can only zero out branches, never inflate probability above the exact value.
prop_TopKNeverInflates :: Property
prop_TopKNeverInflates = forAll (elements correctProbValuesTestCases) (checkTopKNeverInflates 0.1)

checkTopKNeverInflates :: Double -> (Program, IRValue, [IRValue], (IRValue, IRValue)) -> Property
checkTopKNeverInflates thresh (p, inp, params, _) = ioProperty $ do
  let topKResult = irDensity (topKConf thresh) p inp params
  let exactResult = irDensity defaultCompilerConfig p inp params
  case (topKResult, exactResult) of
    (VTuple (VFloat topKP) _, VTuple (VFloat exactP) _) ->
      return $ counterexample (show topKP ++ " > " ++ show exactP) (topKP <= exactP + 1e-9)
    _ -> return $ counterexample "Return type was no tuple" False

-- BC counts both if-else leaf branches and InjF enumerable branches.
-- testDiceAdd = plusI(dice6, dice6): for P(sum=7), all 6 die combinations are valid,
-- so without topK BC=6.  With threshold=0.2 (>1/6), accProb*(1/6)<0.2 → all 6 pruned → BC=0.
prop_TopKFewerBranches :: Property
prop_TopKFewerBranches = once $ ioProperty $ do
  let topKBCResult = irDensity (topKBCConf 0.2) testDiceAdd (VInt 7) []
  let noBCResult   = irDensity bcConf           testDiceAdd (VInt 7) []
  case (topKBCResult, noBCResult) of
    (VTuple _ (VTuple _ (VFloat topKBC)), VTuple _ (VTuple _ (VFloat noBC))) ->
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
    (VTuple _ (VTuple _ (VFloat lowBC)), VTuple _ (VTuple _ (VFloat highBC))) ->
      return $ counterexample (show highBC ++ " > " ++ show lowBC ++ " (higher threshold should prune at least as much)") (highBC <= lowBC)
    _ -> return $ counterexample "Return type was no tuple" False

-- BC for if-else: each leaf emits 1, IfThenElse uses formula cond+left+right-1.
-- A 3-leaf if-else (if b then (if b2 then uniform else 3.0) else 1.0) should give BC=3.
-- inner: cond(1)+uniform(1)+const3(1)-1=2; outer: cond(1)+2+const1(1)-1=3.
prop_BCLeafCountIfElse :: Property
prop_BCLeafCountIfElse = once $ ioProperty $ do
  let prog = Program [("main", ifThenElse (bernoulli 0.5) (ifThenElse (bernoulli 0.5) uniform (constF 3.0)) (constF 1.0))] [] []
  let result = irDensity bcConf prog (VFloat 0.5) []
  case result of
    VTuple _ (VTuple _ (VFloat bc)) -> return $ counterexample ("Expected BC=3, got " ++ show bc) (bc == 3.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- dice 6 is a pure if-else tree with 6 leaves. BC should equal 6 for any query.
-- dice1=1; dice(n)=cond(1)+constI(n)(1)+dice(n-1)-1 = dice(n-1)+1; so dice(6)=6.
prop_BCDiceIfElse :: Property
prop_BCDiceIfElse = once $ ioProperty $ do
  let result = irDensity bcConf testDice (VInt 3) []
  case result of
    VTuple _ (VTuple _ (VFloat bc)) -> return $ counterexample ("Expected BC=6, got " ++ show bc) (bc == 6.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- Consistency: dice6 as if-else (BC=6) and testDiceAdd as InjF (BC=6 for P(7)) agree.
prop_BCConsistency :: Property
prop_BCConsistency = once $ ioProperty $ do
  let diceResult    = irDensity bcConf testDice    (VInt 3) []
  let diceAddResult = irDensity bcConf testDiceAdd (VInt 7) []
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
prop_TopKDiceAllOrNothing = once $ ioProperty $ do
  let low   = irDensity (topKConf 0.1)        testDice (VInt 3) []
  let high  = irDensity (topKConf 0.2)        testDice (VInt 3) []
  let exact = irDensity defaultCompilerConfig testDice (VInt 3) []
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
prop_TopKInjFEnum = once $ ioProperty $ do
  let low   = irDensity (topKConf 0.1)        testDiceAdd (VInt 7) []
  let high  = irDensity (topKConf 0.2)        testDiceAdd (VInt 7) []
  let exact = irDensity defaultCompilerConfig testDiceAdd (VInt 7) []
  case (low, high, exact) of
    (VTuple lowP _, VTuple (VFloat hP) _, VTuple exactP _) ->
      return $ lowP `reasonablyClose` exactP
            .&&. counterexample ("threshold=0.2 should prune all InjF enum branches: P=" ++ show hP) (hP == 0.0)
    _ -> return $ counterexample "Return type was no tuple" False

-- Parses testCases/dice.ppl (d4, equal P=0.25 per face) and runs it through the full
-- parsing + compilation pipeline with topK enabled, via the public runProb API
-- (which threads the initial acc_prob for topK-compiled programs).
-- threshold=0.1 (<0.25): no branch is pruned; each face should have P=0.25.
prop_TopKEndToEnd :: Property
prop_TopKEndToEnd = once $ ioProperty $ do
  prog <- parseProgram "testCases/dice.ppl"
  let results = map (\v -> irDensity (topKConf 0.1) prog (VFloat v) []) [1.0, 2.0, 3.0, 4.0]
  return $ conjoin
    [ case r of
        VTuple p _ -> p `reasonablyClose` VFloat 0.25
        x -> counterexample ("Unexpected result shape: " ++ show x) False
    | r <- results ]

-- testConditionalLambdaBC: named deterministic selector applied to a coin-flip argument.
-- Routes through IsConditional + toIREnumerate path in IRCompiler.
-- Argument has 2 discrete values; each iteration traverses one if-else arm → BC = 2.
prop_BCConditionalLambda :: Property
prop_BCConditionalLambda = once $ ioProperty $ do
  let result = irDensity bcConf testConditionalLambdaBC (VFloat 1.0) []
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
prop_killAllVarExtraction = once $ ioProperty $ do
  let result = irDensity defaultCompilerConfig testNormalScaledViaVar (VFloat 2.0) []
  case result of
    VTuple (VFloat p) _ ->
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
prop_stripBranchCountReturnShape = once $ ioProperty $ do
  let withBC    = irDensity bcConf testDice (VInt 3) []
  let withoutBC = irDensity defaultCompilerConfig testDice (VInt 3) []
  let isTriple (VTuple _ (VTuple _ _)) = True
      isTriple _                       = False
  return $
    counterexample ("countBranches=True should return triple, got: " ++ show withBC)
      (isTriple withBC)
    .&&.
    counterexample ("countBranches=False should return pair, got: " ++ show withoutBC)
      (case withoutBC of { VTuple _ (VTuple _ _) -> False; VTuple _ _ -> True; _ -> False })

-- When topKThreshold is set, IREnv should contain exactly one constant named TOP_K_CUTOFF
-- with the value matching the config.
prop_TopKConstantPresentInEnv :: Property
prop_TopKConstantPresentInEnv = once $ ioProperty $ do
  let conf = defaultCompilerConfig { topKThreshold = Just 0.005 }
      Right irEnv = compile conf testDice
      IREnv _ _ consts = irEnv
  return $ case lookup "TOP_K_CUTOFF" consts of
    Just (VFloat v) -> counterexample ("Expected 0.005, got " ++ show v) (abs (v - 0.005) < 1e-12)
    Just other      -> counterexample ("Expected VFloat, got " ++ show other) False
    Nothing         -> counterexample "TOP_K_CUTOFF constant absent from IREnv" False

-- When topKThreshold is Nothing, no TOP_K_CUTOFF constant should appear in IREnv.
prop_TopKConstantAbsentWithoutFlag :: Property
prop_TopKConstantAbsentWithoutFlag = once $ ioProperty $ do
  let Right irEnv = compile defaultCompilerConfig testDice
      IREnv _ _ consts = irEnv
  return $ counterexample "TOP_K_CUTOFF should not appear when topK is disabled"
    (isNothing (lookup "TOP_K_CUTOFF" consts))
  where isNothing Nothing = True; isNothing _ = False

-- The generated Python should contain a plain assignment `TOP_K_CUTOFF = <value>`,
-- not a class definition.
prop_TopKPythonConstantIsPlainAssignment :: Property
prop_TopKPythonConstantIsPlainAssignment = once $ ioProperty $ do
  let conf = defaultCompilerConfig { topKThreshold = Just 0.001 }
      Right irEnv = compile conf testDice
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
      Right irEnv = compile conf testDice
      pyLines = SPLL.CodeGenPyTorch.generateFunctions True irEnv
      assignmentLines = filter ("TOP_K_CUTOFF = " `isInfixOf`) pyLines
  return $ case assignmentLines of
    [line] -> counterexample ("Assignment line: " ++ line)
                (show thresh `isInfixOf` line)
    other  -> counterexample ("Expected exactly one assignment line, got: " ++ show other) False

-- The interpreter must resolve IRVar "TOP_K_CUTOFF" via the constant in IREnv:
-- a topK compile with threshold=0.001 on testDice should agree with exact inference
-- (all branches kept since 1/6 >> 0.001).
prop_TopKConstantResolvedByInterpreter :: Property
prop_TopKConstantResolvedByInterpreter = once $ ioProperty $ do
  let withTopK = irDensity (topKConf 0.001)      testDice (VInt 3) []
  let exact    = irDensity defaultCompilerConfig testDice (VInt 3) []
  case (withTopK, exact) of
    (VTuple topKP _, VTuple exactP _) ->
      return $ topKP `reasonablyClose` exactP
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
  defaultMain $ testGroup "Tests"
    [ specTests
    , parserTests
    , internalsTests
    , encodeTests
    , e2e
    ]
