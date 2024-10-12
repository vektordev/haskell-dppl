{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

import Test.QuickCheck

import SPLL.Examples
--import Lib
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Typing.Typing
import SPLL.Analysis
import SPLL.IntermediateRepresentation
import SPLL.IRCompiler
import IRInterpreter
import Data.Maybe (fromJust, catMaybes)
import Control.Monad.Random.Lazy (Random, RandomGen, Rand, evalRandIO)
import SPLL.Typing.PInferBranched
import SPLL.Typing.Infer
import SPLL.Typing.Witnessing
import SpecExamples
--import ArbitrarySPLL
import Control.Exception.Base (SomeException, try)
import Test.QuickCheck.Monadic (monadicIO, run, assert)
import Test.QuickCheck.Property (failed, reason)
import Debug.Trace (trace)
import SPLL.Lang.Lang (Value)
import Control.Monad.Supply
import Data.Foldable
import Data.Number.Erf (erf)
import Numeric.AD (grad', auto)
import Numeric.AD.Internal.Reverse (Reverse, Tape)
import Data.Reflection (Reifies)

-- Generalizing over different compilation stages, we can fit all "this typing is what the compiler would find" cases.
class Recompilable a where
  recompile :: a -> Either CompileError a

untypeP :: Program a -> Program a
untypeP (Program defs neuralDecl) = Program (map (\(a,b) -> (a, untypeE b)) defs) neuralDecl

untypeE :: Expr a -> Expr a
untypeE = tMap (const makeTypeInfo)

instance Show a => Recompilable (Program a) where
  recompile = infer . untypeP

instance Show a => Recompilable (Expr a) where
  recompile e = case inferNoWit $ makeMain $ untypeE e of
    Right (Program [("main", d)] _) -> Right d
    Left x -> Left x
    Right (Program _ _) -> error "unexpected error when recompiling Expr TypeInfo a."

thetaTreeExample :: IRExpr Double
thetaTreeExample = IRConst (VThetaTree (ThetaTree [0, 1, 2, 3] [ThetaTree [4, 5, 6, 7] [], ThetaTree [8, 9, 10, 11] [], ThetaTree [12, 13, 14, 15] []]))

flatTree :: Eq a => [a] -> [IRExpr a]
flatTree a = [IRConst (VThetaTree (ThetaTree a []))]

normalPDF :: Double -> Double
normalPDF x = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)

normalCDF :: Double -> Double
normalCDF x = (1/2)*(1 + erf(x/sqrt(2)))
    
correctProbValuesTestCases :: [(Program Double, Value Double, [IRExpr Double], Value Double)]
correctProbValuesTestCases = [(uniformProg, VFloat 0.5, [], VFloat 1.0),
                              (normalProg, VFloat 0.5, [], VFloat $ normalPDF 0.5),
                              (uniformProgMult, VFloat (-0.25), [], VFloat 2),
                              (normalProgMult, VFloat (-1), [], VFloat (normalPDF (-2) * 2)),
                              (uniformNegPlus, VFloat (-4.5), [], VFloat 1),
                              (testList, VList [VFloat 0.25, VFloat 0], [], VFloat $ normalPDF 0 * 2),
                              (simpleTuple, VTuple (VFloat 0.25) (VFloat 0), [], VFloat $ normalPDF 0 * 2),
                              (uniformIfProg, VFloat 0.5, [], VFloat 0.5),
                              (constantProg, VFloat 2, [], VFloat 1),
                              
                              (uniformExp, VFloat $ exp 4.5, [], VFloat $ 1/exp 4.5),
                              (testInjF, VFloat 1.5, [], VFloat 0.5),
                              (testInjF2, VFloat 3, [], VFloat 0.5),
                              (testTheta, VFloat 1.5, flatTree [1.5], VFloat 1),
                              (testTheta, VFloat 1.5, flatTree [1], VFloat 0),
                              (testThetaTree, VFloat 11, [thetaTreeExample], VFloat 1),
                              --(testAnd, VBool True, [], VFloat 0.25),
                              --(testOr, VBool True, [], VFloat 0.75),
                              (testNot, VBool True, [], VFloat 0.25),
                              (simpleCall, VFloat 0.5, [], VFloat 1.0),
                              --(testCallLambda, VFloat 2.5, [], VFloat 1.0),
                              --(testCallLambdaAdvanced, VFloat 2.5, [], VFloat 1.0),
                              --(testLetIn, VFloat 1.5, [], VFloat 1.0)]
                              --(testRecursion, VFloat 1.5, [], VFloat (1/81)),
                              (testInjFPlusLeft, VFloat 1.5, [], VFloat 1.0),
                              (testInjFPlusRight, VFloat 1.5, [], VFloat 1.0),
                              (testDim, VFloat 3, [], VFloat 0.5),
                              (testDim, VFloat 0.4, [], VFloat 0.25)]

correctIntegralValuesTestCases :: [(Program Double, Value Double, Value Double, [IRExpr Double], Value Double)]
correctIntegralValuesTestCases = [(uniformProg, VFloat 0, VFloat 1, [], VFloat 1.0),
                                  (uniformProg, VFloat  (-1), VFloat 2, [], VFloat 1.0),
                                  (normalProg, VFloat (-5), VFloat 5, [], VFloat $ normalCDF 5 - normalCDF (-5)),
                                  (normalProgMult, VFloat (-5), VFloat 5, [], VFloat $ normalCDF 10 - normalCDF (-10)),
                                  (uniformNegPlus, VFloat (-5), VFloat (-4.5), [], VFloat 0.5),
                                  (uniformProgPlus, VFloat 4, VFloat 4.5, [], VFloat 0.5),
                                  (testList, VList [VFloat 0, VFloat (-1)], VList [VFloat 0.25, VFloat 1], [], VFloat $ (normalCDF 1 - normalCDF (-1)) * 0.5),
                                  (simpleTuple, VTuple (VFloat 0) (VFloat (-1)), VTuple (VFloat 0.25) (VFloat 1), [], VFloat $ (normalCDF 1 - normalCDF (-1)) * 0.5),
                                  (uniformIfProg, VFloat 0, VFloat 1, [], VFloat 0.5),
                                  (constantProg, VFloat 1, VFloat 3, [], VFloat 1),
                                  --,
                                  (testInjF, VFloat 0, VFloat 1, [], VFloat 0.5),
                                  (testInjF2, VFloat 2, VFloat 3, [], VFloat 0.5),
                                  (testInjFPlusLeft, VFloat 1, VFloat 1.5, [], VFloat 0.5),
                                  (testInjFPlusRight, VFloat 1, VFloat 1.5, [], VFloat 0.5),
                                  (testTheta, VFloat 0.9, VFloat 1.1, flatTree [1], VFloat 1),
                                  (simpleCall, VFloat 0, VFloat 1, [], VFloat 1.0)]
                                  --(testCallLambda, VFloat 2, VFloat 3, [], VFloat 1.0)]
                                  --(testCallLambdaAdvanced, VFloat 2, VFloat 3, [], VFloat 1.0),
                                  --(testLetIn, VFloat 1.5, VFloat 2, [], VFloat 0.5)]

noTopKConfig :: CompilerConfig a
noTopKConfig = CompilerConfig Nothing False 0

prop_CheckProbTestCases :: Property
prop_CheckProbTestCases = forAll (elements correctProbValuesTestCases) checkProbTestCase

prop_CheckIntegralTestCases :: Property
prop_CheckIntegralTestCases = forAll (elements correctIntegralValuesTestCases) checkIntegralTestCase

prop_CheckIntegralConverges :: Property
prop_CheckIntegralConverges = forAll (elements correctIntegralValuesTestCases) checkIntegralConverges

prop_CheckTopKInterprets :: Property
prop_CheckTopKInterprets = forAll (elements correctProbValuesTestCases) checkTopKInterprets

prop_CheckProbTestCasesWithBC :: Property
prop_CheckProbTestCasesWithBC = forAll (elements correctProbValuesTestCases) checkProbTestCasesWithBC

checkProbTestCase :: (Program Double, Value Double, [IRExpr Double], Value Double) -> Property
checkProbTestCase (p, inp, params, out) = ioProperty $ do
  actualOutput <- evalRandIO $ irDensity p inp params
  case actualOutput of 
    VTuple a (VFloat _) -> return $ a === out
    _ -> return $ counterexample "Return type was no tuple" False

checkIntegralTestCase :: (Program Double, Value Double, Value Double, [IRExpr Double], Value Double) -> Property
checkIntegralTestCase (p, low, high, params, out) = ioProperty $ do
  actualOutput <- evalRandIO $ irIntegral p low high params
  case actualOutput of 
    VTuple a (VFloat _) -> return $ a === out
    _ -> return $ counterexample "Return type was no tuple" False

--TODO better bounds for Integral
checkIntegralConverges :: (Program Double, Value Double, Value Double, [IRExpr Double], Value Double) -> Property
checkIntegralConverges (p, VFloat a, VFloat b, params, _) = ioProperty $ do
  actualOutput <- evalRandIO $ irIntegral p (VFloat (-9999999)) (VFloat 9999999) params
  case actualOutput of 
    VTuple a (VFloat _) -> return $ a === VFloat 1
    _ -> return $ counterexample "Return type was no tuple" False
checkIntegralConverges _ = False ==> False

checkTopKInterprets :: (Program Double, Value Double, [IRExpr Double], Value Double) -> Property
checkTopKInterprets (p, inp, params, _) = ioProperty $ do
  actualOutput <- evalRandIO $ irDensityTopK p 0.05 inp params
  return $ actualOutput === actualOutput  -- No clue what the correct value should be here. Just test that is interprets to any value

checkProbTestCasesWithBC :: (Program Double, Value Double, [IRExpr Double], Value Double) -> Property
checkProbTestCasesWithBC (p, inp, params, out) = ioProperty $ do
  actualOutput <- evalRandIO $ irDensityBC p inp params
  case actualOutput of 
    VTuple a (VTuple (VFloat _) (VFloat _)) -> return $ a === out
    _ -> return $ counterexample "Return type was no tuple" False

prop_TopK :: Property
prop_TopK = ioProperty $ do
  actualOutput0 <- evalRandIO $ irDensityTopK testTopK 0.1 (VFloat 0) []
  actualOutput1 <- evalRandIO $ irDensityTopK testTopK 0.1 (VFloat 1) []
  case (actualOutput0, actualOutput1) of
    (VTuple a (VFloat _), VTuple b (VFloat _)) -> return $ (b == VFloat 0.95) && (a == VFloat 0)
    _ -> return False

--prop_CheckProbTestCases = foldr (\(p, inp, out) acc -> do
--  checkProbTestCase p inp out .&&. acc) (True===True) correctProbValuesTestCases

irDensityTopK :: RandomGen g => Program Double -> Double -> Value Double -> [IRExpr Double]-> Rand g (Value Double)
irDensityTopK p thresh s params = IRInterpreter.generateRand irEnv irEnv (sampleExpr:params) irExpr
  where Just irExpr = lookup "main_prob" irEnv
        sampleExpr = IRConst s
        irEnv = envToIR (CompilerConfig (Just thresh) False 0) annotated
        annotated = annotateProg typedProg
        typedProg = addTypeInfo p

irDensityBC :: RandomGen g => Program Double -> Value Double -> [IRExpr Double]-> Rand g (Value Double)
irDensityBC p s params = IRInterpreter.generateRand irEnv irEnv (sampleExpr:params) irExpr
  where Just irExpr = lookup "main_prob" irEnv
        sampleExpr = IRConst s
        irEnv = envToIR (CompilerConfig Nothing True 0) annotated
        annotated = annotateProg typedProg
        typedProg = addTypeInfo p

irDensity :: RandomGen g => Program Double -> Value Double -> [IRExpr Double] -> Rand g (Value Double)
irDensity p s params = IRInterpreter.generateRand irEnv irEnv (sampleExpr:params) irExpr
  where Just irExpr = lookup "main_prob" irEnv
        sampleExpr = IRConst s
        irEnv = envToIR noTopKConfig annotated
        annotated = annotateProg typedProg
        typedProg = addTypeInfo p

irIntegral :: RandomGen g => Program Double -> Value Double -> Value Double -> [IRExpr Double] -> Rand g (Value Double)
irIntegral p low high params = IRInterpreter.generateRand irEnv irEnv (lowExpr:highExpr:params) irExpr
  where Just irExpr = lookup "main_integ" irEnv
        lowExpr = IRConst low
        highExpr = IRConst high
        irEnv = envToIR noTopKConfig annotated
        annotated = annotateProg typedProg
        typedProg = addTypeInfo p

{-irInterpret :: RandomGen g => Program () Double -> [IRExpr Double] -> Rand g (Value Double)
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

langDensity :: Program () Double -> Double -> Value Double
langDensity p sample = case Interpreter.runInferL [] witExpr [] (VFloat sample) of
  PDF prob -> VFloat prob
  DiscreteProbability prob -> VFloat prob
  where Program _ witExpr = addWitnessesProg typedProg
        typedProg = addTypeInfo p


-- Program sets for tests
examples :: [Program () Float]
examples = [makeMain variableLength, makeMain testGreater, makeMain testGaussianMixture, makeMain testIntractable]

{-
testsetA :: [Program (TypeInfo a) Double]
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

canCompile :: (Show a) => Program a -> Bool
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

autoIRExpr :: (Num a, Reifies s Tape) => IRExpr a -> IRExpr (Reverse s a)
autoIRExpr e = irMap auto e-}


{-prop_interpretersEqualDensity :: Program () Double -> Double -> Property
prop_interpretersEqualDensity p sample = do
  let compilable = canCompile p
  if compilable then ioProperty $ do
      irValue <- evalRandIO $ irDensity p sample
      return $ irValue == langDensity p sample
  else
    property Discard -}

--testCompile :: Expr a -> Property
--testCompile e = addWitnessesProg $ addTypeInfo $ makeMain e

testRecompile :: (Eq a, Show a, Recompilable a) => a -> Property
testRecompile inp = case recompile inp of
   Left err -> counterexample (show inp) (False === True)
   Right program -> program === inp

expressionsGen :: Gen (Expr () Float)
expressionsGen = elements (map fst expressions)

parametrizedGen :: Gen (Env () Float, Thetas Float)
parametrizedGen = do
  expr <- elements (map fst expressions)
  let maxIx = maximum $ catMaybes $ map maxThetaIx $ findThetas expr
  --  (\thExpr -> case thExpr of ThetaI _ x -> Just x otherExpr -> Nothing)
  thetas <- genThetas (maxIx + 1)
  return ([("main", expr)], thetas)

maxThetaIx :: Expr t a -> Maybe Int
maxThetaIx (ThetaI _ a x) = Just x
maxThetaIx _ = Nothing

genThetas :: Int -> Gen (Thetas Float)
genThetas = vector

findThetas :: Expr t a -> [Expr t a]
findThetas (ThetaI a b c) = [ThetaI a b c]
findThetas expr = concatMap findThetas x
  where x = getSubExprs expr

expressions :: [(Expr () Float, TypeInfo a)]
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


propInfer :: (Eq a, Show a) => Program a -> Program a -> Property
propInfer a b = addWitnessesProg (addTypeInfo a) === b

sumsToOne :: IO Result
sumsToOne = undefined
-}
return []


runTests :: IO Bool
runTests = $quickCheckAll


main :: IO Bool
main = do
  x <- runTests
  print x
  return x
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
