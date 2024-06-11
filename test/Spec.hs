{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

import Test.QuickCheck

import SPLL.Examples
--import Lib
import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Typing.Typing
import SPLL.Analysis
import SPLL.IntermediateRepresentation
import Interpreter
import IRInterpreter
import Data.Maybe (fromJust, catMaybes)
import Control.Monad.Random.Lazy (Random, RandomGen, Rand, evalRandIO)
import SPLL.Typing.PInferBranched
import SPLL.Typing.Infer
import SPLL.Typing.Witnessing
import SpecExamples
import ArbitrarySPLL
import Control.Exception.Base (SomeException, try)
import Test.QuickCheck.Monadic (monadicIO, run, assert)
import Debug.Trace (trace)
import SPLL.Lang (Value)
import Control.Monad.Supply
import Data.Foldable
import Data.Number.Erf (erf)
import Numeric.AD (grad', auto)
import InjectiveFunctions (autoExpr, autoEnv, autoVal)
import Numeric.AD.Internal.Reverse (Reverse, Tape)
import Data.Reflection (Reifies)

-- Generalizing over different compilation stages, we can fit all "this typing is what the compiler would find" cases.
class Recompilable a where
  recompile :: a -> Either CompileError a

untypeP :: Program t a -> Program () a
untypeP (Program defs main) = Program (map (\(a,b) -> (a, untypeE b)) defs) (untypeE main)

untypeE :: Expr t a -> Expr () a
untypeE = tMap (const ())

instance Show a => Recompilable (Program TypeInfoWit a) where
  recompile = infer . untypeP

instance Show a => Recompilable (Program TypeInfo a) where
  recompile = inferNoWit . untypeP

instance Show a => Recompilable (Expr TypeInfo a) where
  recompile e = case inferNoWit $ makeMain $ untypeE e of
    Right (Program [("main", d)] _) -> Right d
    Left x -> Left x
    Right (Program _ _) -> error "unexpected error when recompiling Expr TypeInfo a."

-- Program sets for tests
examples :: [Program () Float]
examples = [makeMain variableLength, makeMain testGreater, makeMain testGaussianMixture, makeMain testIntractable]

testsetA :: [Program TypeInfoWit Double]
testsetA = [variableLengthT, testLetT, testLetNonLetT, testLetDT, testLetTupleT, testLetXYT]
prop_RecompileA :: Property
prop_RecompileA = forAll (elements testsetA) testRecompile

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

canCompile :: (Show a) => Program () a -> Bool
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

normalPDF :: Double -> Double
normalPDF x = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)

normalCDF :: Double -> Double
normalCDF x = (1/2)*(1 + erf(x/sqrt(2)))
    
correctProbValuesTestCases :: [(Program () Double, Value Double, [Double], Value Double)]
correctProbValuesTestCases = [(uniformProg, VFloat 0.5, [], VFloat 1.0),
                              (normalProg, VFloat 0.5, [], VFloat $ normalPDF 0.5),
                              (uniformProgMult, VFloat (-0.25), [], VFloat 2),
                              (normalProgMult, VFloat (-1), [], VFloat (normalPDF (-2) * 2)),
                              (uniformNegPlus, VFloat (-4.5), [], VFloat 1),
                              (testList, VList [VFloat 0.25, VFloat 0], [], VFloat $ normalPDF 0 * 2),
                              (simpleTuple, VTuple (VFloat 0.25) (VFloat 0), [], VFloat $ normalPDF 0 * 2),
                              (uniformIfProg, VFloat 0.5, [], VFloat 0.5),
                              (constantProg, VFloat 2, [], VFloat 1),
                              (simpleCall, VFloat 0.5, [], VFloat 1.0),
                              (uniformExp, VFloat $ exp 4.5, [], VFloat 1.0)]

correctIntegralValuesTestCases :: [(Program () Double, Value Double, Value Double, [Double], Value Double)]
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
                                  (simpleCall, VFloat 0, VFloat 1, [], VFloat 1.0)]

prop_CheckProbTestCases :: Property
prop_CheckProbTestCases = forAll (elements correctProbValuesTestCases) checkProbTestCase

prop_CheckIntegralTestCases :: Property
prop_CheckIntegralTestCases = forAll (elements correctIntegralValuesTestCases) checkIntegralTestCase

prop_CheckIntegralConverges :: Property
prop_CheckIntegralConverges = forAll (elements correctIntegralValuesTestCases) checkIntegralConverges

checkProbTestCase :: (Program () Double, Value Double, [Double], Value Double) -> Property
checkProbTestCase (p, inp, thetas, out) = ioProperty $ do
  actualOutput <- evalRandIO $ irDensity p inp thetas
  return $ actualOutput === out

checkIntegralTestCase :: (Program () Double, Value Double, Value Double, [Double], Value Double) -> Property
checkIntegralTestCase (p, low, high, thetas, out) = ioProperty $ do
  actualOutput <- evalRandIO $ irIntegral p low high thetas
  return $ actualOutput === out

--TODO better bounds for Integral
checkIntegralConverges :: (Program () Double, Value Double, Value Double, [Double], Value Double) -> Property
checkIntegralConverges (p, VFloat a, VFloat b, thetas, _) = ioProperty $ do
  actualOutput <- evalRandIO $ irIntegral p (VFloat (-9999999)) (VFloat 9999999) thetas
  return $ trace (show actualOutput) actualOutput === VFloat 1
checkIntegralConverges _ = False ==> False

--prop_CheckProbTestCases = foldr (\(p, inp, out) acc -> do
--  checkProbTestCase p inp out .&&. acc) (True===True) correctProbValuesTestCases

irDensity :: RandomGen g => Program () Double -> Value Double -> [Double] -> Rand g (Value Double)
irDensity p sample thetas = IRInterpreter.generate irEnv irEnv thetas [] irExpr
  where irExpr = runSupply (toIRProbability main (IRConst sample)) (+1) 1
        Just main = lookup "main" annotated
        irEnv = envToIR annotated
        annotated = map (\(a,b) -> (a, annotate b)) env
        env = progToEnv typedProg
        typedProg = addTypeInfo p

irIntegral :: RandomGen g => Program () Double -> Value Double -> Value Double -> [Double] -> Rand g (Value Double)
irIntegral p low high thetas = IRInterpreter.generate irEnv irEnv thetas [] irExpr
  where irExpr = runSupply (toIRIntegrate main (IRConst low) (IRConst high)) (+1) 1
        Just main = lookup "main" annotated
        irEnv = envToIR annotated
        annotated = map (\(a,b) -> (a, annotate b)) env
        env = progToEnv typedProg
        typedProg = addTypeInfo p

irInterpret :: RandomGen g => Program () Double -> [IRExpr Double] -> Rand g (Value Double)
irInterpret p params = IRInterpreter.generate irEnv irEnv [] params main
  where Just main = lookup "main_prob" irEnv
        irEnv = envToIR annotated
        annotated = map (\(a,b) -> (a, annotate b)) env
        env = progToEnv typedProg
        typedProg = addTypeInfo p

progToIREnv ::(Ord a, Fractional a, Show a, Eq a, Random a) => Program () a -> [(String, IRExpr a)]
progToIREnv p = envToIR $ map (\(a,b) -> (a, annotate b)) $ progToEnv $ addTypeInfo p

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

--testCompile :: Expr () a -> Property
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
maxThetaIx (ThetaI _ x) = Just x
maxThetaIx _ = Nothing

genThetas :: Int -> Gen (Thetas Float)
genThetas = vector

findThetas :: Expr t a -> [Expr t a]
findThetas (ThetaI a b) = [ThetaI a b]
findThetas expr = concatMap findThetas x
  where x = getSubExprs expr

expressions :: [(Expr () Float, TypeInfo)]
expressions = [
    (testIf, TypeInfo TBool Integrate),
    (testGreater, TypeInfo TBool Integrate),
    (testGreater2, TypeInfo TBool Integrate)
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


propInfer :: (Eq a, Show a) => Program () a -> Program TypeInfoWit a -> Property
propInfer a b = addWitnessesProg (addTypeInfo a) === b

sumsToOne :: IO Result
sumsToOne = undefined

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
