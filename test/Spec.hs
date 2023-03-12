{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}

import Test.QuickCheck

import Lib
import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.PType
import SPLL.Typing.RType
import Interpreter
import Data.Maybe (fromJust, catMaybes)
import Control.Monad.Random.Lazy (Random)
import PInferBranched
import SPLL.Examples
import Infer
import Witnessing
import SpecExamples

examples :: [Program () a]
examples = [testProg, makeMain testGreater, makeMain testGaussianMixture, makeMain testIntractable]
main :: IO ()
main = do
   checkProgs [(variableLengthS, variableLengthT),
               (testLetS, testLetT),
               (testLetNonLetS, testLetNonLetT),
               (testLetDS, testLetDT),
               (testLetTupleS, testLetTupleT),
               (testLetXYS, testLetXYT)]
  -- quickCheck $ compilesTo [("main", fst $ head expressions)] (snd $ head expressions)
  -- quickCheck $ forAll expressionsGen (\expr -> compilesTo [("main", expr)] $ fromJust $ lookup expr expressions)
  -- quickCheck $ forAll parametrizedGen $ discreteProbAlignment 1000
  -- putStrLn "all tests done"

checkProgs ::(Eq a, Show a) => [(Program () a, Program TypeInfoWit a)] -> IO ()
checkProgs [] = do putStrLn "finished"
checkProgs ((a,b):progs) = do
  quickCheck $ prop_infer a b
  checkProgs progs
expressionsGen :: Gen (Expr () Float)
expressionsGen = elements (map fst expressions)

parametrizedGen :: Gen (Env () Float, Thetas Float)
parametrizedGen = do
  expr <- elements (map fst expressions)
  let maxIx = maximum $ catMaybes $ map maxThetaIx $findThetas expr
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
  where x = recurse expr

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


prop_infer :: (Eq a, Show a) => Program () a -> Program TypeInfoWit a -> Property
prop_infer a b = addWitnessesProg (addTypeInfo a) === b

sumsToOne :: IO Result
sumsToOne = undefined


