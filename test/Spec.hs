{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}

import Test.QuickCheck

import Lib
import Lang
import Typing
import RType
import PType
import Interpreter
import Data.Maybe (fromJust, catMaybes)
import Control.Monad.Random.Lazy (Random)

main :: IO ()
main = do
  quickCheck $ compilesTo [("main", fst $ head expressions)] (snd $ head expressions)
  quickCheck $ forAll expressionsGen (\expr -> compilesTo [("main", expr)] $ fromJust $ lookup expr expressions)
  quickCheck $ forAll parametrizedGen $ discreteProbAlignment 1000
  putStrLn "all tests done"

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

discreteProbAlignment :: (Random a, Show a, Real a, Floating a) => Int -> (Env () a, Thetas a) -> Property
discreteProbAlignment nSamples (env, thetas) = ioProperty $ case mMain of
    Nothing -> return $ counterexample "typed main not found in discreteProbAlignment" False
    Just mainExpr -> do
      samples <- mkSamples nSamples typedEnv thetas mainExpr
      let sample_counts = count samples
      let valProb = [(probability typedEnv typedEnv thetas mainExpr val, DiscreteProbability (realToFrac val_count / realToFrac nSamples))| (val_count, val) <- sample_counts]
      return $ conjoin (map (\(x, y) -> epsilonProb 0.05 x y) valProb)
  where
    pretypedEnv = typeCheckEnv env
    mMain = lookup "main" typedEnv
    typedEnv = resolveConstraints pretypedEnv
  

sumsToOne :: IO Result
sumsToOne = undefined

--compilesTo :: Env () a -> TypeInfo -> Bool
compilesTo :: Eq a => [(String, Expr () a)] -> TypeInfo -> Property
compilesTo env t = case lookup "main" pretypedEnv of
    Just _ -> case lookup "main" typedEnv of
      Nothing -> counterexample "typed main not found" False
      Just typed_main -> getTypeInfo typed_main === t
    Nothing -> counterexample "untyped main not found" False
  where
    pretypedEnv = typeCheckEnv env
    typedEnv = resolveConstraints pretypedEnv

