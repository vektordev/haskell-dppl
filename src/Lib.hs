{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Lib where
--    ( someFunc
--    ) where


import Numeric.AD
import System.Random
--import Control.Monad
--import Data.List (transpose, sortBy, elemIndices, nub)
import Data.Maybe
import Data.Reflection (Reifies)
import Numeric.AD.Internal.Reverse ( Reverse, Tape)
--import Data.Either (fromRight)
import Debug.Trace
import Data.Function (on)
import Data.Ord
import Data.List (elemIndices, sortBy, nub, intercalate)
import Text.Pretty.Simple

import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Typing.Infer
import SPLL.Typing.PInfer2
import SPLL.Typing.RInfer
import Control.Monad.Random (evalRandIO, getRandomR, replicateM, forM_)
import SPLL.IntermediateRepresentation
import SPLL.Analysis
import SPLL.CodeGenPyTorch
import SPLL.CodeGenJulia
import SPLL.Typing.Witnessing
import SPLL.Examples
import Debug.Trace
import SpecExamples
import Statistics.Sample.KernelDensity
import Data.Vector.Generic (fromList)
import qualified Data.Vector as V
import Data.Bifunctor (bimap)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Number.Erf
import SPLL.Typing.BruteForceSolver (forceAddTypeInfo, runBruteForceSolver)
import SPLL.IRCompiler
import SPLL.Typing.ForwardChaining
import IRInterpreter
import PrettyPrint
import Data.Bifunctor (second)
{-variableLengthS2 :: Program  () Double
variableLengthS2 = Program [("b", IfThenElse ()
                          (GreaterThan () (Uniform ()) (ThetaI () 0))
                          (Null ())
                          (Cons () (Constant () (VBool True)) (Call () "b")))]
                  (Call () "b")
-}
--assumption about grad: Reverse s a is Num if a is Num.
--Thererfore, grad :: (Traversable f, Num a) => (forall s. Reifies s Tape => f (Reverse s a) -> Reverse s a) -> f a -> f a
-- essentially translates to grad :: Traversable f, Num a) => (f (Reverse s a) -> Reverse s a) -> f a -> f a
-- or more simply: grad takes any function :: Traversable f, Num a => f a -> a;
-- but then we have to sort out the type of the hypothesis (a)

--someFunc = print "Hello world"

data Language = Python | Julia deriving Show

readSamples :: IO [(Double, Double)]
readSamples = do
  f <- readFile "./data/train_data.txt"
  --print $ lines f
  let res = map read $ lines f
  --print res
  return res

map2RSamples :: (Double, Double) -> Value
map2RSamples (a,b) = constructVList [VFloat a, VFloat b]

{-
thatGaussThing :: IO()
thatGaussThing = do
  --TODO: I desperately need tuple types.
  -- Otherwise gaussianMixture won't compile because it sports a heterogeneous list.
  untypedSamples <- readSamples
  let samples = map map2RSamples untypedSamples
  print samples
  let env = [("main", testGaussianMixture)] :: Env () Double
  initialThetas <- replicateM 9 (getRandomR (0.0, 1.0))
  let pretypedEnv = typeCheckEnv env
  let typedEnv = resolveConstraints pretypedEnv
  let Just main = lookup "main" typedEnv
  print main
  let thetasRecovered = myGradientAscent 400 typedEnv initialThetas main samples
  mapM_ print thetasRecovered
  llScan typedEnv (fst $ last thetasRecovered) main
-}

{-
llScan :: (Erf a, Real a, Floating a, Show a, Enum a) => Program -> Thetas a -> Expr -> IO ()
llScan p thetas main = do
  let scanPts = [(x,y) | x <- [0, 0.01 .. 1], y <- [0, 0.01 .. 1]]
  let scanRes = [(x, y, runInferL p main thetas (VList [VFloat x, VFloat y])) | x <- [0, 0.01.. 1], y <- [0, 0.01.. 1]]
  print scanPts
  print scanRes
  let fileStr = unlines $ map (\(x,y,l) -> show x ++ ", " ++ show y ++ ", " ++ (show $ unwrapP l)) scanRes
  writeFile "./data/ll_out.txt" fileStr
  -}
{-
newCodeGen :: Expr TypeInfo Float -> IO ()
newCodeGen tExpr = do
  let annotated = SPLL.Analysis.annotate tExpr
  print annotated
  let irGen = toIRGenerate annotated
  print irGen
  let gen = generateCode irGen ""
  putStrLn $ unlines gen
  let irProb = runSupplyVars $ toIRProbability annotated (IRVar "input")
  print irProb
  let prob = generateCode irProb ""
  putStrLn $ unlines prob-}

newCodeGenAll :: CompilerConfig -> Program -> IO ()
newCodeGenAll conf p = do
  pPrint p
  let preAnnotated = annotateEnumsProg p
  let annotated = annotateAlgsProg preAnnotated
  pPrint annotated
  let ir = envToIR conf annotated
  pPrint ir
  let pycode = SPLL.CodeGenPyTorch.generateFunctions ir
  let jlcode = SPLL.CodeGenJulia.generateFunctions ir
  putStrLn "python code:"
  putStrLn $ unlines pycode
  putStrLn "julia code:"
  putStrLn $ unlines jlcode

codeGenToLang :: Language -> CompilerConfig -> Program -> IO String
codeGenToLang lang conf prog = do
  printIfVerbose conf "=== Parsed Program ===\n"
  doVerbose 2 conf (pPrint prog)
  printIfVerbose conf (pPrintProg prog)

  let preAnnotated = annotateEnumsProg prog
  doVerbose 2 conf (putStrLn "\n\n=== Annotated Program (1) ===\n" >> pPrint preAnnotated)

  let typed = addTypeInfo preAnnotated
  doVerbose 2 conf (putStrLn "\n\n=== Typed Program ===\n" >> pPrint typed)

  let annotated = annotateAlgsProg typed
  doVerbose 2 conf (putStrLn "\n\n=== Annotated Program (2) ===\n" >> pPrint annotated)

  let ir = envToIR conf annotated
  printIfVerbose conf "\n\n=== Compiled Program ===\n"
  printIfVerbose conf (pPrintIREnv ir)
  doVerbose 2 conf (pPrint ir)

  case lang of
    Python -> return $ intercalate "\n" (SPLL.CodeGenPyTorch.generateFunctions ir)
    Julia -> return $ intercalate "\n" (SPLL.CodeGenJulia.generateFunctions ir)

doVerbose :: Int -> CompilerConfig -> IO () -> IO()
doVerbose level CompilerConfig{verbose=v} action = if v >= level then action else return ()

printIfVerbose :: CompilerConfig -> String -> IO ()
printIfVerbose conf s = doVerbose 1 conf (putStrLn s)

printIfMoreVerbose :: CompilerConfig -> String -> IO ()
printIfMoreVerbose conf s = doVerbose 2 conf (putStrLn s)

someFunc :: IO ()
someFunc = do
  putStrLn "--------"
  putStrLn "--------"
  let conf = CompilerConfig{topKThreshold = Nothing, countBranches = True, verbose=2}
  let lang = Python
  let prog = testCallLambda --testDiceAdd --testNN
  someString <- codeGenToLang lang conf prog
  putStrLn someString
  putStrLn "========="
--runNNTest :: IO ()
{-
runNNTest :: IO [Value Float]
runNNTest = do
  print "Running NN Test"
  let testNN2 = addWitnesses Set.empty testNN
  let typedEnv = [("main", testNN2)]

  let Just main = lookup "main" typedEnv
  putStrLn $ unlines $ prettyPrint main
  let resultR = rType $ getTypeInfo main
  print resultR
  let resultP = pType $ getTypeInfo main
  print resultP
  return  [VFloat 3.0]
  --mkSamples 1000 typedEnv [] [Constant (TypeInfo TSymbol Deterministic) (VSymbol "image1"), Constant (TypeInfo TSymbol Deterministic) (VSymbol "image2")] main
-}

{-
myGradientAscent :: (Erf a, RealFloat a, Show a, Floating a, Real a) => Int -> a -> Program -> Thetas a -> Expr -> [Value] -> [(Thetas a, a)]
myGradientAscent 0 _ _ _ _ _ = []
myGradientAscent n learning_rate p thetas expr vals =
  (thetas, loss) : myGradientAscent (n-1) learning_rate p new expr vals
    where
      (loss, new) = optimizeStep p expr vals thetas learning_rate

optimizeStep :: (Erf a, Show a, RealFloat a, Floating a, Real a) => Program -> Expr -> [Value] -> Thetas a -> a -> (a, Thetas a)
optimizeStep p expr samples thetas learning_rate = (loss,
    addThetas thetas (mult (1.0 / fromIntegral (length samples))(mult learning_rate gradient)) )
  where
    -- does it make a difference if we do sum(gradients) or if we do gradient(sums)?
    -- TODO: Is it correct to apply map-sum, or do we flatten the wrong dimension here?
    --grad_loss :: [(loss :: a, grad :: Thetas a)]
    grad_loss = [grad' (\theta -> log $ unwrapP $ runInferL (autoProg p) (autoExpr expr) theta (autoVal sample)) thetas | sample <- samples]
    --grad_thetas = [Thetas a]

    grad_thetas = map snd grad_loss
    --gradient :: Thetas a
    gradient = foldl1 addThetas grad_thetas
    loss = sum $ map fst grad_loss

-}

{-addThetas :: (Floating a) => Thetas a -> Thetas a -> Thetas a
addThetas x y = zipWith (+) x y

mult :: (Floating a) => a -> Thetas a -> Thetas a
mult x y = map (*x) y


testDensity2d :: String -> Program Double -> Thetas Double -> IO ()
testDensity2d experimentName prog thetas = do
  let typedProg = addWitnessesProg (addTypeInfo prog)
  let Just main = lookup "main" typedProg
  print "Type Info"
  samples <- mkSamples 10000 typedProg thetas [] main
  let dataStrs = map (\(VList vals) -> intercalate "," (map (\(VFloat x) -> show x) vals)) samples
  let fileStr = unlines dataStrs
  writeFile ("./data/gen_samples" ++ experimentName ++ ".txt") fileStr

  let interval_a = (0.01, 0.99, 0.01)
  let interval_b = (0.01, 0.99, 0.01)
  let interval = sequence [createInputs interval_a, createInputs interval_b]
  let valF [d1, d2] = VList [VFloat d1,  VFloat d2]
  let likelihood_y = map (\(PDF p) -> p) (map (runInferL typedProg main thetas  . valF) interval)
  let dataStrsL = map show likelihood_y
  let interval_line (a,b,c) = show a ++ "," ++ show b ++ "," ++ show c
  let fileStrL = unlines ((interval_line interval_a):(interval_line interval_b:dataStrsL))
  print (filter ( (> 100) . fst)(zip likelihood_y interval))
  writeFile ("./data/likelihoods_" ++ experimentName ++ ".txt") fileStrL

testDensity1d :: String -> Program Double -> Thetas Double -> IO ()
testDensity1d experimentName prog thetas = do
  let typedProg = addWitnessesProg (addTypeInfo prog)
  let Just main = lookup "main" typedProg
  print "Type Info"
  samples <- mkSamples 10000 typedProg thetas [] main
  let dataStrs = map (\(VFloat val)-> show val) samples
  let fileStr = unlines dataStrs
  writeFile ("./data/gen_samples1d" ++ experimentName ++ ".txt") fileStr
  let interval_a = (0.01, 0.99, 0.01)
  let interval =  createInputs interval_a
  let likelihood_y = map (\(PDF p) -> p) (map (runInferL typedProg main thetas . VFloat) interval)
  let dataStrsL = map show likelihood_y
  let interval_line (a,b,c) = show a ++ "," ++ show b ++ "," ++ show c
  let fileStrL = unlines ((interval_line interval_a):dataStrsL)
  writeFile ("./data/likelihoods_1d" ++ experimentName ++ ".txt") fileStrL
  -}
  
{-genTheta :: ( Show a, Fractional a, Ord a, Random a, Floating a) => Program -> IO (a)
genTheta p = if predicateProg isNotTheta p
              then do
                     let typedProg = addWitnessesProg (addTypeInfo p)
                     let (Just main) = lookup "main" typedProg
                     val <- evalRandIO $ Interpreter.generate typedEnv typedEnv [] [] main
                     return (getVFloat val)
              else error "Theta in prior expression"
              
genThetas :: (Show a, Fractional a, Ord a, Random a, Floating a) => Program -> IO (Thetas a)
genThetas p = if predicateProg isNotTheta p
              then do
                     let typedEnv = progToEnv $ addWitnessesProg (addTypeInfo p)
                     let (Just main) = lookup "main" typedEnv
                     val <- evalRandIO $ Interpreter.generate typedEnv typedEnv [] [] main
                     return (valToFloatList val)
              else error "Theta in prior expression"
valToFloatList :: Value -> Thetas a
valToFloatList (VFloat x) = [x]
valToFloatList (VList vfl) = map getVFloat vfl
-}
{-
testRun :: (Erf a, RealFloat a, Floating a, Ord a, Random a, Show a, Real a, Enum a) => String -> Program -> Thetas a -> IO ()
testRun experimentName prog thetas = do
  print "Hello world"
  mapM_ putStrLn (prettyPrintProg prog)
  print "A"
  let typedEnv = progToEnv $ addWitnessesProg (addTypeInfo prog)
  let Just main = lookup "main" typedEnv
  print "Type Info"
  mapM_ (putStrLn . unlines . prettyPrint . snd) typedEnv
  let resultR = rType $ getTypeInfo main
  print resultR
  let resultP = pType $ getTypeInfo main
  print resultP
  print main
  samples <- mkSamples 1000 typedEnv thetas [] main
  print typedEnv
  let p = runInferIO typedEnv main thetas (VFloat 1.0)
  p
  print "Avg sample "
  --print $ avgSamples samples
  --print "Likelihood 1.0 "

  let valF d = VList [VFloat $ head d, VFloat $ d !! 1, VFloat $ d !! 2]
  -- (-20.0, 20.0, 0.1)
  -- (0.01, 0.99, 0.01)
  let integ_sizes = [(0.01, 0.99, 0.01), (0.01, 0.99, 0.01), (0.01, 0.99, 0.01)]
  let stepsizeAll = foldl (\x (_,_,s) -> x*s) 1.0 integ_sizes
  print stepsizeAll
  let createInputs (start, end, stepsize) = [start, start+stepsize .. end]
  let inputs = map createInputs integ_sizes
  
  let inputsS = sequence inputs
  print $ length inputsS
  --print sum_sig
  --print $ length sig_lik
  let integ = integralApprox integ_sizes valF (runInferL typedEnv main thetas)
  let ex = expectedValue integ_sizes valF (runInferL typedEnv main thetas)
  print "Integral of function"
  --print integ
  --print ex
  --print $ likelihood typedEnv typedEnv [0.0] main (VTuple (VFloat 0.9)(VFloat 0.1))

  --putStrLn "exprDebugMetrics:"
  --exprDebugMetrics typedEnv main samples ([0.1, 0.1])
  --gradientDiag typedEnv [[x] | x <- [0, 0.01 .. 1]] main samples
  --probabilityDiag typedEnv [[x] | x <- [0, 0.01 .. 3]] main (VFloat 0.1)
  --putStrLn " // exprDebugMetrics:"

  --mapM_ print $ count samples

  -- (genThetas uniformProg) (if parameters differ in prior
  initialThetas <- replicateM (length thetas) (genTheta uniformProg)
  let thetasRecovered = myGradientAscent 500 0.01 typedEnv initialThetas main samples
  --mapM_ print thetasRecovered
  --TODO: Handle different theta sizes
  -- also put original thetas as first line.
  let firstline = intercalate ", " $ map show (thetas ++ [0])
  let dataStrs = map (\(ts, d) -> intercalate ", " $ map show (ts ++ [d])) thetasRecovered
  let fileStr = unlines (firstline:dataStrs)
  --writeFile ("./data/thetas_out_" ++ experimentName ++ ".txt") fileStr
  print "end of test run"
  --gradientDiagAt typedEnv [0.1, 0.9] main samples
  --gradientDiagAt typedEnv [-0.1, 0.9] main samples
  --gradientDiagAt typedEnv [0.2, 0.9] main samples
  -- [VTuple (VFloat 0.9) (VFloat 0.4)]
expectedValue :: (Floating a, Enum a, Show a) => [(a, a, a)] -> ([a] -> Value) -> (Value -> Probability a) -> Probability a
expectedValue rectangleInfo valF lkF = (pAnd  (foldl pOr (PDF 0) lks)  (PDF (1/lk_sum)))
  where createInputs (start, end, stepsize) = [start, start+stepsize .. end]
        inputs = map createInputs rectangleInfo
        inputsS = sequence inputs
        stepsizeAll = foldl (\x (_,_,s) -> x*s) 1.0 rectangleInfo
        lks_2 = map ( lkF . valF) inputsS
        lks = zipWith pAnd lks_2 x_vals
        x_vals =  map (DiscreteProbability . head) inputsS
        (PDF lk_sum) = foldl pOr (PDF 0) lks_2

createInputs :: (Floating a, Enum a) => (a, a, a) -> [a]
createInputs (start, end, stepsize) = [start, start+stepsize .. end]

integralApprox :: (Floating a, Enum a, Show a) => [(a, a, a)] -> ([a] -> Value) -> (Value -> Probability a) -> Probability a
integralApprox rectangleInfo valF lkF = pAnd  (DiscreteProbability stepsizeAll) (foldl pOr (PDF 0) lks)
  where inputs = map createInputs rectangleInfo
        inputsS = sequence inputs
        stepsizeAll = foldl (\x (_,_,s) -> x*s) 1.0 rectangleInfo
        lks = map ( lkF . valF) inputsS

mkSamples :: (Fractional a, Ord a, Random a, Floating a) => Int -> Env a -> Thetas a -> [Expr] -> Expr -> IO [Value]
mkSamples 0 _ _ _ _ = return []
mkSamples n env thetas args expr = do
  sample <- evalRandIO $ Interpreter.generate env env thetas args expr
  remainder <- mkSamples (n-1) env thetas args expr
  return (sample:remainder)

avgSamples :: (Fractional a, Ord a, Random a) => [Value] -> a
avgSamples samples =  (1.0 / fromIntegral (length samples)) * (rec samples 0)
  where rec ((VFloat b):[]) z = z + b
        rec ((VFloat b):k) z = rec k (z + b)
count :: Eq a => [a] -> [(Int, a)]
count lst = sortBy (compare `on` (Down . fst)) [(length $ elemIndices x lst, x) | x <- nub lst]
-}
