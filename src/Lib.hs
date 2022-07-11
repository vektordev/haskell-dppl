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

import Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import Interpreter
import Transpiler
import Control.Monad.Random (evalRandIO, getRandomR, replicateM, forM_)
import CodeGen
import SPLL.IntermediateRepresentation
import SPLL.Analysis
import SPLL.CodeGenJulia

--assumption about grad: Reverse s a is Num if a is Num.
--Thererfore, grad :: (Traversable f, Num a) => (forall s. Reifies s Tape => f (Reverse s a) -> Reverse s a) -> f a -> f a
-- essentially translates to grad :: Traversable f, Num a) => (f (Reverse s a) -> Reverse s a) -> f a -> f a
-- or more simply: grad takes any function :: Traversable f, Num a => f a -> a;
-- but then we have to sort out the type of the hypothesis (a)

--someFunc = print "Hello world"

--weatherHask lastDay = if lastDay == rainy
--  then let current = randA in (current, weatherHask current)
--  else let current = randB in (current, weatherHask current)

paramExpr :: Expr () Float
paramExpr = Arg () "iterations" TFloat (IfThenElse ()
  (GreaterThan () (Call () "iterations") (Constant () (VFloat 0.5)))
  (Cons () (Constant () (VBool True)) (CallArg () "main" [Plus () (Call () "iterations") (Constant () (VFloat (-1.0)))]))
  (Null ()))

variableLength :: Expr () a
variableLength = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Null ())
  --(Cons () (Normal ()) (Call () "main"))
  (Cons () (Constant () (VBool True)) (Call () "main"))

--testExpr :: Num a => Expr a
testIf :: Expr () a
testIf = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Constant () (VBool True))
  (Constant () (VBool False))

testGreater :: Expr () a
testGreater = GreaterThan () (Uniform ()) (ThetaI () 0)

testGreater2 :: Expr () a
testGreater2 = GreaterThan () (ThetaI () 0) (Uniform ())

testExpr2 :: Expr () a
testExpr2 = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Null ())
  (Cons () (Constant () (VBool True)) (Call () "main"))

testGauss :: Expr () a
--testGauss = Plus () (Normal ()) (ThetaI () 0)
testGauss = Plus () (Mult () (Normal ()) (ThetaI () 0)) (ThetaI () 1)

--  (IfThenElse ()
--    (GreaterThan () (Uniform ()) (ThetaI () 1))
--    (Cons () (Constant () (VBool True)) (Call () "main"))
--    )

--testGauss = compile "Normal * theta[0] + theta[1]"

{--
MNIST_CNN_GEN :: Image -> Int (CNN yields distribution, we return sample)
e.g. [0 -> 0.5; 1 -> 0.3, 2 -> 0.2]; when sampling: return 0 with probability 0.5
     [0 -> 0.98; 1 -> 0.01, 2 -> 0.01]; when sampling: return 0 with probability 0.98
MNIST_CNN_Likelihood :: Image -> Int -> Float (index into distribution)
AutoDiff yields gradient for
MNIST_CNN:: Image -> Int (As Softmax over probabilities)
main =
  let
    x <- MNIST_CNN(imgA)
    y <- MNIST_CNN(imgB)
  in x + y

How do we train this? We get a result... 15 and imgA and imgB.
  MaxP(MNIST_CNN(imgA) = 6 && MNIST_CNN(imgB) = 9)
  MaxP(MNIST_CNN(imgA) = 7 && MNIST_CNN(imgB) = 8)
  MaxP(MNIST_CNN(imgA) = 8 && MNIST_CNN(imgB) = 7)
  MaxP(MNIST_CNN(imgA) = 9 && MNIST_CNN(imgB) = 6)
  
likelihood(imgA, imgB, N) = \sum{x,y | x+y=15} (imgA == x && imgB == y)

Maybe we can do Distributional MNist? (Assume for example we have a distribution of x-digit MNIST postal codes and samples from that distribution.
Assume we know the distribution, can we find the MNIST mapping?
 -}
testGaussianMixture :: Expr () a
testGaussianMixture = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Cons ()
    (Plus ()
      (Mult () (Normal ()) (ThetaI () 1))
      (ThetaI () 2))
    (Cons ()
      (Plus ()
        (Mult () (Normal ()) (ThetaI () 3))
        (ThetaI () 4))
      (Null ())))
  (Cons ()
    (Plus ()
      (Mult () (Normal ()) (ThetaI () 5))
      (ThetaI () 6))
    (Cons ()
      (Plus ()
        (Mult () (Normal ()) (ThetaI () 7))
        (ThetaI () 8))
      (Null ())))

gaussianMixture :: Expr () a
gaussianMixture = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Cons ()
    (Plus ()
      (Mult () (Normal ()) (ThetaI () 1))
      (ThetaI () 2))
    (Cons ()
      (Plus ()
        (Mult () (Normal ()) (ThetaI () 3))
        (ThetaI () 4))
      (Cons ()
        (Constant () (VBool True))
        (Null ()))))
  (Cons ()
    (Plus ()
      (Mult () (Normal ()) (ThetaI () 5))
      (ThetaI () 6))
    (Cons ()
      (Plus ()
        (Mult () (Normal ()) (ThetaI () 7))
        (ThetaI () 8))
      (Cons ()
        (Constant () (VBool True))
        (Null ()))))

testIntractable :: Expr () a
testIntractable = Mult ()
  (Mult () (Normal ()) (ThetaI () 1))
  (Mult () (Normal ()) (ThetaI () 2))
  
testInconsistent :: Expr () Double
testInconsistent = IfThenElse ()
  (GreaterThan () (Constant () (VFloat 0.0)) (ThetaI () 0))
  (Constant () (VBool True))
  (Constant () (VBool False))

failureCase :: Expr () a
failureCase = Mult () (Normal ()) (ThetaI () 0)

gaussLists :: Expr () a
gaussLists = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Null ())
  (Cons () (Plus () (Mult () (Normal ()) (ThetaI () 1)) (ThetaI () 2)) (Call () "main"))

gaussMultiLists :: Expr () a
gaussMultiLists = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Null ())
  (Cons ()
    (IfThenElse ()
      (GreaterThan () (Uniform ()) (ThetaI () 1))
      (Plus () (Mult () (Normal ()) (ThetaI () 2)) (ThetaI () 3))
      (Plus () (Mult () (Normal ()) (ThetaI () 4)) (ThetaI () 5)))
    (Call () "main"))
    
testNNUntyped :: Expr () a
--testNN : Lambda im1 -> (Lambda im2 -> readNN im1 + readNN im2)
testNNUntyped = Lambda () "im1" (Lambda () "im2" (Plus () (ReadNN () (Call () "im1")) (ReadNN () (Call () "im2"))))

--mNist im1 im2 = read im1 + read im2
--p(sum | im1, im2)

testNN :: Expr TypeInfo a
testNN = Lambda (TypeInfo (Arrow TSymbol (Arrow TSymbol TInt)) Chaos) "im1"
  (Lambda (TypeInfo (Arrow TSymbol TInt) Chaos) "im2" (Plus (TypeInfo TInt Integrate)
    (ReadNN (TypeInfo TInt Integrate) (Call (TypeInfo TSymbol Deterministic) "im1"))
    (ReadNN (TypeInfo TInt Integrate) (Call (TypeInfo TSymbol Deterministic) "im2"))))

triMNist :: Expr TypeInfo a
triMNist = Lambda (TypeInfo (Arrow TSymbol (Arrow TSymbol (Arrow TSymbol TInt))) Chaos) "im1"
  (Lambda (TypeInfo (Arrow TSymbol (Arrow TSymbol TInt)) Chaos) "im2"
    (Lambda (TypeInfo (Arrow TSymbol TInt) Chaos) "im3" (Plus (TypeInfo TInt Integrate)
      (ReadNN (TypeInfo TInt Integrate) (Call (TypeInfo TSymbol Deterministic) "im3"))
      (Plus (TypeInfo TInt Integrate)
        (ReadNN (TypeInfo TInt Integrate) (Call (TypeInfo TSymbol Deterministic) "im1"))
        (ReadNN (TypeInfo TInt Integrate) (Call (TypeInfo TSymbol Deterministic) "im2")))
      )))


readSamples :: IO [(Double, Double)]
readSamples = do
  f <- readFile "./data/train_data.txt"
  --print $ lines f
  let res = map read $ lines f
  --print res
  return res

map2RSamples :: (Double, Double) -> Value Double
map2RSamples (a,b) = VList [VFloat a, VFloat b]

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

llScan :: (Real a, Floating a, Show a, Enum a) => Env TypeInfo a -> Thetas a -> Expr TypeInfo a -> IO ()
llScan tenv thetas main = do
  let scanPts = [(x,y) | x <- [0, 0.01 .. 1], y <- [0, 0.01 .. 1]]
  let scanRes = [(x, y, likelihood tenv tenv thetas main (VList [VFloat x, VFloat y])) | x <- [0, 0.01.. 1], y <- [0, 0.01.. 1]]
  print scanPts
  print scanRes
  let fileStr = unlines $ map (\(x,y,l) -> show x ++ ", " ++ show y ++ ", " ++ (show $ unwrapP l)) scanRes
  writeFile "./data/ll_out.txt" fileStr

newCodeGen :: Expr TypeInfo Float -> IO ()
newCodeGen tExpr = do
  let annotated = SPLL.Analysis.annotate tExpr
  print annotated
  let irGen = toIRGenerate annotated
  print irGen
  let gen = generateCode irGen
  putStrLn $ unlines gen
  let irProb = toIRProbability annotated (IRVar "input")
  print irProb
  let prob = generateCode irProb
  putStrLn $ unlines prob

newCodeGenAll :: Env TypeInfo Float -> IO ()
newCodeGenAll env = do
  let annotated = map (\(a,b) -> (a, SPLL.Analysis.annotate b)) env
  print annotated
  let ir = envToIR annotated
  print ir
  let code = generateFunctions ir
  putStrLn $ unlines code

someFunc :: IO ()
someFunc = do--thatGaussThing
  --x <- runNNTest
  --print x
  --let env = [("main", testNNUntyped)] :: Env () Float
  --cmp <- compile env triMNist
  --let cmp = [("main", triMNist)] :: Env TypeInfo Float
  --let cmp = [("main", testNN)] :: Env TypeInfo Float
  let env = [("main", testGauss)] :: Env () Float
  cmp2 <- compile env
  newCodeGenAll cmp2
  --let x = transpile cmp
  --print x
  --let y = map mkProbability x
  --mapM_ putStrLn y
  --let env = [("main", testInconsistent)] :: Env () Double
  --only once
  --in testRun "gaussMultiLists" env [0.55, 0.45, 0.5, 0.8, 0.3, 0.4]
  --in testRun "testInconsistent" env [-0.5]
  --repeat a bunch of times:
  --in forM_ [1..100] (\n -> testRun ("gaussMultiLists_" ++ show n) env [0.55, 0.45, 0.5, 0.8, 0.3, 0.4])
  --in forM_ [1..100] (\n -> testRun ("gaussLists_" ++ show n) env [0.5, 0.9, 0.3])

--runNNTest :: IO ()
runNNTest :: IO [Value Float]
runNNTest = do
  print "Running NN Test"
  let typedEnv = [("main", testNN)]
  let Just main = lookup "main" typedEnv
  putStrLn $ unlines $ prettyPrint main
  let resultR = getR main
  print resultR
  let resultP = getP main
  print resultP
  mkSamples 1000 typedEnv [] [Constant (TypeInfo TSymbol Deterministic) (VSymbol "image1"), Constant (TypeInfo TSymbol Deterministic) (VSymbol "image2")] main
  

myGradientAscent :: (Floating a, Real a) => Int -> [(String, Expr TypeInfo a)] -> Thetas a -> Expr TypeInfo a -> [Value a] -> [(Thetas a, a)]
myGradientAscent 0 _ _ _ _ = []
myGradientAscent n env thetas expr vals =
  (thetas, loss) : myGradientAscent (n-1) env new expr vals
    where
      (loss, new) = optimizeStep env expr vals thetas

probabilityDiag :: (Floating a, Ord a, Real a, Show a) => [(String, Expr TypeInfo a)] -> [Thetas a] -> Expr TypeInfo a -> Value a -> IO ()
probabilityDiag env thetaScan expr sample = mapM_ (\theta -> probabilityDiagAt env theta expr sample) thetaScan

probabilityDiagAt :: (Floating a, Ord a, Real a, Show a) => [(String, Expr TypeInfo a)] -> Thetas a -> Expr TypeInfo a -> Value a -> IO ()
probabilityDiagAt env theta expr sample = do
  print theta
  print (likelihood env env theta expr sample)

gradientDiag :: (Floating a, Ord a, Real a, Show a) => [(String, Expr TypeInfo a)] -> [Thetas a] -> Expr TypeInfo a -> [Value a] -> IO ()
gradientDiag env thetaScan expr samples = mapM_ (\theta -> gradientDiagAt env theta expr samples) thetaScan

gradientDiagAt :: (Floating a, Ord a, Real a, Show a) => [(String, Expr TypeInfo a)] -> Thetas a -> Expr TypeInfo a -> [Value a] -> IO ()
gradientDiagAt env tht expr samples = do
  let grad_loss = [grad' (\theta -> log $ unwrapP $ likelihood (autoEnv env) (autoEnv env) theta (autoExpr expr) (autoVal sample)) tht | sample <- samples]
  print ("gradient debug info for theta: " ++ (show tht))
  putStrLn ("gradients: " ++ show (foldl1 addThetas $ map snd grad_loss))
  putStrLn ("LL: " ++ show (sum $ map fst grad_loss))
  --print "LL: "
  --print $ sum $ map fst grad_loss

optimizeStep :: (Floating a, Real a) => Env TypeInfo a -> Expr TypeInfo a -> [Value a] -> Thetas a -> (a, Thetas a)
optimizeStep env expr samples thetas = (loss, addThetas thetas (mult 0.00003 gradient))
  where
    -- does it make a difference if we do sum(gradients) or if we do gradient(sums)?
    -- TODO: Is it correct to apply map-sum, or do we flatten the wrong dimension here?
    --grad_loss :: [(loss :: a, grad :: Thetas a)]
    grad_loss = [grad' (\theta -> log $ unwrapP $ likelihood (autoEnv env) (autoEnv env) theta (autoExpr expr) (autoVal sample)) thetas | sample <- samples]
    --grad_thetas = [Thetas a]
    grad_thetas = map snd grad_loss
    --gradient :: Thetas a
    gradient = foldl1 addThetas grad_thetas
    loss = sum $ map fst grad_loss

exprDebugMetrics :: (Floating a, Real a, Show a, Enum a) => Env TypeInfo a -> Expr TypeInfo a -> [Value a] -> Thetas a -> IO ()
exprDebugMetrics env expr samples thetas = do
  mapM_ (\thX -> printInfo thX) [[x] | x <- [0.0, 0.1 .. 1.0]]
    where
      ll thX = sum [log $ unwrapP $ likelihood env env thX expr sample | sample <- samples]
      grad_loss thX = [grad' (\theta -> log $ unwrapP $ likelihood (autoEnv env) (autoEnv env) theta (autoExpr expr) (autoVal sample)) thX | sample <- samples]
      grad_thetas thX = map snd (grad_loss thX)
      gradient thX = foldl1 addThetas $ grad_thetas thX
      printInfo thX = do
        print (ll thX)
        print (gradient thX)

autoExpr :: (Num a, Reifies s Tape) => Expr x a -> Expr x (Reverse s a)
autoExpr = fmap auto

autoEnv :: (Num a, Reifies s Tape) => Env x a -> Env x (Reverse s a)
autoEnv = map (\ (name, expr) -> (name, autoExpr expr))

autoVal :: (Num a, Reifies s Tape) => Value a -> Value (Reverse s a)
autoVal (VBool x) = VBool x
autoVal (VFloat y) = VFloat (auto y)
autoVal (VList xs) = VList (map autoVal xs)

addThetas :: (Floating a) => Thetas a -> Thetas a -> Thetas a
addThetas x y = zipWith (+) x y

mult :: (Floating a) => a -> Thetas a -> Thetas a
mult x y = map (*x) y

--myGradientAscent :: (Num a, Num b, Num c, Num d) => Int -> Env a -> [b] -> Expr a -> [Value a] -> [([c], d)]
--myGradientAscent 0 _ _ _ _ = []
--myGradientAscent env thetas expr vals = (thetas, loss) : myGradientAscent env newHypothesis expr vals
--  where
    --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
--    loss = sum $ [unwrapP (log $ probability env thetas expr val) | val <- vals]
---    gradient = [sum (grad (\ th -> log $ unwrapP $ _ env th expr datum) thetas) | datum <- vals]
--    newHypothesis = zipWith (+) thetas $ map (\el -> 0.0001 * el) gradient
--pr_ :: (Num a, Num b) => a -> Env b -> [a]

{---setTypeInfo :: Expr x a -> t -> Expr t a
setTypeInfo (IfThenElse x a b c)  t = IfThenElse t a b c
setTypeInfo (GreaterThan x a b)   t = GreaterThan t a b
setTypeInfo (ThetaI x a)          t = ThetaI t a
setTypeInfo (Uniform x)           t = Uniform t
setTypeInfo (Constant x a)        t = Constant t a
setTypeInfo (Mult x a b)          t = Mult t a b
setTypeInfo (Plus x a b)          t = Plus t a b
setTypeInfo (Null x)              t = Null t
setTypeInfo (Cons x a b)          t = Cons t a b
setTypeInfo (Call x a)            t = Call t a
setTypeInfo (LetIn x a b c)       t = LetIn t a b c--}



--Needs to resolve constrained types as a second step.
typeCheckEnv :: Env () a -> Env TypeInfo a
typeCheckEnv env = [(name, typeCheckExpr env expr) | (name, expr) <- env]

--TODO: This should iterate to a fixed point.
resolveConstraints :: Eq a => Env TypeInfo a -> Env TypeInfo a
resolveConstraints en = fixedPointIteration en (\env -> fmap (\(name, t) -> (name, resolveConstraintsExpr env name t)) env) --does this need (Check a ..) type?

--TODO: This may not pass name to subexpr. Instead, name should be left blank then.
resolveConstraintsExpr :: Env TypeInfo a -> String -> Expr TypeInfo a -> Expr TypeInfo a
resolveConstraintsExpr env name = tMapHead (rDeconstrain env name)
                                . tMapHead (pDeconstrain env name)
                                . tMapTails (rDeconstrain env "")
                                . tMapTails (pDeconstrain env "")

-- get the type info of expr. If it is a PIdent constraint, try to relax it. Does not handle recursive PIdents.
-- in a recursive PIdent,
pDeconstrain ::  Env TypeInfo a -> String -> Expr TypeInfo a -> TypeInfo
pDeconstrain env defName expr = TypeInfo rt $ case pt of
    Deterministic -> Deterministic
    Integrate -> Integrate
    Chaos -> Chaos
    -- we're going to have to do a Fixed-point-iteration here to resolve constraints. Only use the lookup results if concrete value
    PIdent name assigns -> if name == defName
        -- direct recursion
        then fixedPointLookup assigns Deterministic
        -- depends on another symbol
        else fromMaybe (PIdent name assigns) pResult
      where
        exprName = lookup name env
        TypeInfo _ pName = getTypeInfo $ fromJust exprName
        pResult = lookup pName assigns
  where
    TypeInfo rt pt = getTypeInfo expr

fixedPointIteration :: Eq a => a -> (a -> a) -> a
fixedPointIteration a f = if b == a then b else fixedPointIteration b f
  where b = f a

recFixedPointLookup :: [(PType, PType)] -> PType -> PType
recFixedPointLookup table = fixedPointLookup (zip (map fst table) cleanedUpSnds)
  where
    --TODO: Sort out any constraints in the following:
    cleanedUpSnds = map snd table

fixedPointLookup :: (Eq a, Show a) => [(a, a)] -> a -> a
fixedPointLookup table start = trace (show table) $ trace (show start) (if res == start then start else fixedPointLookup table res)
  where
    res = fromJust $ lookup start table

rDeconstrain ::  Env TypeInfo a -> String -> Expr TypeInfo a -> TypeInfo
rDeconstrain env defName expr = TypeInfo rt pt
  where
    TypeInfo rtOld pt = getTypeInfo expr
    rt = case rtOld of
      TBool -> TBool
      TFloat -> TFloat
      ListOf x -> ListOf x
      NullList -> NullList
      RIdent name -> rOfName
        where 
          TypeInfo rOfName _ = getTypeInfo $ fromJust $ lookup name env
      RConstraint name ofType resType -> let TypeInfo rOfName _ = getTypeInfo $ fromJust $ lookup name env in
        if defName == name
          --simple recursion
          then if rOfName == RConstraint name resType resType
            --"fn is of type x as long as fn is of type x.
            then resType
            else if rOfName == ofType
              then resType
              else error ("type error in return type constraintA - " ++ show rOfName ++ show ofType)
          else if rOfName == ofType
            then resType
            else RConstraint name ofType resType

compile :: (Show a, Floating a, Ord a) => Env () a -> IO (Env TypeInfo a)
compile env = do
  let pretypedEnv = typeCheckEnv env
  let Just pre_main = lookup "main" pretypedEnv
  putStrLn $ unlines $ prettyPrint pre_main
  let typedEnv = resolveConstraints pretypedEnv
  return typedEnv

reconstructThetas :: (Floating a, Ord a, Random a, Show a, Real a) => Env () a -> Int -> Thetas a -> IO [(Thetas a, a)]
reconstructThetas env nSamples thetas = do
  cEnv <- compile env
  let Just main = lookup "main" cEnv
  samples <- mkSamples nSamples cEnv thetas [] main
  --let initialGuess = replicate (length thetas) 0.5
  initialGuess <- replicateM (length thetas) (getRandomR (0.0, 1.0))
  let reconstructedThetas = myGradientAscent 100 cEnv initialGuess main samples
  return reconstructedThetas

testRun :: (Floating a, Ord a, Random a, Show a, Real a, Enum a) => String -> Env () a -> Thetas a -> IO ()
testRun experimentName env thetas = do
  print "Hello world"
  print env
  let pretypedEnv = typeCheckEnv env
  let Just pre_main = lookup "main" pretypedEnv
  putStrLn $ unlines $ prettyPrint pre_main
  let typedEnv = resolveConstraints pretypedEnv
  let Just main = lookup "main" typedEnv
  putStrLn $ unlines $ prettyPrint main
  let resultR = getR main
  print resultR
  let resultP = getP main
  print resultP
  samples <- mkSamples 1000 typedEnv thetas [] main
  --putStrLn "exprDebugMetrics:"
  --exprDebugMetrics typedEnv main samples ([0.1, 0.1])
  --gradientDiag typedEnv [[x] | x <- [0, 0.01 .. 1]] main samples
  --probabilityDiag typedEnv [[x] | x <- [0, 0.01 .. 3]] main (VFloat 0.1)
  --putStrLn " // exprDebugMetrics:"
  mapM_ print $ count samples
  --let initialThetas = (replicate (length thetas) 0.5)
  initialThetas <- replicateM (length thetas) (getRandomR (0.0, 1.0))
  let thetasRecovered = myGradientAscent 500 typedEnv initialThetas main samples
  mapM_ print thetasRecovered
  --TODO: Handle different theta sizes
  -- also put original thetas as first line.
  let firstline = intercalate ", " $ map show (thetas ++ [0])
  let dataStrs = map (\(ts, d) -> intercalate ", " $ map show (ts ++ [d])) thetasRecovered
  let fileStr = unlines (firstline:dataStrs)
  writeFile ("./data/thetas_out_" ++ experimentName ++ ".txt") fileStr

mkSamples :: (Fractional a, Ord a, Random a) => Int -> Env TypeInfo a -> Thetas a -> [Expr TypeInfo a] -> Expr TypeInfo a -> IO [Value a]
mkSamples 0 _ _ _ _ = return []
mkSamples n env thetas args expr = do
  sample <- evalRandIO $ generate env env thetas args expr
  remainder <- mkSamples (n-1) env thetas args expr
  return (sample:remainder)

count :: Eq a => [a] -> [(Int, a)]
count lst = sortBy (compare `on` (Down . fst)) [(length $ elemIndices x lst, x) | x <- nub lst]

{--
flip theta alpha = if alpha < theta then True else False

probabilityFlip theta sample = if sample then 1 - theta else theta

--test_ad :: [Float]
test_ad = grad (\[x,y,z] -> x*y+z) [1.0,2.0,3.0]

test_ad_2 theta sample = grad (\[th] -> probabilityFlip th sample) [theta]

someFunc :: IO()
someFunc = do
  replicateM_ 10 asdf
  asdf2

sample theta = do
  alpha <- randomIO :: IO Float
  return (Lib.flip theta alpha)

asdf2 = do
  let theta = 0.5
  samples :: [Bool] <- replicateM 1000 (sample theta)
  print samples
  print $ nub samples
  print [(elem, length [x | x <- samples, x == elem]) | elem <- nub samples]
  let gdResult :: [(Float, Float)] = gaIterate 100 0.1 samples --gradientAscent (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [0.1]
  mapM_ print gdResult

gaIterate :: (Eq t, Num t, Floating b) => t -> b -> [Bool] -> [(b, b)]
gaIterate 0 hypothesis samples = [(hypothesis, loss)]
  where
    loss = sum $ [probabilityFlip hypothesis datum | datum <- samples]
gaIterate iterations hypothesis samples = (hypothesis, loss) : gaIterate (iterations-1 ) newHypothesis samples
  where
    --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
    loss = sum $ [probabilityFlip hypothesis datum | datum <- samples]
    gradient = sum $ map sum [grad (\[th] -> log $ probabilityFlip th datum) [hypothesis]| datum <- samples]
    newHypothesis = hypothesis + 0.0001 * gradient

asdf = do
  let theta = 0.5
  alpha <- randomIO :: IO Float
  let sample = Lib.flip theta alpha
  print (test_ad_2 theta sample)
--  print test_nn
--}