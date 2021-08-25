{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}

module Lib
    ( someFunc
    ) where


import Numeric.AD
import Linear.Vector
import Linear.Matrix
import System.Random
import Control.Monad
import Data.List
import Control.Monad.Random
import Control.Monad.Except
import Control.Monad.Reader
import Numeric.AD.Internal.Reverse (Reverse)

gradientStep thetas samples = zipWith (+) thetas $ map (0.0001 *) gradient
  where gradient = [sum (grad (\th -> probability th datum) thetas) | datum <- samples]

probability :: (Num a) => [a] -> t -> a
probability = undefined

pr_ :: (Num a, Num b) => a -> Env b -> [a]

{--
data Expr a = IfThenElse (Expr a) (Expr a) (Expr a)
          | GreaterThan (Expr a) (Expr a)
          | ThetaI Int
          | Uniform
          | Constant (Value a)
          | Mult (Expr a) (Expr a)
          | Plus (Expr a) (Expr a)
          | Null
          | Cons (Expr a) (Expr a)
          | Call String
          | LetIn String (Expr a) (Expr a)
          deriving (Show)

data RType = TBool
           | TFloat
           deriving (Show, Eq)

data PType = Deterministic
           | Integrate
           | Chaos
           deriving (Show, Ord, Eq)

data TExpr a = TExpr RType PType (Expr a)
           deriving (Show)

type Env a = [(String, (Expr a))]

data Value a = VFloat a
           | VBool Bool
           deriving (Show)

data Probability a = PDF a
                 | DiscreteProbability a
                 deriving (Show)

type Check a = ExceptT TypeError (Reader (Env a))

data TypeError = Mismatch RType RType
               deriving (Show, Eq)

--TODO: Assert that downgrade Chaos Deterministic = Chaos
downgrade :: PType -> PType -> PType
downgrade = max

upgrade :: PType -> PType -> PType
upgrade = min

matchR :: Num a => Expr a -> Expr a -> Check a RType
matchR e1 e2 = do
  e1R <- inferR e1
  e2R <- inferR e2
  if e1R /= e2R
  then throwError $ Mismatch e1R e2R
  else return e1R

-- make no assumption about thetas
inferR :: Num a => Expr a -> Check a RType
inferR (IfThenElse cond left right) = do
  condR <- inferR cond
  if condR /= TBool
  then throwError $ Mismatch condR TBool
  else matchR left right
inferR (GreaterThan left right) = matchR left right
inferR (ThetaI _) = return TFloat
inferR Uniform = return TFloat
inferR (Constant (VFloat _)) = return TFloat
inferR (Constant (VBool _)) = return TBool
inferR (Mult e1 e2) = matchR e1 e2
inferR (Plus e1 e2) = matchR e1 e2

inferP :: Num a => Expr a -> Check a PType
inferP (IfThenElse _ left right) = do
  leftP <- inferP left
  rightP <- inferP right
  -- assumption: cond is always binomial - this should follow from typing rules.
  return $ downgrade leftP rightP
inferP (GreaterThan left right) = do
  leftP <- inferP left
  rightP <- inferP right
  return $ downgrade leftP rightP
inferP (ThetaI _) = return Deterministic
inferP (Constant _ ) = return Deterministic
inferP Uniform = return Integrate
inferP (Mult left right) = do
  leftP <- inferP left
  rightP <- inferP right
  if downgrade leftP rightP == Deterministic
  then return $ upgrade leftP rightP
  -- we do not know how to integrate over a product
  else return Chaos
inferP (Plus left right) = do
  leftP <- inferP left
  rightP <- inferP right
  if downgrade leftP rightP == Deterministic
  then return $ upgrade leftP rightP
  -- we do not know how to integrate over a sum
  else return Chaos
inferP Null = return Deterministic
inferP (Cons head tail) = do
  -- TODO: Assumes independence. Invalid if there exists x elem Env that is used in head and tail.
  headP <- inferP head
  tailP <- inferP tail
  return $ downgrade headP tailP
inferP (Call name) = undefined --TODO: here there be dragons

generate :: (RandomGen g, Num a, Ord a, Random a) => Env a -> [a] -> Expr a -> Rand g (Value a)
generate env thetas (IfThenElse cond left right) = do
  condV <- generate env thetas cond
  case condV of
    VBool True -> generate env thetas left
    VBool False -> generate env thetas right
    _ -> error "Type error"
generate env thetas (GreaterThan left right) = do
  a <- generate env thetas left
  b <- generate env thetas right
  case (a,b) of
    (VFloat a, VFloat b) -> return $ VBool (a > b)
    _ -> error "Type error"
generate env thetas (ThetaI i) = return $ VFloat (thetas !! i)
generate env thetas Uniform = do
  r <- getRandomR (0.0, 1.0) --uniformR (0.0, 1.0)
  return $ VFloat r

pAnd :: Num a => Probability a -> Probability a -> Probability a
pAnd (PDF a) (PDF b) = PDF (a*b)
pAnd (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a*b)

pOr :: Num a => Probability a -> Probability a -> Probability a
pOr (PDF a) (PDF b) = PDF (a+b)
pOr (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a+b)

probability :: Num a => Env a -> [a] -> Expr a -> Value a -> Probability a
-- possible problems in the probability math in there:
probability env thetas (IfThenElse cond left right) val = pOr (pAnd pCond pLeft) (pAnd pCond pRight)
  where
    pCond = probability env thetas cond (VBool True)
    pLeft = probability env thetas left val
    pRight = probability env thetas right val
probability env thetas (GreaterThan left right) val = undefined
--}
{--
data SPN = Leaf Float Float | Product [SPN] | Sum [(SPN, Float)]  

data NN = NN [NNLayer]

data NNLayer = NNLayer [[Float]] Activation

data Activation = Sigmoid | ReLU | Rational | CoRational

--runNNLayer :: NNLayer -> Vector -> Vector
--runNNLayer layer inp = undefined
  
--someFunc :: IO ()
--someFunc = putStrLn "someFunc"
--  where struct = Product [Leaf 0 0.5, Leaf 0.5, 0.5]

--mse :: Float -> Float -> Float

--imaginaryData :: [([Float], Float)]
imaginaryData = [([x, y, z], [x*x]) | x <- [1..10], y <- [1..10], z <- [1..10]]

--nnLayer ::  -> Vector -> Vector
--nnLayer :: (Foldable r, Additive r, Functor f, Ord b, Num b) => f (r b) -> r b -> f b
nnLayer matrix input = fmap activation (matrix !* input)
  where activation = relu

--relu :: (Ord p, Num p) => p -> p
relu preactivation = if preactivation < 0 then 0 else preactivation

--imNN :: (Fractional a, Foldable t, Foldable r, Additive t, Additive r, Ord a) => t (r a) -> r a -> t a -> a
imNN matrix x y = mseVec (nnLayer matrix x) y

--mseVec :: (Fractional a, Foldable t, Additive t) => t a -> t a -> a
mseVec a b = sum se / realToFrac(length se)
  where se = fmap (\el -> el * el) (a ^-^ b)

--mse :: Num a => a -> a -> a
mse a b = (a-b) * (a-b)


--initMatrix :: [[Float]]
initMatrix = [[1,2,3],[4,5,6]]

testResult = imNN initMatrix (fst $ head imaginaryData) (snd $ head imaginaryData)

test_nn = grad (\mat -> imNN mat (auto x) (auto y)) initMatrix
  where
    x = fst $ head imaginaryData
    y = snd $ head imaginaryData
-}
{--
testRun :: Num a => Env a -> IO ()
testRun env = do
  print env
  let Just main = lookup "main" env
  samples <- mkSamples 1000 env [0.5] main
  let thetasRecovered = myGradientAscent 100 env [0.1] main samples
  print (reverse thetasRecovered)

mkSamples :: Num a => Int -> Env a -> [a] -> Expr a -> IO [Value a]
mkSamples 0 _ _ _ = return []
mkSamples n env thetas expr = do
  sample <- evalRandIO $ generate env thetas expr
  tail <- mkSamples (n-1) env thetas expr
  return (sample:tail)

unwrapP :: Num a => Probability a -> a
unwrapP (PDF x) = x
unwrapP (DiscreteProbability x) = x

--myGradientAscent :: (Num a, Num b, Num c, Num d) => Int -> Env a -> [b] -> Expr a -> [Value a] -> [([c], d)]
--myGradientAscent 0 _ _ _ _ = []
myGradientAscent n env thetas expr vals = (thetas, loss) : myGradientAscent (n-1) env newHypothesis expr vals
  where
    --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
    loss = sum $ [unwrapP (log $ probability env thetas expr val) | val <- vals]
    gradient = [sum (grad (\ th -> log $ unwrapP $ _ env th expr datum) thetas) | datum <- vals]
    newHypothesis = zipWith (+) thetas $ map (\el -> 0.0001 * el) gradient

testing2 :: Num a => p1 -> p2 -> p3 -> [a] -> [a]
testing2 env expr datum = grad (\ th -> unwrapP $ _ env th expr datum)

testing4 :: Fractional a => [a] -> a
testing4 th = unwrapP $ probability [] th Null $ VFloat 0.0

testing5 :: [a] -> [a]
testing5 = grad testing4

testing6 :: [a] -> [a]
testing6 = grad (log testing4)
-}
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
