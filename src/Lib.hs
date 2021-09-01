{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}

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
import Data.Reflection (Reifies)
import Numeric.AD.Internal.Reverse (Reverse)
import Numeric.AD.Internal.Reverse (Tape)

--assumption about grad: Reverse s a is Num if a is Num.
--Thererfore, grad :: (Traversable f, Num a) => (forall s. Reifies s Tape => f (Reverse s a) -> Reverse s a) -> f a -> f a
-- essentially translates to grad :: Traversable f, Num a) => (f (Reverse s a) -> Reverse s a) -> f a -> f a
-- or more simply: grad takes any function :: Traversable f, Num a => f a -> a;
-- but then we have to sort out the type of the hypothesis (a)

--someFunc = print "Hello world"

--testExpr :: Num a => Expr a
testExpr = IfThenElse
  (GreaterThan Uniform (ThetaI 0))
  (Constant (VBool True))
  (Constant (VBool False))

someFunc :: IO()
someFunc =
  let env = [("main", testExpr)] :: Env Float
  in testRun env
  

--gradientStep thetas samples = zipWith (+) thetas $ map (0.0001 *) gradient
--  where gradient = [sum (grad (\th -> probability th datum) thetas) | datum <- samples]

--lambdathing :: forall s a2. (Num a2, Reifies s Tape) => 
lambdathing :: Num a => Env a -> Expr a -> Value a -> [a] -> a
lambdathing env expr sample theta = unwrapP $ probability env theta expr sample

something :: Num a => Env a -> Expr a -> Value a -> [a] -> [a]
something env expr sample = grad (\(theta) -> unwrapP $ probability (autoEnv env) theta (autoExpr expr) (autoVal sample))

myGradientAscent 0 _ _ _ _ = []
myGradientAscent n env thetas expr vals =
  (thetas, loss) : myGradientAscent (n-1) env new expr vals
    where
      --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
      (loss, new) = optimizeStep env expr vals thetas

--TODO: can we fix this to use the Foldable theta?
optimizeStep :: (Fractional a, Num a) => Env a -> Expr a -> [Value a] -> [a] -> (a, [a])
optimizeStep env expr samples thetas = (loss, zipWith (+) thetas $ map (*0.0001) gradient)
  where
    -- does it make a difference if we do sum(gradients) or if we do gradient(sums)?
    -- TODO: Is it correct to apply map-sum, or do we flatten the wrong dimension here?
    --grad_loss :: [(loss :: a, grad :: [a])]
    grad_loss = [grad' (\(theta) -> unwrapP $ probability (autoEnv env) theta (autoExpr expr) (autoVal sample)) thetas | sample <- samples]
    gradient = map sum $ Data.List.transpose $ map snd grad_loss
    loss = sum $ map fst grad_loss

autoExpr :: (Num a, Reifies s Tape) => Expr a -> Expr (Reverse s a)
autoExpr e = fmap auto e

autoEnv :: (Num a, Reifies s Tape) => Env a -> Env (Reverse s a)
autoEnv xs = map (\(name, expr) -> (name, autoExpr expr)) xs

autoVal :: (Num a, Reifies s Tape) => Value a -> Value (Reverse s a)
autoVal (VBool x) = VBool x
autoVal (VFloat y) = VFloat (auto y)

--myGradientAscent :: (Num a, Num b, Num c, Num d) => Int -> Env a -> [b] -> Expr a -> [Value a] -> [([c], d)]
--myGradientAscent 0 _ _ _ _ = []
--myGradientAscent env thetas expr vals = (thetas, loss) : myGradientAscent env newHypothesis expr vals
--  where
    --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
--    loss = sum $ [unwrapP (log $ probability env thetas expr val) | val <- vals]
---    gradient = [sum (grad (\ th -> log $ unwrapP $ _ env th expr datum) thetas) | datum <- vals]
--    newHypothesis = zipWith (+) thetas $ map (\el -> 0.0001 * el) gradient
--pr_ :: (Num a, Num b) => a -> Env b -> [a]


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

instance Functor Expr where
  fmap = exprMap

exprMap :: (a -> b) -> Expr a -> Expr b
exprMap f (IfThenElse a b c) = IfThenElse (fmap f a) (fmap f b) (fmap f c)
exprMap f (GreaterThan a b) = GreaterThan (fmap f a) (fmap f b)
exprMap f (ThetaI x) = ThetaI x
exprMap f Uniform = Uniform
exprMap f (Constant x) = Constant $ fmap f x
exprMap f (Mult a b) = Mult (fmap f a) (fmap f b)
exprMap f (Plus a b) = Plus (fmap f a) (fmap f b)
exprMap f Null = Null
exprMap f (Cons a b) = Cons (fmap f a) (fmap f b)
exprMap f (Call x) = Call x
exprMap f (LetIn x a b) = LetIn x (fmap f a) (fmap f b)


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

instance Functor Value where
    fmap f (VFloat a) = VFloat $ f a
    fmap f (VBool a) = VBool a

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

pAnd :: Num a => Probability a -> Probability a -> Probability a
pAnd (PDF a) (PDF b) = PDF (a*b)
pAnd (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a*b)

pOr :: Num a => Probability a -> Probability a -> Probability a
pOr (PDF a) (PDF b) = PDF (a+b)
pOr (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a+b)

unwrapP :: Num a => Probability a -> a
unwrapP (PDF x) = x
unwrapP (DiscreteProbability x) = x

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
inferR (GreaterThan left right) = do
  e1R <- inferR left
  e2R <- inferR right
  if e1R /= e2R
  then throwError $ Mismatch e1R e2R
  else return TBool
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

generate :: (Fractional a, RandomGen g, Num a, Ord a, Random a) => Env a -> [a] -> Expr a -> Rand g (Value a)
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
generate env thetas (Constant x) = return x

probability :: Num a => Env a -> [a] -> Expr a -> Value a -> Probability a
-- possible problems in the probability math in there:
probability env thetas (IfThenElse cond left right) val = pOr (pAnd pCond pLeft) (pAnd pCond pRight)
  where
    pCond = probability env thetas cond (VBool True)
    pLeft = probability env thetas left val
    pRight = probability env thetas right val
probability env thetas (GreaterThan left right) val = undefined

prettyPrint :: (Num a, Show a) => Env a -> Expr a -> [String]
prettyPrint env expr = 
  fstLine : indented
    where
      childExprs = recurse expr
      indented = map indent $ concatMap (prettyPrint env) childExprs :: [String]
      indent ls = "    " ++ ls
      rType = runReader (runExceptT (inferR expr)) env
      pType = runReader (runExceptT (inferP expr)) env
      fstLine = printFlat expr ++ " [" ++ show rType ++ " | " ++ show pType ++ "]"

recurse :: Expr a -> [Expr a]
recurse (IfThenElse a b c) = [a,b,c]
recurse (GreaterThan a b) = [a,b]
recurse (ThetaI _) = []
recurse (Uniform) = []
recurse (Constant _) = []
recurse (Mult a b) = [a,b]
recurse (Plus a b) = [a,b]
recurse (Null) = []
recurse (Cons a b) = [a,b]
recurse (Call _) = []
recurse (LetIn _ a b) = [a,b]

printFlat :: Show a => Expr a -> String
printFlat (IfThenElse _ _ _) = "IfThenElse"
printFlat (GreaterThan _ _) = "GreaterThan"
printFlat (ThetaI i) = "Theta_" ++ show i
printFlat Uniform = "Uniform"
printFlat (Constant x) = "Constant (" ++ show x ++ ")"
printFlat (Mult _ _) = "Mult"
printFlat (Plus _ _) = "Plus"
printFlat Null = "Null"
printFlat (Cons _ _) = "Cons"
printFlat (Call a) = "Call" ++ a
printFlat (LetIn _ _ _ ) = "LetIn"

testRun :: (Num a, Fractional a, Ord a, Random a, Show a) => Env a -> IO ()
testRun env = do
  print env
  let Just main = lookup "main" env
  putStrLn $ unlines $ prettyPrint env main
  let resultR = runReader (runExceptT (inferR main)) env
  print resultR
  let resultP = runReader (runExceptT (inferP main)) env
  print resultP
  samples <- mkSamples 1000 env [0.5] main
  mapM_ print samples
  let thetasRecovered = myGradientAscent 100 env [0.1] main samples
  print (reverse thetasRecovered)

mkSamples :: (Fractional a, Num a, Ord a, Random a) => Int -> Env a -> [a] -> Expr a -> IO [Value a]
mkSamples 0 _ _ _ = return []
mkSamples n env thetas expr = do
  sample <- evalRandIO $ generate env thetas expr
  tail <- mkSamples (n-1) env thetas expr
  return (sample:tail)

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