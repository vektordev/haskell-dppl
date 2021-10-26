{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Lib
    ( someFunc
    ) where


import Numeric.AD
import System.Random
--import Control.Monad
--import Data.List (transpose, sortBy, elemIndices, nub)
import Data.Maybe
import Control.Monad.Random
import Data.Reflection (Reifies)
import Numeric.AD.Internal.Reverse ( Reverse, Tape)
--import Data.Either (fromRight)
--import Debug.Trace
import Data.Function (on)
import Data.Ord
import Data.List (elemIndices, sortBy, nub)

import Lang
import Typing
import RType
import PType

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

weatherExpr :: Expr () a
weatherExpr = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Null ())
  (Cons () (Constant () (VBool True)) (Call () "main"))

--testExpr :: Num a => Expr a
testExpr :: Expr () a
testExpr = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Constant () (VBool True))
  (Constant () (VBool False))

testExpr2 :: Expr () a
testExpr2 = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Null ())
  (Cons () (Constant () (VBool True)) (Call () "main"))

someFunc :: IO()
someFunc =
  --let env = [("main", testExpr2)] :: Env () Float
  let env = [("main", paramExpr)] :: Env () Float
  in testRun env

myGradientAscent :: (Floating a, Ord a) => Int -> [(String, Expr TypeInfo a)] -> Thetas a -> Expr TypeInfo a -> [Value a] -> [(Thetas a, a)]
myGradientAscent 0 _ _ _ _ = []
myGradientAscent n env thetas expr vals =
  (thetas, loss) : myGradientAscent (n-1) env new expr vals
    where
      (loss, new) = optimizeStep env expr vals thetas

--TODO: can we fix this to use the Foldable theta?
optimizeStep :: (Floating a, Ord a) => Env TypeInfo a -> Expr TypeInfo a -> [Value a] -> Thetas a -> (a, Thetas a)
optimizeStep env expr samples thetas = (loss, addThetas thetas (mult 0.00001 gradient))
  where
    -- does it make a difference if we do sum(gradients) or if we do gradient(sums)?
    -- TODO: Is it correct to apply map-sum, or do we flatten the wrong dimension here?
    --grad_loss :: [(loss :: a, grad :: Thetas a)]
    grad_loss = [grad' (\(theta) -> log $ unwrapP $ probability (autoEnv env) (autoEnv env) theta (autoExpr expr) (autoVal sample)) thetas | sample <- samples]
    --grad_thetas = [Thetas a]
    grad_thetas = map snd grad_loss
    --gradient :: Thetas a
    gradient = foldl1 addThetas grad_thetas
    loss = sum $ map fst grad_loss

autoExpr :: (Num a, Reifies s Tape) => Expr x a -> Expr x (Reverse s a)
autoExpr = fmap auto

autoEnv :: (Num a, Reifies s Tape) => Env x a -> Env x (Reverse s a)
autoEnv = map (\ (name, expr) -> (name, autoExpr expr))

autoVal :: (Num a, Reifies s Tape) => Value a -> Value (Reverse s a)
autoVal (VBool x) = VBool x
autoVal (VFloat y) = VFloat (auto y)
autoVal (VList xs) = VList (map autoVal xs)

type Thetas a = [a]

--instance Traversable Thetas where
--  traverse (Thetas a) = Thetas $ traverse a

findTheta :: Expr x a -> Thetas a -> a
findTheta (ThetaI _ i) (ts) = ts !! i
findTheta expr (ts) = error "called FindTheta on non-theta expr."

addThetas :: (Floating a) => Thetas a -> Thetas a -> Thetas a
addThetas (x) (y) = (zipWith (+) x y)

mult :: (Floating a) => a -> Thetas a -> Thetas a
mult x (y) = map (*x) y

--myGradientAscent :: (Num a, Num b, Num c, Num d) => Int -> Env a -> [b] -> Expr a -> [Value a] -> [([c], d)]
--myGradientAscent 0 _ _ _ _ = []
--myGradientAscent env thetas expr vals = (thetas, loss) : myGradientAscent env newHypothesis expr vals
--  where
    --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
--    loss = sum $ [unwrapP (log $ probability env thetas expr val) | val <- vals]
---    gradient = [sum (grad (\ th -> log $ unwrapP $ _ env th expr datum) thetas) | datum <- vals]
--    newHypothesis = zipWith (+) thetas $ map (\el -> 0.0001 * el) gradient
--pr_ :: (Num a, Num b) => a -> Env b -> [a]



data Probability a = PDF a
                 | DiscreteProbability a
                 deriving (Show)


--Nothing indicates low/high infinity.
data Limits a = Limits (Maybe (Value a)) (Maybe (Value a))

pAnd :: Num a => Probability a -> Probability a -> Probability a
pAnd (PDF a) (PDF b) = PDF (a*b)
pAnd (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a*b)
pAnd (PDF a) (DiscreteProbability b) = PDF (a*b)
pAnd (DiscreteProbability a) (PDF b) = PDF (a*b)

pOr :: Num a => Probability a -> Probability a -> Probability a
pOr (PDF a) (PDF b) = PDF (a+b)
pOr (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a+b)
pOr (PDF a) (DiscreteProbability b) = PDF (a+b)
pOr (DiscreteProbability a) (PDF b) = PDF (a+b)

unwrapP :: Probability a -> a
unwrapP (PDF x) = x
unwrapP (DiscreteProbability x) = x

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


--note: We need detGenerate in order to be able to solve probability: Reverse s a does not have a Random instance,
-- so we have to make do without in probability. Hence if we need to generate, we need to generate deterministically.
detGenerate :: (Fractional a, Ord a) => Env TypeInfo a -> Thetas a -> Expr TypeInfo a -> Value a
detGenerate env thetas (IfThenElse _ cond left right) = do
  case detGenerate env thetas cond of
    VBool True -> detGenerate env thetas left
    VBool False -> detGenerate env thetas right
    _ -> error "Type error"
detGenerate env thetas (GreaterThan _ left right) =
  case (a,b) of
    (VFloat af, VFloat bf) -> VBool (af > bf)
    _ -> error "Type error"
  where
    a = detGenerate env thetas left
    b = detGenerate env thetas right
detGenerate _ thetas expr@(ThetaI _ i) = VFloat (findTheta expr thetas)
detGenerate _ _ (Uniform _) = error "tried to detGenerate from random atom"
detGenerate _ _ (Constant _ x) = x
detGenerate _ _ (Null _) = VList []
detGenerate env thetas (Cons _ hd tl) = VList (detGenerate env thetas hd : xs)
  where VList xs = detGenerate env thetas tl
detGenerate _ _ expr =
  if pt /= Deterministic
  then error "tried detGenerate on non-deterministic expr"
  else error "detGenerate not defined for expr"
    where TypeInfo rt pt = getTypeInfo expr

generate :: (Fractional a, RandomGen g, Ord a, Random a) => Env TypeInfo a -> Env TypeInfo a -> Thetas a -> Expr TypeInfo a -> Rand g (Value a)
generate globalEnv env thetas (IfThenElse _ cond left right) = do
  condV <- generate globalEnv env thetas cond
  case condV of
    VBool True -> generate globalEnv env thetas left
    VBool False -> generate globalEnv env thetas right
    _ -> error "Type error"
generate globalEnv env thetas (GreaterThan _ left right) = do
  a <- generate globalEnv env thetas left
  b <- generate globalEnv env thetas right
  case (a,b) of
    (VFloat af, VFloat bf) -> return $ VBool (af > bf)
    _ -> error "Type error"
generate _ _ thetas expr@(ThetaI _ i) = return $ VFloat (findTheta expr thetas)
generate _ _ _ (Uniform _) = do
  r <- getRandomR (0.0, 1.0) --uniformR (0.0, 1.0)
  return $ VFloat r
generate _ _ _ (Constant _ x) = return x
generate _ _ _ (Null _) = return $ VList []
generate globalEnv env thetas (Cons _ hd tl) = do
  ls <- generate globalEnv env thetas tl
  case ls of
    VList xs -> do
      x <- generate globalEnv env thetas hd
      return $ VList (x : xs)
    _ -> error "type error in list cons"
--Call leaves function context, pass GlobalEnv to ensure env is cleaned up.
generate globalEnv env thetas (Call t name) = generate globalEnv globalEnv thetas expr
  where Just expr = lookup name env

probability :: (Fractional a, Ord a) => Env TypeInfo a -> Env TypeInfo a -> Thetas a -> Expr TypeInfo a -> Value a -> Probability a
-- possible problems in the probability math in there:
probability globalEnv env thetas (IfThenElse t cond left right) val = pOr (pAnd pCond pLeft) (pAnd pCondInv pRight)
  where
    pCond = probability globalEnv env thetas cond (VBool True)
    pCondInv = DiscreteProbability (1 - unwrapP pCond)
    pLeft = probability globalEnv env thetas left val
    pRight = probability globalEnv env thetas right val
probability globalEnv env thetas (GreaterThan t left right) (VBool x)
  | leftP == Deterministic && rightP == Integrate && x     = PDF $ integrate right thetas env (Limits (Just leftGen) Nothing)
  | rightP == Deterministic && leftP == Integrate && x     = PDF $ integrate left thetas env (Limits Nothing (Just rightGen))
  | leftP == Deterministic && rightP == Integrate && not x = PDF $ 1 - integrate right thetas env (Limits (Just leftGen) Nothing)
  | rightP == Deterministic && leftP == Integrate && not x = PDF $ 1 - integrate left thetas env (Limits Nothing (Just rightGen))
  | otherwise = error "undefined probability for greaterThan"
  where
    leftP = getP left
    rightP = getP right
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
probability _ _ thetas expr@(ThetaI _ x) (VFloat val) = if val == (findTheta expr thetas) then DiscreteProbability 1 else DiscreteProbability 0
probability _ _ _ (ThetaI _ _) _ = error "typing error in probability - ThetaI"
probability _ _ _ (Uniform _) (VFloat x) = if 0 <= x && x <= 1 then PDF 1 else PDF 0
probability _ _ _ (Uniform _) _ = error "typing error in probability - Uniform"
probability _ _ _ (Constant _ val) val2 = if val == val2 then DiscreteProbability 1 else DiscreteProbability 0
probability globalEnv env thetas (Mult _ left right) (VFloat x)
  | leftP == Deterministic = probability globalEnv env thetas right (VFloat inverse)
  | rightP == Deterministic = probability globalEnv env thetas left (VFloat inverse)
  | otherwise = error "can't solve Mult"
  where
    leftP = getP left
    rightP = getP right
    VFloat leftGen = detGenerate env thetas left
    VFloat rightGen = detGenerate env thetas right
    inverse = if leftP == Deterministic then x / leftGen else x / rightGen
probability _ _ _ (Null _) (VList []) = DiscreteProbability 1
probability _ _ _ (Null _) _ = DiscreteProbability 0
probability _ _ _ (Cons _ _ _) (VList []) = DiscreteProbability 0
probability globalEnv env thetas (Cons _ hd tl) (VList (x:xs)) = pAnd (probability globalEnv env thetas hd x) (probability globalEnv env thetas tl $ VList xs)
probability globalEnv env thetas (Call _ name) val = probability globalEnv globalEnv thetas expr val
  where Just expr = lookup name env


integrate :: (Num a, Ord a) => Expr TypeInfo a -> Thetas a -> Env TypeInfo a -> Limits a -> a
integrate (Uniform t) thetas env (Limits low high) = h2 - l2
  where
    h2 = min 1 $ maybe 1 unwrap high
    l2 = max 0 $ maybe 0 unwrap low
    unwrap vflt = case vflt of
      VFloat x -> x
      _ -> error "unexpected type-error in RT:Integrate"
integrate _ _ _ _ = error "undefined integrate for expr"


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

--TODO: Verify Env changes are done in a sane manner.

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

fixedPointLookup :: Eq a => [(a, a)] -> a -> a
fixedPointLookup table start = if res == start then start else fixedPointLookup table res
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


testRun :: (Floating a, Ord a, Random a, Show a) => Env () a -> IO ()
testRun env = do
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
  samples <- mkSamples 1000 typedEnv ([0.5]) main
  mapM_ print $ count samples
  let thetasRecovered = myGradientAscent 100 typedEnv ([0.1]) main samples
  print thetasRecovered

mkSamples :: (Fractional a, Ord a, Random a) => Int -> Env TypeInfo a -> Thetas a -> Expr TypeInfo a -> IO [Value a]
mkSamples 0 _ _ _ = return []
mkSamples n env thetas expr = do
  sample <- evalRandIO $ generate env env thetas expr
  remainder <- mkSamples (n-1) env thetas expr
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