module Interpreter where

import Control.Monad.Random

import Lang
import SPLL.Typing.PType
import SPLL.Typing.RType
import SPLL.Typing.Typing

import Statistics.Distribution (ContGen, genContVar, quantile, density)
import Statistics.Distribution.Normal

type Thetas a = [a]

findTheta :: Expr x a -> Thetas a -> a
findTheta (ThetaI _ i) ts = if i >= length ts then error "out of bounds in Thetas" else ts !! i
findTheta _ _ = error "called FindTheta on non-theta expr."

--TODO: Verify Env changes are done in a sane manner in interpreter


--instance Traversable Thetas where
--  traverse (Thetas a) = Thetas $ traverse a

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
detGenerate _ _ (Normal _) = error "tried to detGenerate from random atom"
detGenerate _ _ (Constant _ x) = x
detGenerate _ _ (Null _) = VList []
detGenerate env thetas (Cons _ hd tl) = VList (detGenerate env thetas hd : xs)
  where VList xs = detGenerate env thetas tl
detGenerate _ _ expr =
  if pt /= Deterministic
  then error "tried detGenerate on non-deterministic expr"
  else error "detGenerate not defined for expr"
    where TypeInfo rt pt = getTypeInfo expr

generate :: (Fractional a, RandomGen g, Ord a, Random a) => Env TypeInfo a -> Env TypeInfo a -> Thetas a -> [Expr TypeInfo a] -> Expr TypeInfo a -> Rand g (Value a)
generate globalEnv env thetas [] l@(Lambda _ name expr) = error "no args provided to lambda"
generate globalEnv env thetas (arg:args) (Lambda _ name expr) = generate globalEnv ((name, arg):env ) thetas args expr
generate _ _ _ (_:_) expr = error "args provided to non-lambda"
generate globalEnv env thetas args (IfThenElse _ cond left right) = do
  condV <- generate globalEnv env thetas args cond
  case condV of
    VBool True -> generate globalEnv env thetas args left
    VBool False -> generate globalEnv env thetas args right
    _ -> error "Type error"
generate globalEnv env thetas args (GreaterThan _ left right) = do
  a <- generate globalEnv env thetas args left
  b <- generate globalEnv env thetas args right
  case (a,b) of
    (VFloat af, VFloat bf) -> return $ VBool (af > bf)
    _ -> error "Type error"
generate _ _ thetas args expr@(ThetaI _ i) = return $ VFloat (findTheta expr thetas)
generate _ _ _ args (Uniform _) = do
  r <- getRandomR (0.0, 1.0) --uniformR (0.0, 1.0)
  return $ VFloat r
--TODO: ghastly RNG implementation. Statistics.Distribution offers a RNG implementation that is incompatible with Rand.
generate _ _ _ args (Normal _) = do
  let gauss = normalDistr 0 1
  r <- getRandomR (0.0, 1.0)
  let result = quantile gauss r
  return $ VFloat $ realToFrac result
generate _ _ _ args (Constant _ x) = return x
generate a b c args (Plus _ left right) = do
  leftSample <- generate a b c args left
  rightSample <- generate a b c args right
  case (leftSample, rightSample) of
    (VFloat l, VFloat r) -> return $ VFloat (l + r)
    _ -> error "Type error"
generate a b c args (Mult _ left right) = do
  leftSample <- generate a b c args left
  rightSample <- generate a b c args right
  case (leftSample, rightSample) of
    (VFloat l, VFloat r) -> return $ VFloat (l * r)
    _ -> error "Type error"
generate _ _ _ args (Null _) = return $ VList []
generate globalEnv env thetas args (Cons _ hd tl) = do
  ls <- generate globalEnv env thetas args tl
  case ls of
    VList xs -> do
      x <- generate globalEnv env thetas args hd
      return $ VList (x : xs)
    _ -> error "type error in list cons"
--Call leaves function context, pass GlobalEnv to ensure env is cleaned up.
generate globalEnv env thetas args (Call t name) = generate globalEnv globalEnv thetas args expr
  where Just expr = lookup name env
generate globalEnv env thetas args (ReadNN _ expr) = error "NN not implemented"

sigmoid :: Floating a => a -> a
sigmoid x = 1 / (1 + exp (-x))

likelihood :: (Fractional a, Ord a, Real a, Floating a) => Env TypeInfo a -> Env TypeInfo a -> Thetas a -> Expr TypeInfo a -> Value a -> Probability a
-- possible problems in the probability math in there:
likelihood globalEnv env thetas (IfThenElse t cond left right) val = pOr (pAnd pCond pLeft) (pAnd pCondInv pRight)
  where
    pCond = likelihood globalEnv env thetas cond (VBool True)
    pCondInv = DiscreteProbability (1 - unwrapP pCond)
    pLeft = likelihood globalEnv env thetas left val
    pRight = likelihood globalEnv env thetas right val
likelihood globalEnv env thetas (GreaterThan t left right) (VBool x)
  --consider GreaterThan () (Uniform ()) (ThetaI () 0)
  -- the right side is deterministic. the probability of getting true out of the expr is 1 - theta
  -- rightGen will return theta. Therefore, integrating Uniform from -inf to theta will result in theta.
  | rightP == Deterministic && leftP  == Integrate && x     = DiscreteProbability $ 1 - integrate left thetas env (Limits Nothing (Just rightGen))
  | rightP == Deterministic && leftP  == Integrate && not x = DiscreteProbability $ integrate left thetas env (Limits Nothing (Just rightGen))
  | leftP  == Deterministic && rightP == Integrate && x     = DiscreteProbability $ 1 - integrate right thetas env (Limits (Just leftGen) Nothing)
  | leftP  == Deterministic && rightP == Integrate && not x = DiscreteProbability $ integrate right thetas env (Limits (Just leftGen) Nothing)
  | leftP  == Deterministic && rightP == Deterministic && x = DiscreteProbability $ sigmoid (leftFloat - rightFloat)
  | leftP  == Deterministic && rightP == Deterministic && not x = DiscreteProbability $ sigmoid (rightFloat - leftFloat)
  | otherwise = error "undefined probability for greaterThan"
  where
    leftP = getP left
    rightP = getP right
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
    VFloat leftFloat = leftGen
    VFloat rightFloat = rightGen
likelihood _ _ thetas expr@(ThetaI _ x) (VFloat val) = if val == findTheta expr thetas then DiscreteProbability 1 else DiscreteProbability 0
likelihood _ _ _ (ThetaI _ _) _ = error "typing error in probability - ThetaI"
likelihood _ _ _ (Uniform _) (VFloat x) = if 0 <= x && x <= 1 then PDF 1 else PDF 0
likelihood _ _ _ (Uniform _) _ = error "typing error in probability - Uniform"
--probability _ _ _ (Normal _) (VFloat x) = PDF $ realToFrac $ density (normalDistr 0 1) $ realToFrac x
likelihood _ _ _ (Normal _) (VFloat x) = PDF myDensity
  where myDensity = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)
likelihood _ _ _ (Normal _) _ = error "typing error in probability - Normal"
likelihood _ _ _ (Constant _ val) val2 = if val == val2 then DiscreteProbability 1 else DiscreteProbability 0
likelihood globalEnv env thetas (Mult _ left right) (VFloat x)
  -- need to divide by the deterministic sample
  | leftP == Deterministic || rightP == Deterministic = correctedProbability
  | otherwise = error "can't solve Mult; unexpected type error"
  where
    leftP = getP left
    rightP = getP right
    VFloat leftGen = detGenerate env thetas left
    VFloat rightGen = detGenerate env thetas right
    detSample = if leftP == Deterministic then leftGen else rightGen
    inverse = x / detSample
    PDF inverseProbability = if leftP == Deterministic
      then likelihood globalEnv env thetas right (VFloat inverse)
      else likelihood globalEnv env thetas left (VFloat inverse)
    correctedProbability = PDF (inverseProbability / detSample)
likelihood globalEnv env thetas (Plus _ left right) (VFloat x)
  | leftP == Deterministic = likelihood globalEnv env thetas right (VFloat inverse)
  | rightP == Deterministic = likelihood globalEnv env thetas left (VFloat inverse)
  | otherwise = error "can't solve Plus; unexpected type error"
  where
    leftP = getP left
    rightP = getP right
    VFloat leftGen = detGenerate env thetas left
    VFloat rightGen = detGenerate env thetas right
    inverse = if leftP == Deterministic then x - leftGen else x - rightGen
likelihood _ _ _ (Null _) (VList []) = DiscreteProbability 1
likelihood _ _ _ (Null _) _ = DiscreteProbability 0
likelihood _ _ _ (Cons _ _ _) (VList []) = DiscreteProbability 0
likelihood globalEnv env thetas (Cons _ hd tl) (VList (x:xs)) = pAnd (likelihood globalEnv env thetas hd x) (likelihood globalEnv env thetas tl $ VList xs)
likelihood globalEnv env thetas (Call _ name) val = likelihood globalEnv globalEnv thetas expr val
  where Just expr = lookup name env

-- Cons a [b,c,d] = [a,b,c,d]

--likelihood([a, b, ... l], Cons subExprA subExprB)
-- = (likelihood(a, subExprA) * (likelihood([b, ..., l], subExprB)

integrate :: (Num a, Ord a) => Expr TypeInfo a -> Thetas a -> Env TypeInfo a -> Limits a -> a
integrate (Uniform t) thetas env (Limits low high) = if l2 > 1 || h2 < 0 then 0 else h2 - l2
  where
    h2 = min 1 $ maybe 1 unwrap high
    l2 = max 0 $ maybe 0 unwrap low
    unwrap vflt = case vflt of
      VFloat x -> x
      _ -> error "unexpected type-error in RT:Integrate"
integrate _ _ _ _ = error "undefined integrate for expr"

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
