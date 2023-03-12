{-# LANGUAGE FlexibleContexts #-}
module Interpreter where

import Control.Monad.Random

import Numeric.AD
import SPLL.Lang
import SPLL.Typing.PType
import SPLL.Typing.RType
import SPLL.Typing.Typing
import qualified Data.Set as Set
import Debug.Trace
import Numeric.AD (grad, auto)
import Statistics.Distribution (ContGen, genContVar, quantile, density)
import Statistics.Distribution.Normal
import InjectiveFunctions
import Numeric.AD.Internal.Reverse ( Reverse, Tape)
import qualified Data.Map as Map
import Data.Reflection (Reifies)
import Data.Number.Erf

type Thetas a = [a]

findTheta :: Expr x a -> Thetas a -> a
findTheta (ThetaI _ i) ts = if i >= length ts then error "out of bounds in Thetas" else ts !! i
findTheta _ _ = error "called FindTheta on non-theta expr."

--TODO: Verify Env changes are done in a sane manner in interpreter

--instance Traversable Thetas where
--  traverse (Thetas a) = Thetas $ traverse a

--note: We need detGenerate in order to be able to solve probability: Reverse s a does not have a Random instance,
-- so we have to make do without in probability. Hence if we need to generate, we need to generate deterministically.
detGenerate :: (Floating a, Fractional a, Ord a) => Env TypeInfoWit a -> Thetas a -> Expr TypeInfoWit a -> Value a
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
detGenerate env thetas (Plus _ left right) = if pt1 == Deterministic && pt2 == Deterministic
  then VFloat (val1 + val2)
  else error "detGenerate non-deterministic plus"
  where
    (TypeInfoWit rt1 pt1 _) = getTypeInfo left
    (TypeInfoWit rt2 pt2 _) = getTypeInfo right
    (VFloat val1) = detGenerate env thetas left
    (VFloat val2) = detGenerate env thetas right
detGenerate env thetas (Mult _ left right) = if pt1 == Deterministic && pt2 == Deterministic
  then VFloat (val1 * val2)
  else error "detGenerate non-deterministic mult"
  where
    (TypeInfoWit rt1 pt1 _) = getTypeInfo left
    (TypeInfoWit rt2 pt2 _) = getTypeInfo right
    (VFloat val1) = detGenerate env thetas left
    (VFloat val2) = detGenerate env thetas right
detGenerate _ thetas expr@(ThetaI _ i) = VFloat (findTheta expr thetas)
detGenerate _ _ (Uniform _) = error "tried to detGenerate from random atom"
detGenerate _ _ (Normal _) = error "tried to detGenerate from random atom"
detGenerate _ _ (Constant _ x) = x
detGenerate _ _ (Null _) = VList []
detGenerate _ _ (TNull _) = VTuple []
detGenerate env thetas (Cons _ hd tl) = VList (detGenerate env thetas hd : xs)
  where VList xs = detGenerate env thetas tl
detGenerate env thetas (TCons _ hd tl) = VTuple (detGenerate env thetas hd : xs)
  where VList xs = detGenerate env thetas tl
detGenerate env thetas (Call t name) = detGenerate env thetas expr
  where Just expr = lookup name env
detGenerate env thetas (Var t name) = detGenerate env thetas expr
  where Just expr = lookup name env
detGenerate env thetas (InjF t name params expr) = forward params_val innerVal
  where (Just (FPair fPair)) = lookup name globalFenv
        (_, forward, _, _) = fPair
        innerVal = detGenerate env thetas expr
        params_val = map (detGenerate env thetas) params
detGenerate _ _ expr =
  if pt /= Deterministic
  then error "tried detGenerate on non-deterministic expr"
  else error "detGenerate not defined for expr"
    where TypeInfoWit rt pt _ = getTypeInfo expr

generate :: (Fractional a, RandomGen g, Ord a, Random a, Floating a) => Env TypeInfoWit a -> Env TypeInfoWit a -> Thetas a -> [Expr TypeInfoWit a] -> Expr TypeInfoWit a -> Rand g (Value a)
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
generate _ _ _ args (TNull _) = return $ VTuple []
generate globalEnv env thetas args (Cons _ hd tl) = do
  ls <- generate globalEnv env thetas args tl
  case ls of
    VList xs -> do
      x <- generate globalEnv env thetas args hd
      return $ VList (x : xs)
    _ -> error "type error in list cons"
generate globalEnv env thetas args (TCons _ hd tl) = do
  ls <- generate globalEnv env thetas args tl
  case ls of
    VTuple xs -> do
      x <- generate globalEnv env thetas args hd
      return $ VTuple (x : xs)
    _ -> error "type error in list cons"
--Call leaves function context, pass GlobalEnv to ensure env is cleaned up.
generate globalEnv env thetas args (Call t name) = generate globalEnv globalEnv thetas args expr
  where Just expr = lookup name globalEnv
generate globalEnv env thetas args (Var t name) = generate globalEnv globalEnv thetas args expr
  where Just expr = lookup name env
generate globalEnv env thetas args (ReadNN _ expr) = error "NN not implemented"
generate globalEnv env thetas args (LetIn _ name decl bij) =
  do
    declValue <- generate globalEnv env thetas args decl
    let (VFloat val) = declValue
    let extendedEnv = (name, Constant (TypeInfoWit (getRType declValue) Deterministic Set.empty) declValue):env
    generate globalEnv extendedEnv thetas args bij
generate globalEnv env thetas args (InjF _ name params f2) =
  do
    let (Just (FPair fPair)) = lookup name globalFenv
    let (_, forward, _, _) = fPair
    innerVal <- generate globalEnv env thetas args f2
    let params_val = map (detGenerate env thetas) params
    return (forward params_val innerVal)

callInv :: (Floating a) => FEnv2 a -> String -> Params a -> a -> a
callInv fenv name pa va = idd pa va
  where (Just (FPair2 fPair)) = lookup name fenv
        (_, idd, _) = fPair


sigmoid :: Floating a => a -> a
sigmoid x = 1 / (1 + exp (-x))

--TODO expand to more vars
replaceEnvBranch :: (Show a) => (Env TypeInfoWit a, Env TypeInfoWit a)  -> String -> (Env TypeInfoWit a, Env TypeInfoWit a)
replaceEnvBranch (envS1, envS2) var = (env1, env2)
  where Just (Constant ti (VBranch val1 val2 bName)) =  lookup var envS1
        envNoB1 = filter (\x -> fst x /= var) envS1
        envNoB2 = filter (\x -> fst x /= var) envS2
        env1 = (var, Constant ti val1):envNoB1
        env2 = (var, Constant ti val2):envNoB2

branchedCompare :: (Ord a, Eq a, Floating a) => Value a -> Value a -> Probability a
branchedCompare (VBranch val1 val2 x) comp = BranchedProbability (branchedCompare val1 comp) (branchedCompare val2 comp) x
branchedCompare (VFloat x) (VRange l@(Limits _ _)) = if isInRange l x then DiscreteProbability 1 else DiscreteProbability 0
branchedCompare val1 val2 = if val1 == val2 then DiscreteProbability 1 else DiscreteProbability 0

isInRange :: (Ord a) => Limits a ->  a -> Bool
isInRange (Limits Nothing Nothing) _ = True
isInRange (Limits Nothing (Just (VFloat x))) z = z <= x
isInRange (Limits (Just (VFloat x)) Nothing) z = z <= x
isInRange (Limits (Just (VFloat x)) (Just (VFloat y))) z = z <= y && z >= x

applyCorBranch :: (Floating a) => Probability a -> Value a -> Probability a
applyCorBranch (BranchedProbability p1 p2 x) (VBranch v1 v2 y)
  | x == y = BranchedProbability (applyCorBranch p1 v1) (applyCorBranch p2 v2) x
  | otherwise = error "wrong variables appluCor"
applyCorBranch (BranchedProbability p1 p2 x) vv@(VFloat v) = BranchedProbability (applyCorBranch p1 vv) (applyCorBranch p2 vv) x
applyCorBranch (PDF p) (VFloat v) = PDF (p * v)
applyCorBranch (DiscreteProbability p) (VFloat v) = DiscreteProbability (p * v)

likelihood :: (Erf a, Show a, Fractional a, Ord a, Real a, Floating a) => Env TypeInfoWit a -> Env TypeInfoWit a -> Thetas a -> Expr TypeInfoWit a -> BranchMap a -> Value a -> Probability a
-- possible problems in the probability math in there:
likelihood _ _ _ expr _ _
  | getPW expr == Bottom = error "cannot calculate likelihood for bottom type"
likelihood globalEnv env thetas ee@(IfThenElse t cond left right) branchMap val = case Map.lookup ee branchMap of
   (Just [branchName]) -> let (env1, env2) = foldl replaceEnvBranch (env, env) [branchName] in
     BranchedProbability (pAnd pCond (likelihood globalEnv env1 thetas left branchMap val))
                         (pAnd pCondInv (likelihood globalEnv env2 thetas right branchMap val)) branchName
   Nothing -> pOr (pAnd pCond pLeft) (pAnd pCondInv pRight)
  where
    -- No Intersection
    pCond = likelihood globalEnv env thetas cond branchMap (VBool True)
    pCondInv = DiscreteProbability (1 - unwrapP pCond)
    pLeft = likelihood globalEnv env thetas left branchMap val
    pRight = likelihood globalEnv env thetas right branchMap val

likelihood globalEnv env thetas (GreaterThan t left right) branchMap (VBool x)
  --consider GreaterThan () (Uniform ()) (ThetaI () 0)
  -- the right side is deterministic. the probability of getting true out of the expr is 1 - theta
  -- rightGen will return theta. Therefore, integrating Uniform from -inf to theta will result in theta.
  | rightP == Deterministic && leftP  == Integrate && x     = DiscreteProbability $ 1 - integrate left thetas (Limits Nothing (Just rightGen))
  | rightP == Deterministic && leftP  == Integrate && not x = DiscreteProbability $ integrate left thetas (Limits Nothing (Just rightGen))
  | leftP  == Deterministic && rightP == Integrate && x     = DiscreteProbability $ 1 - integrate right thetas (Limits (Just leftGen) Nothing)
  | leftP  == Deterministic && rightP == Integrate && not x = DiscreteProbability $ integrate right thetas (Limits (Just leftGen) Nothing)
  | leftP  == Deterministic && rightP == Deterministic && x = DiscreteProbability $ sigmoid (leftFloat - rightFloat)
  | leftP  == Deterministic && rightP == Deterministic && not x = DiscreteProbability $ sigmoid (rightFloat - leftFloat)
  | otherwise = error "undefined probability for greaterThan"
  where
    leftP = getPW left
    rightP = getPW right
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
    VFloat leftFloat = leftGen
    VFloat rightFloat = rightGen
likelihood _ _ thetas expr@(ThetaI _ x) _ val2 = branchedCompare (VFloat (findTheta expr thetas)) val2
likelihood _ _ _ (Uniform _) _ (VFloat x) = if 0 <= x && x <= 1 then PDF 1 else PDF 0
likelihood _ _ thetas (Uniform t) _ (VRange limits) = DiscreteProbability $ integrate (Uniform t) thetas limits
--likelihood _ _ _ (Uniform _) _ (VRange OpenInterval (VFloat x)) = DiscreteProbability
--likelihood _ _ _ (Uniform _) _ (VRange OpenInterval OpenInterval) = DiscreteProbability

likelihood globalEnv env thetas d@(Uniform _) branchMap (VBranch v1 v2 x)  = BranchedProbability (lf v1) (lf v2) x
  where lf = likelihood globalEnv env thetas d branchMap
--probability _ _ _ (Normal _) (VFloat x) = PDF $ realToFrac $ density (normalDistr 0 1) $ realToFrac x
likelihood _ _ _ (Normal _) _ (VFloat x) = PDF myDensity
  where myDensity = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)
likelihood _ _ thetas (Normal t) _ (VRange limits) = DiscreteProbability $ integrate (Normal t) thetas limits

likelihood _ _ _ (Constant _ val) _ val2 = branchedCompare val val2
likelihood globalEnv env thetas (Mult _ left right) branchMap (VRange limits)
  -- need to divide by the deterministic sample
  | leftP == Deterministic || rightP == Deterministic = inverseProbability
  | otherwise = error "can't solve Mult; unexpected type error"
  where
    leftP = getPW left
    rightP = getPW right
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
    VFloat detSample = if leftP == Deterministic then leftGen else rightGen
    inverse = fmap (flip(/) detSample) (VRange limits)
    inverse_flip = if detSample < 0 then swapLimits inverse else inverse
    inverseProbability = if leftP == Deterministic
      then likelihood globalEnv env thetas right branchMap inverse_flip
      else likelihood globalEnv env thetas left branchMap inverse_flip
likelihood globalEnv env thetas (Mult _ left right) branchMap (VFloat x)
  -- need to divide by the deterministic sample
  | leftP == Deterministic || rightP == Deterministic = correctedProbability
  | otherwise = error "can't solve Mult; unexpected type error"
  where
    leftP = getPW left
    rightP = getPW right
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
    detSample = if leftP == Deterministic then leftGen else rightGen
    inverse = fmap ((*x) . ((/)1)) detSample
    inverseProbability = if leftP == Deterministic
      then likelihood globalEnv env thetas right branchMap inverse
      else likelihood globalEnv env thetas left branchMap inverse
    correctedProbability = (applyCorBranch inverseProbability (fmap (abs . ((/)1)) detSample))
likelihood globalEnv env thetas (Plus _ left right) branchMap val
  | leftP == Deterministic = case val of
    (VFloat x) -> likelihood globalEnv env thetas right branchMap (inverse x)
    (VRange limits) -> likelihood globalEnv env thetas right branchMap (inverse_nob (VRange limits))
  | rightP == Deterministic = case val of
    (VFloat x) -> likelihood globalEnv env thetas left branchMap (inverse x)
    (VRange limits) -> likelihood globalEnv env thetas left branchMap (inverse_nob (VRange limits))
  | otherwise = error "can't solve Plus; unexpected type error"
  where
  -- TODO: Branching for range queries
    leftP = getPW left
    rightP = getPW right
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
    detSample = if leftP == Deterministic then leftGen else rightGen
    VFloat vflDet = detSample
    inverse x = fmap ((+x) . (*(-1))) detSample
    inverse_nob x = fmap (flip(-) vflDet) x
-- TODO lists as variables with branching

likelihood _ _ _ (Null _) _ (VList []) = DiscreteProbability 1
likelihood _ _ _ (Null _) _ _ = DiscreteProbability 0
likelihood _ _ _ (TNull _) _ (VTuple []) = DiscreteProbability 1
likelihood _ _ _ (TNull _) _ _ = DiscreteProbability 0
likelihood _ _ _ (Cons _ _ _) _ (VList []) = DiscreteProbability 0
likelihood globalEnv env thetas (Cons _ hd tl) branchMap (VList (x:xs)) =
        (pAnd (likelihood globalEnv env thetas hd branchMap x) (likelihood globalEnv env thetas tl branchMap $ VList xs) )
      
likelihood _ _ _ (TCons _ _ _) _ (VTuple []) = DiscreteProbability 0
likelihood globalEnv env thetas (TCons _ hd tl) branchMap (VTuple (x:xs)) =
  pAnd (likelihood globalEnv env thetas hd branchMap x) (likelihood globalEnv env thetas tl branchMap $ VTuple xs)

likelihood globalEnv env thetas (Call _ name) branchMap val = likelihood globalEnv globalEnv thetas expr branchMap val
  where Just expr = lookup name env
likelihood globalEnv env thetas (Var _ name) branchMap val = likelihood globalEnv globalEnv thetas expr branchMap val
  where Just expr = lookup name env
-- Cons a [b,c,d] = [a,b,c,d]

--likelihood([a, b, ... l], Cons subExprA subExprB)
-- = (likelihood(a, subExprA) * (likelihood([b, ..., l], subExprB)
likelihood globalEnv env thetas inj@(InjF ti name params expr) branchMap val =
  likelihood globalEnv env thetas expr branchMap invVal `pAnd` (DiscreteProbability $ abs (inverse_grad params_val val))
  where (Just (FPair (_, forward, inverse, inverse_grad))) = lookup name globalFenv
        --inverse_grad_auto = grad' (\[val] -> callInv globalFenv2 name (map autoVal params_val) val) [vfloat_val]
        --(VFloat vfloat_val) = val
        params_val = map (detGenerate env thetas) params
        invVal = inverse params_val val
        
-- expr -> let x = normal in sig(x) 
-- likelihood(0.2|expr) = (x = inverse_sig(0.2)) --> 
likelihood globalEnv env thetas (LetIn _ name decl bij) branchMap val
-- pAnd p_cor
  | getPTypeW (getTypeInfo decl) == Integrate =
    case likelihoodForValue (likelihood globalEnv env thetas decl branchMap) baseDistV name `pAnd` e2Dist of
      (BranchedProbability p1 p2 branch) -> marginalizeBranches (BranchedProbability p1 p2 branch) name
      p -> p
  | getPTypeW (getTypeInfo decl) == Deterministic = likelihood globalEnv extendedEnvD thetas bij branchMap val
  | otherwise = error "non exhaustive letin (bottom type perhaps)"
  where -- Integrate case
        (baseDistV, cor_factor, branchMapE) = getInvValue globalFenv globalEnv env thetas bij name val 1.0
        extendedEnvI = (name, Constant (TypeInfoWit TFloat Deterministic Set.empty) baseDistV):env
        e2Dist = likelihood globalEnv extendedEnvI thetas bij (Map.unionWith (++) branchMap branchMapE) val
        -- Deterministic case
        -- Could replace this with value env
        extendedEnvD = (name, Constant (TypeInfoWit TFloat Deterministic Set.empty) (detGenerate env thetas decl)):env

likelihood globalEnv env thetas d branchMap (VBranch v1 v2 x) = BranchedProbability (lf v1) (lf v2) x
  where lf = likelihood globalEnv env thetas d branchMap

likelihood _ _ _ (ThetaI _ _) _ _ = error "typing error in probability - ThetaI"
likelihood _ _ _ (Cons _ _ _) _ _ = error "typing error in probability - Cons (maybe value is not list)"
likelihood _ _ _ (Normal _) _ _ = error "typing error in probability - Normal"
likelihood _ _ _ (Uniform _) _ _ = error "typing error in probability - Uniform"

-- let x = normal in let y = normal in if flip then (x, y) else (x-3, normal)
-- getinv x = branch val, val - 3 --> basedistV branchedprobability n1 n2
-- getinv y = branch val, vmarg --> basedistV branchedprobability n3 1
-- likelihood (x, y)
marginalizeBranches :: (Num a, Show a) => Probability a -> String -> Probability a
marginalizeBranches (BranchedProbability p1 p2 x) name
  | x == name = pOr p1 p2
  | otherwise = BranchedProbability (marginalizeBranches p1 name) (marginalizeBranches p2 name) x
likelihoodForValue :: (Num a) => (Value a -> Probability a) -> Value a -> String -> Probability a
likelihoodForValue ll (VBranch val1 val2 y) x
 | x == y = BranchedProbability (likelihoodForValue ll val1 x) (likelihoodForValue ll val2 x) x
 | otherwise = error "unfitting variables likelihood for value"
likelihoodForValue ll val _ = ll val

type BranchMap a = Map.Map (Expr TypeInfoWit a) [String]
getInvValue :: (Floating a, Num a, Fractional a, Ord a) => FEnv a -> Env TypeInfoWit a -> Env TypeInfoWit a -> Thetas a -> Expr TypeInfoWit a -> String -> Value a -> a -> (Value a, a, BranchMap a)
getInvValue _ _ _ _ expr v _ _
  | Set.notMember v (getWitsW expr) = error "witnessed var not in deducible"
getInvValue fenv globalEnv env thetas (Var _ name) var val cor_factor = if name == var
                                                                            then (val, abs cor_factor, Map.empty)
                                                                            else error "False variable in var encountered"
getInvValue fenv globalEnv env thetas (InjF _ name params f2) var val cor_factor =
  getInvValue fenv globalEnv env thetas f2 var (inverse params_val val) (cor_factor * inverse_grad params_val val)
  where (Just (FPair fPair)) = lookup name fenv
        (_, forward, inverse, inverse_grad) = fPair
        --grad_loss :: [(loss :: a, grad :: Thetas a)]
        --grad_loss thX = [grad' (\theta -> log $ unwrapP $ likelihood (autoEnv env) (autoEnv env) theta (autoExpr expr) (autoVal sample)) thX | sample <- samples]

        --inverse_grad_auto = head $ grad (\[inv_val] -> inverse_p inv_val) [val]
        --inverse_p = inverse params_val
        --auto_p = (map auto params_val)
        params_val = map (detGenerate env thetas) params

getInvValue fenv globalEnv env thetas (Plus ti expr1 expr2) var (VFloat val) cor_factor
  | var `elem` getWitsW expr1 = getInvValue fenv globalEnv env thetas expr1 var (VFloat $ val - val2) cor_factor
  | var `elem` getWitsW expr2 = getInvValue fenv globalEnv env thetas expr2 var (VFloat $ val - val1)  cor_factor
  where (VFloat val2) = detGenerate env thetas expr2
        (VFloat val1) = detGenerate env thetas expr1
getInvValue fenv globalEnv env thetas (Mult ti expr1 expr2) var (VFloat val) cor_factor
  | notElem var (getWits ti) || getPTypeW ti == Bottom = error "Cannot calculate inverse value in this mult expression"
  | var `elem` getWitsW  expr1 = getInvValue fenv globalEnv env thetas expr1 var (VFloat $ val/ val2) (cor_factor/val2)
  | var `elem` getWitsW  expr2 = getInvValue fenv globalEnv env thetas expr2 var (VFloat $ val/ val1)  (cor_factor/val1)
  where (VFloat val2) = detGenerate env thetas expr2
        (VFloat val1) = detGenerate env thetas expr1
getInvValue fenv globalEnv env thetas (Cons ti fst rst) var (VList (fst_v:rst_v)) cor_factor
  | notElem var (getWits ti) || getPTypeW ti == Bottom = error "Cannot calculate inverse value in this cons expression"
  | var `elem` getWitsW fst = getInvValue fenv globalEnv env thetas fst var fst_v cor_factor
  | var `elem` getWitsW rst = getInvValue fenv globalEnv env thetas rst var (VList rst_v) cor_factor
getInvValue fenv globalEnv env thetas (LetIn ti name decl expr) var val cor_factor = 
  getInvValue fenv globalEnv env thetas expr var val cor_factor
-- Correction factor not correctly calculated since its not used atm
getInvValue fenv globalEnv env thetas ee@(IfThenElse ti cond tr fl) var val cor_factor
  | var `elem` getWitsW tr && var `elem` getWitsW fl = (VBranch leftVal rightVal var, 1, Map.singleton ee [var])
  -- TODO make these two cases below useful
  | otherwise = error "non-witnessed if-then-else branches"
  -- TODO: What if subtrees have more branches
  where (leftVal, leftCor, _) = getInvValue fenv globalEnv env thetas tr var val cor_factor
        (rightVal, rightCor, _) = getInvValue fenv globalEnv env thetas fl var val cor_factor
getInvValue _ _ _ _ _ _ _ _ = error "bij inv not implemented for expr here"

integrate :: (Erf a, Num a, Ord a) => Expr TypeInfoWit a -> Thetas a -> Limits a -> a
integrate (Uniform t) thetas (Limits low high) 
 | checkLimits (Limits low high) = if l2 > 1 || h2 < 0 then 0 else h2 - l2
 | otherwise = error "Invalid value for limits"
  where
    h2 = min 1 $ maybe 1 unwrap high
    l2 = max 0 $ maybe 0 unwrap low
    unwrap vflt = case vflt of
      VFloat x -> x
      _ -> error "unexpected type-error in RT:Integrate"
integrate (Normal t) thetas (Limits low high)
 | checkLimits (Limits low high) =
   case high of
     Nothing -> 1 - unwrap_cdf low
     (Just sth) -> unwrap_cdf high - unwrap_cdf low
 | otherwise = error "Invalid value for limits"
  where
    unwrap_cdf vflt = case vflt of
      Nothing -> 0
      Just (VFloat x) -> cdf x
      _ -> error "unexpected type-error in RT:Integrate"
    cdf z = (1/2)*(1 + erf(z/sqrt(2)))
integrate _ _ _ = error "undefined integrate for expr"

data Probability a = PDF a
                 | DiscreteProbability a
                 | BranchedProbability (Probability a) (Probability a) String
                 deriving (Show)



pAnd :: (Num a, Show a)  => Probability a -> Probability a -> Probability a
pAnd (PDF a) (PDF b) = PDF (a*b)
pAnd (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a*b)
pAnd (PDF a) (DiscreteProbability b) = PDF (a*b)
pAnd (DiscreteProbability a) (PDF b) = PDF (a*b)
pAnd (BranchedProbability p1 p2 x) pp@(DiscreteProbability p)  = BranchedProbability (pAnd p1 pp) (pAnd p2 pp) x
pAnd pp@(DiscreteProbability p) (BranchedProbability p1 p2 x) = BranchedProbability (pAnd p1 pp) (pAnd p2 pp) x
pAnd pp@(PDF p) (BranchedProbability p1 p2 x) = BranchedProbability (pAnd p1 pp) (pAnd p2 pp) x
pAnd (BranchedProbability p1 p2 x)pp@(PDF p)  = BranchedProbability (pAnd p1 pp) (pAnd p2 pp) x

-- TODO Reordering branched probability trees
pAnd pp2@(BranchedProbability p1 p2 x) (BranchedProbability p3 p4 y) =
  if x == y
  then BranchedProbability (pAnd p1 p3) (pAnd p2 p4) y
  else BranchedProbability (pAnd pp2 p3) (pAnd pp2 p4) y
pAnd (BranchedProbability p1 p2 x) p3 = BranchedProbability (pAnd p1 p3) (pAnd p2 p3) x

pAnd p2 p4 = trace ("error p " ++ show p2 ++ show p4) ( p2)

pOr :: (Show a, Num a) => Probability a -> Probability a -> Probability a
pOr (PDF a) (PDF b) = PDF (a+b)
pOr (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a+b)
pOr (PDF a) (DiscreteProbability b) = PDF (a+b)
pOr (DiscreteProbability a) (PDF b) = PDF (a+b)
pOr (BranchedProbability p1 p2 x) (BranchedProbability p3 p4 y) 
  | x == y = BranchedProbability (pOr p1 p3) (pOr p2 p4) x
  | otherwise = error "pOr on different variable branches"

unwrapP :: Probability a -> a
unwrapP (PDF x) = x
unwrapP (DiscreteProbability x) = x

