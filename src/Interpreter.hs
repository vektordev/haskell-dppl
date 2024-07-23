{-# LANGUAGE FlexibleContexts #-}
module Interpreter where

import Control.Monad.Random
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity

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
import Numeric.AD.Internal.Reverse ( Reverse, Tape)
import qualified Data.Map as Map
import Data.Reflection (Reifies)
import Data.Number.Erf
import PredefinedFunctions

type Thetas a = [a]

data VEnv a
  = ValueEnv {values :: Map.Map String (Value a), branchMap :: BranchMap a}
  deriving (Eq, Show)


type BranchMap a = Map.Map (Expr (TypeInfo a) a) [String]
vempty :: VEnv a
vempty = ValueEnv {values = Map.empty, branchMap = Map.empty}

vextend :: VEnv a -> (String, Value a) -> VEnv a
vextend env (x, s) = env { values = Map.insert x s (values env) }

vremove :: VEnv a -> String -> VEnv a
vremove env var = env {values = Map.delete var (values env)}


findTheta :: Expr x a -> Thetas a -> a
findTheta (ThetaI _ a i) ts = if i >= length ts then error "out of bounds in Thetas" else ts !! i
findTheta _ _ = error "called FindTheta on non-theta expr."

-- | Inference state
data InferLState a = InferLState {global_funcs :: Env (TypeInfo a) a, thetas :: Thetas a}
-- | Initial inference state
initInferL :: Env (TypeInfo a) a -> Thetas a -> InferLState a
initInferL env t = InferLState { global_funcs = env, thetas = t }


data LikelihoodError a
  = BottomError (Expr (TypeInfo a) a)
  | MismatchedValue (Value a) (Expr (TypeInfo a) a)
  deriving (Show)


--TODO: Verify Env changes are done in a sane manner in interpreter
-- | Inference monad
type InferL a b = (ReaderT
                  (VEnv a)             -- Typing TEnvironment
                  (StateT         -- Inference state
                    (InferLState a)
                    (Except (LikelihoodError a)))
                  b)              -- Result

--note: We need detGenerate in order to be able to solve probability: Reverse s a does not have a Random instance,
-- so we have to make do without in probability. Hence if we need to generate, we need to generate deterministically.
detGenerateM :: (Floating a, Fractional a, Ord a) => Expr (TypeInfo a) a -> InferL a (Value a)
detGenerateM (IfThenElse _ cond left right) = do
  condVal <- detGenerateM cond
  case condVal of
    VBool True -> detGenerateM left
    VBool False -> detGenerateM right
    _ -> error "Type error"
detGenerateM (GreaterThan _ left right) = do
  a <- detGenerateM left
  b <- detGenerateM right
  case (a,b) of
    (VFloat af, VFloat bf) -> return $ VBool (af > bf)
    _ -> error "Type error"
detGenerateM (PlusF _ left right) = if pt1 == Deterministic && pt2 == Deterministic
  then (do
    val1 <- detGenerateM left
    val2 <- detGenerateM right
    return $ VFloat (getVFloat val1 + getVFloat val2)
  )
  else error "detGenerate non-deterministic plus"
  where
    rt1 = rType $ getTypeInfo left
    pt1 = pType $ getTypeInfo left
    rt2 = rType $ getTypeInfo right
    pt2 = pType $ getTypeInfo right
detGenerateM (MultF _ left right) = if pt1 == Deterministic && pt2 == Deterministic
  then (do
     val1 <- detGenerateM left
     val2 <- detGenerateM right
     return $ VFloat (getVFloat val1 * getVFloat val2)
   )
  else error "detGenerate non-deterministic mult"
  where
    rt1 = rType $ getTypeInfo left
    pt1 = pType $ getTypeInfo left
    rt2 = rType $ getTypeInfo right
    pt2 = pType $ getTypeInfo right
detGenerateM expr@(ThetaI _ a i) = do
   inf_ste <- get
   return $ VFloat (findTheta expr (thetas inf_ste))
detGenerateM (Uniform _) = error "tried to detGenerate from random atom"
detGenerateM (Normal _) = error "tried to detGenerate from random atom"
detGenerateM (Constant _ x) = return $ x
detGenerateM (Null _) = return $ VList []
detGenerateM (Cons _ hd tl) = do
  vs <- detGenerateM tl
  let (VList xs) = vs
  hs <- detGenerateM hd
  return $ VList (hs: xs)
detGenerateM (TCons _ t1 t2) = do
  v1 <- detGenerateM t1
  v2 <- detGenerateM t2
  return $ VTuple v1 v2
detGenerateM (Call t name) = do
  env <- get
  let Just expr = lookup name (global_funcs env)
  -- Reset value env on call
  local (const vempty) (detGenerateM expr)
detGenerateM (Var t name) = do
  env <- ask
  let Just val = Map.lookup name (values env)
  return val
detGenerateM (InjF t name params) = error "Not yet implemented"
detGenerateM expr =
  if pt /= Deterministic
  then error "tried detGenerate on non-deterministic expr"
  else error "detGenerate not defined for expr"
    where rt = rType $ getTypeInfo expr
          pt = pType $ getTypeInfo expr

generate :: (Fractional a, RandomGen g, Ord a, Random a, Floating a) => Env (TypeInfo a) a -> Env (TypeInfo a) a -> Thetas a -> [Expr (TypeInfo a) a] -> Expr (TypeInfo a) a -> Rand g (Value a)
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
generate _ _ thetas args expr@(ThetaI _ a i) = return $ VFloat (findTheta expr thetas)
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


generate a b c args (PlusF _ left right) = do
  leftSample <- generate a b c args left
  rightSample <- generate a b c args right
  case (leftSample, rightSample) of
    (VFloat l, VFloat r) -> return $ VFloat (l + r)
    _ -> error "Type error"
generate a b c args (MultF _ left right) = do
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
generate globalEnv env thetas args (TCons _ t1 t2) = do
  v1 <- generate globalEnv env thetas args t1
  v2 <- generate globalEnv env thetas args t2
  return $ VTuple v1 v2
--Call leaves function context, pass GlobalEnv to ensure env is cleaned up.
generate globalEnv env thetas args (Call t name) = generate globalEnv globalEnv thetas args expr
  where Just expr = lookup name globalEnv
generate globalEnv env thetas args (Var t name) = generate globalEnv globalEnv thetas args expr
  where Just expr = lookup name env
generate globalEnv env thetas args (ReadNN _ _ expr) = error "NN not implemented"
generate globalEnv env thetas args (LetIn _ name decl bij) =
  do
    declValue <- generate globalEnv env thetas args decl
    let extendedEnv = (name, Constant (makeTypeInfo { rType = (getRType declValue), pType = Deterministic}) declValue):env
    generate globalEnv extendedEnv thetas args bij
generate globalEnv env thetas args (InjF _ name params) = error "Not yet implemented" --TODO

callInv :: (Floating a) => FEnv a -> String -> a -> a
callInv fenv name pa = error "Not yet implemented" --TODO


sigmoid :: Floating a => a -> a
sigmoid x = 1 / (1 + exp (-x))

replaceVEnvBranch :: (Show a) => (Map.Map String (Value a), Map.Map String (Value a)) -> String -> (Map.Map String (Value a), Map.Map String (Value a))
replaceVEnvBranch (envS1, envS2) var = (env1, env2)
  where Just (VBranch val1 val2 bName) =  Map.lookup var envS1
        env1 = Map.insert var val1 envS1
        env2 = Map.insert var val2 envS2
--TODO expand to more vars
replaceEnvBranch :: (Show a) => (Env (TypeInfo a) a, Env (TypeInfo a) a)  -> String -> (Env (TypeInfo a) a, Env (TypeInfo a) a)
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

-- -- | Run the inference monad
runInferL ::(Erf a, Show a, Fractional a, Ord a, Real a, Floating a) =>  Env (TypeInfo a) a -> Expr (TypeInfo a) a -> Thetas a -> Value a -> Probability a
runInferL env expr thetas val = case runExcept $ evalStateT (runReaderT (likelihoodM expr val) vempty) (initInferL env thetas) of
  Left err -> error "error in likelihoodM"
  Right p -> p

runInferIO ::(Erf a, Show a, Fractional a, Ord a, Real a, Floating a) =>  Env (TypeInfo a) a -> Expr (TypeInfo a) a -> Thetas a -> Value a -> IO ()
runInferIO env expr thetas val = case runExcept $ evalStateT (runReaderT (likelihoodM expr val) vempty) (initInferL env thetas) of
  Left err -> print err
  Right p -> print p

likelihoodM :: (Erf a, Show a, Ord a, Real a) => Expr (TypeInfo a) a -> Value a -> InferL a (Probability a)

-- error cases
likelihoodM expr _
  | pType (getTypeInfo expr) == Bottom = throwError $ BottomError expr
likelihoodM expr VAnyList = throwError $ MismatchedValue VAnyList expr

likelihoodM (Call _ name) val = do
  env <- get
  let Just expr = lookup name (global_funcs env)
  -- Reset value env on call
  local (const vempty) (likelihoodM expr val)

likelihoodM (LetIn ti name decl bij) val
  | pType (getTypeInfo decl) == Integrate = do
      (baseDistV, bMap) <- getInvValueM globalFenv bij name val
      baseDistProb <- likelihoodM decl baseDistV
      e2Dist <- local (\venv -> venv{values = Map.insert name baseDistV (values venv),
                                     branchMap = Map.union bMap (branchMap venv)}) (likelihoodM bij val)
      let pBr = baseDistProb `pAnd` e2Dist
      return $ marginalizeBranches pBr name
  | pType (getTypeInfo decl) == Deterministic = do
      declVal <- detGenerateM decl
      let scope e = vremove e name `vextend` (name, declVal)
      local scope (likelihoodM bij val)
  | otherwise = throwError $ BottomError (LetIn ti name decl bij)
  --where -- Integrate case
        --extendedEnvI = (name, Constant (TypeInfoWit TFloat Deterministic Set.empty) baseDistV):env
        --e2Dist = likelihood globalEnv extendedEnvI thetas bij (Map.unionWith (++) branchMap branchMapE) val
        -- Deterministic case
        -- Could replace this with value env
        --extendedEnvD = (name, Constant (TypeInfoWit TFloat Deterministic Set.empty) (detGenerate env thetas decl)):env

likelihoodM ee@(IfThenElse t cond left right) val =
  do
    venv <- ask
    pCond <- likelihoodM cond (VBool True)
    let pCondInv = DiscreteProbability (1 - unwrapP pCond)
    case Map.lookup ee (branchMap venv) of
      Nothing -> do
        pLeft <- likelihoodM left val
        pRight <- likelihoodM right val
        return (pOr (pAnd pCond pLeft) (pAnd pCondInv pRight))
      (Just [branchName]) -> do
        let (env1, env2) = foldl replaceVEnvBranch (values venv, values venv) [branchName]
        pLeft <- local (\venv -> venv{values = env1}) (likelihoodM left val)
        pRight <- local (\venv -> venv{values = env2}) (likelihoodM right val)
        return $ BranchedProbability (pAnd pCond pLeft) (pAnd pCondInv pRight) branchName

likelihoodM (Null _) (VList []) = return $ DiscreteProbability 1
likelihoodM (Null _) (VList [VAnyList])  = return $ DiscreteProbability 1
likelihoodM (Null _) _ = return $ DiscreteProbability 0
likelihoodM (Cons _ _ _) (VList [VAnyList])  = return $  DiscreteProbability 1
likelihoodM (Cons _ _ _) (VList []) = return $ DiscreteProbability 0
likelihoodM e@(Cons _ _ _) v = throwError $ MismatchedValue v e
likelihoodM (Cons _ hd tl) (VList (x:xs)) = do
    fstP <- likelihoodM hd x
    sndP <- likelihoodM tl $ VList xs
    return (pAnd fstP sndP)
likelihoodM (TCons _ t1 t2) (VTuple x1 x2) = do
   fstP <- likelihoodM t1 x1
   sndP <- likelihoodM t2 x2
   return $ pAnd fstP sndP
likelihoodM inj@(InjF ti name params) val = error "Not yet implemented"  --TODO
        --inverse_grad_auto = grad' (\[val] -> callInv globalFenv2 name (map autoVal params_val) val) [vfloat_val]
        --(VFloat vfloat_val) = val
        
likelihoodM expr (VRange (Limits Nothing Nothing)) = return $ DiscreteProbability 1.0

likelihoodM (GreaterThan t left right) (VBool x)
  --consider GreaterThan () (Uniform ()) (ThetaI () 0)
  -- the right side is deterministic. the probability of getting true out of the expr is 1 - theta
  -- rightGen will return theta. Therefore, integrating Uniform from -inf to theta will result in theta.
  | rightP == Deterministic && leftP  == Integrate && x = do
    rightGen <- detGenerateM right
    return $ DiscreteProbability $ 1 - integrate left (Limits Nothing (Just rightGen))
  | rightP == Deterministic && leftP  == Integrate && not x = do
    rightGen <- detGenerateM right
    return $ DiscreteProbability $ integrate left (Limits Nothing (Just rightGen))
  | rightP == Integrate && leftP  == Deterministic && x = do
    leftGen <- detGenerateM left
    return $ DiscreteProbability $ 1 - integrate left (Limits Nothing (Just leftGen))
  | rightP == Integrate && leftP  == Deterministic && not x = do
    leftGen <- detGenerateM left
    return $ DiscreteProbability $ integrate left (Limits Nothing (Just leftGen))
  | leftP  == Deterministic && rightP == Deterministic= do
    rightGen <- detGenerateM right
    leftGen <- detGenerateM left
    let VFloat leftFloat = leftGen
    let VFloat rightFloat = rightGen
    return $ DiscreteProbability $ if x then sigmoid (leftFloat - rightFloat) else sigmoid(rightFloat - leftFloat)
  where
    leftP = pType $ getTypeInfo left
    rightP = pType $ getTypeInfo right
likelihoodM expr@(ThetaI _ a x) val2 = do
   inf_ste <- get
   return $ branchedCompare (VFloat (findTheta expr (thetas inf_ste))) val2
likelihoodM (Uniform _) (VFloat x) = return $ if 0 <= x && x <= 1 then PDF 1 else PDF 0
likelihoodM (Uniform t) (VRange limits) = return $ DiscreteProbability $ integrate (Uniform t) limits
likelihoodM e@(Uniform _) v = throwError $ MismatchedValue v e

likelihoodM (Normal _) (VFloat x) = return $ PDF myDensity
  where myDensity = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)
likelihoodM (Normal t) (VRange limits) = return $ DiscreteProbability $ integrate (Normal t) limits
likelihoodM e@(Normal _) v = throwError $ MismatchedValue v e

likelihoodM (Constant _ val) val2 = return $ branchedCompare val val2
likelihoodM (MultF _ left right) (VRange limits)
  -- need to divide by the deterministic sample
  | leftP == Deterministic =
    do
      leftGen <- detGenerateM left
      let VFloat leftFloat = leftGen
      let inverse = fmap (flip(/) leftFloat) (VRange limits)
      let inverse_flip = if leftFloat < 0 then swapLimits inverse else inverse
      likelihoodM right inverse_flip
  | rightP == Deterministic =
      do
        rightGen <- detGenerateM right
        let VFloat rightFloat = rightGen
        let inverse = fmap (flip(/) rightFloat) (VRange limits)
        let inverse_flip = if rightFloat < 0 then swapLimits inverse else inverse
        likelihoodM left inverse_flip
  | otherwise = error "can't solve Mult; unexpected type error"
  where
    leftP = pType $ getTypeInfo left
    rightP = pType $ getTypeInfo right

likelihoodM (MultF ti left right) (VFloat x)
  -- need to divide by the deterministic sample
  | leftP == Deterministic =
      do
        leftGen <- detGenerateM left
        let inverse = fmap ((*x) . ((/)1)) leftGen
        inverseProbability <- likelihoodM right inverse
        return $ (applyCorBranch inverseProbability (fmap (abs . ((/)1)) leftGen))
  | rightP == Deterministic =
      do
        rightGen <- detGenerateM right
        let inverse = fmap ((*x) . ((/)1)) rightGen
        inverseProbability <- likelihoodM left inverse
        return $ (applyCorBranch inverseProbability (fmap (abs . ((/)1)) rightGen))
  | otherwise = throwError $ BottomError (MultF ti left right)
  where
    leftP = pType $ getTypeInfo left
    rightP = pType $ getTypeInfo right

likelihoodM (PlusF ti left right) (VFloat x)
  | leftP == Deterministic =
    do
      leftGen <- detGenerateM left
      likelihoodM right (inverse x leftGen)
  | rightP == Deterministic =
    do
      rightGen <- detGenerateM right
      likelihoodM left (inverse x rightGen)
  | otherwise = throwError $ BottomError (PlusF ti left right)
  where
  -- TODO: Branching for range queries
    leftP = pType $ getTypeInfo left
    rightP = pType $ getTypeInfo right
    inverse x d = fmap ((+x) . (*(-1))) d
    inverse_nob x dtl = fmap (flip(-) dtl) x

likelihoodM (PlusF ti left right) (VRange limits)
  | leftP == Deterministic =
    do
     leftGen <- detGenerateM left
     let VFloat leftFloat = leftGen
     likelihoodM right (inverse_nob (VRange limits) leftFloat)
  | rightP == Deterministic =
    do
      rightGen <- detGenerateM right
      let VFloat rightFloat = rightGen
      likelihoodM left (inverse_nob (VRange limits) rightFloat)
  | otherwise = throwError $ BottomError (PlusF ti left right)
  where
  -- TODO: Branching for range queries
    leftP = pType $ getTypeInfo left
    rightP = pType $ getTypeInfo right
    inverse x d = fmap ((+x) . (*(-1))) d
    inverse_nob x dtl = fmap (flip(-) dtl) x
-- TODO lists as variables with branching

likelihoodM (Var t name) val = do
  env <- ask
  let Just val2 = Map.lookup name (values env)
  return $ branchedCompare val val2

likelihoodM d (VBranch v1 v2 x) = do
   p1 <- lf v1
   p2 <- lf v2
   return $ BranchedProbability p1 p2 x
  where lf = likelihoodM d




-- let x = normal in let y = normal in if flip then (x, y) else (x-3, normal)
-- getinv x = branch val, val - 3 --> basedistV branchedprobability n1 n2
-- getinv y = branch val, vmarg --> basedistV branchedprobability n3 1
-- likelihood (x, y)
marginalizeBranches :: (Num a, Show a) => Probability a -> String -> Probability a
marginalizeBranches (BranchedProbability p1 p2 x) name
  | x == name = pOr p1 p2
  | otherwise = BranchedProbability (marginalizeBranches p1 name) (marginalizeBranches p2 name) x
marginalizeBranches p _ = p
likelihoodForValue :: (Num a) => (Value a -> Probability a) -> Value a -> String -> Probability a
likelihoodForValue ll (VBranch val1 val2 y) x
 | x == y = BranchedProbability (likelihoodForValue ll val1 x) (likelihoodForValue ll val2 x) x
 | otherwise = error "unfitting variables likelihood for value"
likelihoodForValue ll val _ = ll val

getInvValueM :: (Floating a, Num a, Fractional a, Ord a) => FEnv a -> Expr (TypeInfo a) a -> String -> Value a -> InferL a (Value a, BranchMap a)
getInvValueM _ expr v _
  | Set.notMember v (witnessedVars (getTypeInfo expr)) = error "witnessed var not in deducible"
getInvValueM fenv  (Var _ name) var val = if name == var
                                              then return $ (val, Map.empty)
                                              else error "False variable in var encountered"
getInvValueM fenv (InjF _ name params) var val = error "Not yet implemented" --TODO
        --grad_loss :: [(loss :: a, grad :: Thetas a)]
        --grad_loss thX = [grad' (\theta -> log $ unwrapP $ likelihood (autoEnv env) (autoEnv env) theta (autoExpr expr) (autoVal sample)) thX | sample <- samples]

        --inverse_grad_auto = head $ grad (\[inv_val] -> inverse_p inv_val) [val]
        --inverse_p = inverse params_val
        --auto_p = (map auto params_val)

getInvValueM fenv (PlusF ti expr1 expr2) var (VFloat val)
  | var `elem` witnessedVars (getTypeInfo expr1) = do
    val2 <- detGenerateM expr2
    getInvValueM fenv expr1 var (VFloat $ val - (getVFloat val2))
  | var `elem` witnessedVars (getTypeInfo expr2) =  do
    val1 <- detGenerateM expr1
    getInvValueM fenv expr2 var (VFloat $ val - (getVFloat val1))
getInvValueM fenv  (MultF ti expr1 expr2) var (VFloat val)
  | notElem var (witnessedVars ti) || pType ti == Bottom = error "Cannot calculate inverse value in this mult expression"
  | var `elem` witnessedVars (getTypeInfo expr1) = do
    val2 <- detGenerateM expr2
    getInvValueM fenv expr1 var (VFloat $ val / (getVFloat val2))
  | var `elem` witnessedVars (getTypeInfo expr2) =  do
    val1 <- detGenerateM expr1
    getInvValueM fenv expr2 var (VFloat $ val / (getVFloat val1))
getInvValueM fenv (Cons ti fst rst) var (VList (fst_v:rst_v))
  | notElem var (witnessedVars ti) || pType ti == Bottom = error "Cannot calculate inverse value in this cons expression"
  | var `elem` witnessedVars (getTypeInfo fst) = getInvValueM fenv fst var fst_v
  | var `elem` witnessedVars (getTypeInfo rst) = getInvValueM fenv rst var (VList rst_v)
getInvValueM fenv (LetIn ti name decl expr) var val =
  getInvValueM fenv expr var val
-- Correction factor not correctly calculated since its not used atm
getInvValueM fenv ee@(IfThenElse ti cond tr fl) var val
  | var `elem` witnessedVars (getTypeInfo tr) && var `elem` witnessedVars (getTypeInfo fl) = do
    (leftVal, bMap1) <- getInvValueM fenv tr var val
    (rightVal, bMap2) <- getInvValueM fenv fl var val
    return (VBranch leftVal rightVal var, Map.union (Map.union (Map.singleton ee [var]) bMap1) bMap2)
  | otherwise = error "non-witnessed if-then-else branches"
  -- TODO: What if subtrees have more branches
getInvValueM _ _ _ _ = error "bij inv not implemented for expr here"


integrate :: (Show a, Erf a, Num a, Ord a) => Expr (TypeInfo a) a -> Limits a -> a
integrate (Uniform t) (Limits low high)
 | checkLimits (Limits low high) = if l2 > 1 || h2 < 0 then 0 else h2 - l2
 | otherwise = error "Invalid value for limits"
  where
    h2 = min 1 $ maybe 1 unwrap high
    l2 = max 0 $ maybe 0 unwrap low
    unwrap vflt = case vflt of
      VFloat x -> x
      _ -> error "unexpected type-error in RT:Integrate"
integrate (Normal t) (Limits low high)
 | (checkLimits (Limits low high)) =
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
integrate _ _ = error "undefined integrate for expr"

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

