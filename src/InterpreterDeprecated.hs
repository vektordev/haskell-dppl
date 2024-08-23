module InterpreterDeprecated where
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import Interpreter
import System.Random
import Numeric.AD
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Number.Erf
import Control.Monad.Random (evalRandIO, getRandomR, replicateM, forM_)
import Lib
import Data.Reflection (Reifies)
import Numeric.AD.Internal.Reverse ( Reverse, Tape)
import PredefinedFunctions (FPair, FEnv, globalFenv)
--myGradientAscent :: (Num a, Num b, Num c, Num d) => Int -> Env a -> [b] -> Expr a -> [Value a] -> [([c], d)]
--myGradientAscent 0 _ _ _ _ = []
--myGradientAscent env thetas expr vals = (thetas, loss) : myGradientAscent env newHypothesis expr vals
--  where
    --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
--    loss = sum $ [unwrapP (log $ probability env thetas expr val) | val <- vals]
---    gradient = [sum (grad (\ th -> log $ unwrapP $ _ env th expr datum) thetas) | datum <- vals]
--    newHypothesis = zipWith (+) thetas $ map (\el -> 0.0001 * el) gradient
--pr_ :: (Num a, Num b) => a -> Env b -> [a]

probabilityDiag :: (Erf a, Floating a, Ord a, Real a, Show a) => [(String, Expr a)] -> [Thetas a] -> Expr a -> Value a -> IO ()
probabilityDiag env thetaScan expr sample = mapM_ (\theta -> probabilityDiagAt env theta expr sample) thetaScan

probabilityDiagAt :: (Erf a, Floating a, Ord a, Real a, Show a) => [(String, Expr a)] -> Thetas a -> Expr a -> Value a -> IO ()
probabilityDiagAt env theta expr sample = do
  print theta
  print (likelihood env env theta expr Map.empty sample)

gradientDiag :: (Erf a, RealFloat a, Floating a, Ord a, Real a, Show a) => [(String, Expr a)] -> [Thetas a] -> Expr a -> [Value a] -> IO ()
gradientDiag env thetaScan expr samples = mapM_ (\theta -> gradientDiagAt env theta expr samples) thetaScan

gradientDiagAt :: (Erf a, RealFloat a, Floating a, Ord a, Real a, Show a) => [(String, Expr a)] -> Thetas a -> Expr a -> [Value a] -> IO ()
gradientDiagAt env tht expr samples = do
  let grad_lossPre = [grad' (\theta -> log $ unwrapP $ likelihood (autoEnv env) (autoEnv env) theta (autoExpr expr) Map.empty (autoVal sample)) tht | sample <- samples]
  print ("gradient debug info for theta: " ++ (show tht))
  --let grad_loss = filter (not . isNaN . fst) grad_lossPre
  let grad_loss =  grad_lossPre
  print (show $ zip samples grad_loss)
  putStrLn ("gradients: " ++ show (foldl1 addThetas $ map snd grad_loss))
  putStrLn ("LL: " ++ show (sum $ map fst grad_loss))
  --print "LL: "
  --print $ sum $ map fst grad_loss

exprDebugMetrics :: (Erf a, Floating a, Real a, Show a, Enum a) => Env a -> Expr a -> [Value a] -> Thetas a -> IO ()
exprDebugMetrics env expr samples thetas = do
  mapM_ (\thX -> printInfo thX) [[x] | x <- [0.0, 0.1 .. 1.0]]
    where
      ll thX = sum [log $ unwrapP $ likelihood env env thX expr Map.empty sample | sample <- samples]
      grad_loss thX = [grad' (\theta -> log $ unwrapP $ likelihood (autoEnv env) (autoEnv env) theta (autoExpr expr) Map.empty (autoVal sample)) thX | sample <- samples]
      grad_thetas thX = map snd (grad_loss thX)
      gradient thX = foldl1 addThetas $ grad_thetas thX
      printInfo thX = do
        print (ll thX)
        print (gradient thX)

reconstructThetas :: (Erf a, RealFloat a, Floating a, Ord a, Random a, Show a, Real a) => Env a -> Int -> Thetas a -> IO [(Thetas a, a)]
reconstructThetas cEnv nSamples thetas = do
  let Just main = lookup "main" cEnv
  samples <- mkSamples nSamples cEnv thetas [] main
  --let initialGuess = replicate (length thetas) 0.5
  initialGuess <- replicateM (length thetas) (getRandomR (-1.0, 0.0))
  let reconstructedThetas = myGradientAscent 500 0.02 cEnv initialGuess main samples
  return reconstructedThetas

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


--instance Traversable Thetas where
--  traverse (Thetas a) = Thetas $ traverse a
detGenerate :: (Floating a, Fractional a, Ord a) => Env a -> Thetas a -> Expr a -> Value a
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
detGenerate env thetas (PlusF _ left right) = if pt1 == Deterministic && pt2 == Deterministic
  then VFloat (val1 + val2)
  else error "detGenerate non-deterministic plus"
  where
    (TypeInfo {rType = rt1, pType = pt1}) = getTypeInfo left
    (TypeInfo {rType = rt2, pType = pt2}) = getTypeInfo right
    (VFloat val1) = detGenerate env thetas left
    (VFloat val2) = detGenerate env thetas right
detGenerate env thetas (MultF _ left right) = if pt1 == Deterministic && pt2 == Deterministic
  then VFloat (val1 * val2)
  else error "detGenerate non-deterministic mult"
  where
    (TypeInfo {rType = rt1, pType = pt1}) = getTypeInfo left
    (TypeInfo {rType = rt2, pType = pt2}) = getTypeInfo right
    (VFloat val1) = detGenerate env thetas left
    (VFloat val2) = detGenerate env thetas right
detGenerate _ thetas expr@(ThetaI _ a i) = VFloat (findTheta expr thetas)
detGenerate _ _ (Uniform _) = error "tried to detGenerate from random atom"
detGenerate _ _ (Normal _) = error "tried to detGenerate from random atom"
detGenerate _ _ (Constant _ x) = x
detGenerate _ _ (Null _) = VList []
detGenerate env thetas (Cons _ hd tl) = VList (detGenerate env thetas hd : xs)
  where VList xs = detGenerate env thetas tl
-- Deleted Tuple logic, does not work, will not fix
detGenerate env thetas (Call t name) = detGenerate env thetas expr
  where Just expr = lookup name env
detGenerate env thetas (Var t name) = detGenerate env thetas expr
  where Just expr = lookup name env
detGenerate env thetas (InjF t name params) = error "Not yet implemented"
detGenerate _ _ expr =
  if pt /= Deterministic
  then error "tried detGenerate on non-deterministic expr"
  else error "detGenerate not defined for expr"
    where TypeInfo {rType = rt, pType = pt} = getTypeInfo expr


likelihood :: (Erf a, Show a, Fractional a, Ord a, Real a, Floating a) => Env a -> Env a -> Thetas a -> Expr a -> BranchMap a -> Value a -> Probability a
-- possible problems in the probability math in there:
likelihood _ _ _ expr _ _
  | pType (getTypeInfo expr) == Bottom = error "cannot calculate likelihood for bottom type"
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
  | rightP == Deterministic && leftP  == Integrate && x     = DiscreteProbability $ 1 - integrate left (Limits Nothing (Just rightGen))
  | rightP == Deterministic && leftP  == Integrate && not x = DiscreteProbability $ integrate left (Limits Nothing (Just rightGen))
  | leftP  == Deterministic && rightP == Integrate && x     = DiscreteProbability $ 1 - integrate right (Limits (Just leftGen) Nothing)
  | leftP  == Deterministic && rightP == Integrate && not x = DiscreteProbability $ integrate right (Limits (Just leftGen) Nothing)
  | leftP  == Deterministic && rightP == Deterministic && x = DiscreteProbability $ sigmoid (leftFloat - rightFloat)
  | leftP  == Deterministic && rightP == Deterministic && not x = DiscreteProbability $ sigmoid (rightFloat - leftFloat)
  | otherwise = error "undefined probability for greaterThan"
  where
    leftP = pType (getTypeInfo left)
    rightP = pType (getTypeInfo right)
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
    VFloat leftFloat = leftGen
    VFloat rightFloat = rightGen
likelihood _ _ thetas expr@(ThetaI _ a x) _ val2 = branchedCompare (VFloat (findTheta expr thetas)) val2
likelihood _ _ _ (Uniform _) _ (VFloat x) = if 0 <= x && x <= 1 then PDF 1 else PDF 0
likelihood _ _ thetas (Uniform t) _ (VRange limits) = DiscreteProbability $ integrate (Uniform t) limits
--likelihood _ _ _ (Uniform _) _ (VRange OpenInterval (VFloat x)) = DiscreteProbability
--likelihood _ _ _ (Uniform _) _ (VRange OpenInterval OpenInterval) = DiscreteProbability

likelihood globalEnv env thetas d@(Uniform _) branchMap (VBranch v1 v2 x)  = BranchedProbability (lf v1) (lf v2) x
  where lf = likelihood globalEnv env thetas d branchMap
--probability _ _ _ (Normal _) (VFloat x) = PDF $ realToFrac $ density (normalDistr 0 1) $ realToFrac x
likelihood _ _ _ (Normal _) _ (VFloat x) = PDF myDensity
  where myDensity = (1 / sqrt (2 * pi)) * exp (-0.5 * x * x)
likelihood _ _ thetas (Normal t) _ (VRange limits) = DiscreteProbability $ integrate (Normal t) limits

likelihood _ _ _ (Constant _ val) _ val2 = branchedCompare val val2
likelihood globalEnv env thetas (MultF _ left right) branchMap (VRange limits)
  -- need to divide by the deterministic sample
  | leftP == Deterministic || rightP == Deterministic = inverseProbability
  | otherwise = error "can't solve Mult; unexpected type error"
  where
    leftP = pType (getTypeInfo left)
    rightP = pType (getTypeInfo right)
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
    VFloat detSample = if leftP == Deterministic then leftGen else rightGen
    inverse = fmap (flip(/) detSample) (VRange limits)
    inverse_flip = if detSample < 0 then swapLimits inverse else inverse
    inverseProbability = if leftP == Deterministic
      then likelihood globalEnv env thetas right branchMap inverse_flip
      else likelihood globalEnv env thetas left branchMap inverse_flip
likelihood globalEnv env thetas (MultF _ left right) branchMap (VFloat x)
  -- need to divide by the deterministic sample
  | leftP == Deterministic || rightP == Deterministic = correctedProbability
  | otherwise = error "can't solve Mult; unexpected type error"
  where
    leftP = pType (getTypeInfo left)
    rightP = pType (getTypeInfo right)
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
    detSample = if leftP == Deterministic then leftGen else rightGen
    inverse = fmap ((*x) . ((/)1)) detSample
    inverseProbability = if leftP == Deterministic
      then likelihood globalEnv env thetas right branchMap inverse
      else likelihood globalEnv env thetas left branchMap inverse
    correctedProbability = (applyCorBranch inverseProbability (fmap (abs . ((/)1)) detSample))
likelihood globalEnv env thetas (PlusF _ left right) branchMap val
  | leftP == Deterministic = case val of
    (VFloat x) -> likelihood globalEnv env thetas right branchMap (inverse x)
    (VRange limits) -> likelihood globalEnv env thetas right branchMap (inverse_nob (VRange limits))
  | rightP == Deterministic = case val of
    (VFloat x) -> likelihood globalEnv env thetas left branchMap (inverse x)
    (VRange limits) -> likelihood globalEnv env thetas left branchMap (inverse_nob (VRange limits))
  | otherwise = error "can't solve Plus; unexpected type error"
  where
  -- TODO: Branching for range queries
    leftP = pType (getTypeInfo left)
    rightP = pType (getTypeInfo right)
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
    detSample = if leftP == Deterministic then leftGen else rightGen
    VFloat vflDet = detSample
    inverse x = fmap ((+x) . (*(-1))) detSample
    inverse_nob x = fmap (flip(-) vflDet) x
-- TODO lists as variables with branching

likelihood _ _ _ (Null _) _ (VList []) = DiscreteProbability 1
likelihood _ _ _ (Null _) _ _ = DiscreteProbability 0
likelihood _ _ _ (Cons _ _ _) _ (VList []) = DiscreteProbability 0
likelihood globalEnv env thetas (Cons _ hd tl) branchMap (VList (x:xs)) =
        (pAnd (likelihood globalEnv env thetas hd branchMap x) (likelihood globalEnv env thetas tl branchMap $ VList xs) )


--Deleted Tuple logic from here, does not work, will not fix
likelihood globalEnv env thetas (Call _ name) branchMap val = likelihood globalEnv globalEnv thetas expr branchMap val
  where Just expr = lookup name env
likelihood globalEnv env thetas (Var _ name) branchMap val = likelihood globalEnv globalEnv thetas expr branchMap val
  where Just expr = lookup name env
-- Cons a [b,c,d] = [a,b,c,d]

--likelihood([a, b, ... l], Cons subExprA subExprB)
-- = (likelihood(a, subExprA) * (likelihood([b, ..., l], subExprB)
likelihood globalEnv env thetas inj@(InjF ti name params) branchMap val = error "Not yet implemented"
-- expr -> let x = normal in sig(x)
-- likelihood(0.2|expr) = (x = inverse_sig(0.2)) -->
likelihood globalEnv env thetas (LetIn _ name decl bij) branchMap val
-- pAnd p_cor
  | pType (getTypeInfo decl) == Integrate =
    case likelihoodForValue (likelihood globalEnv env thetas decl branchMap) baseDistV name `pAnd` e2Dist of
      (BranchedProbability p1 p2 branch) -> marginalizeBranches (BranchedProbability p1 p2 branch) name
      p -> p
  | pType (getTypeInfo decl) == Deterministic = likelihood globalEnv extendedEnvD thetas bij branchMap val
  | otherwise = error "non exhaustive letin (bottom type perhaps)"
  where -- Integrate case
        (baseDistV, cor_factor, branchMapE) = getInvValue globalFenv globalEnv env thetas bij name val 1.0
        extendedEnvI = (name, Constant (makeTypeInfo{rType = TFloat, pType = Deterministic}) baseDistV):env
        e2Dist = likelihood globalEnv extendedEnvI thetas bij (Map.unionWith (++) branchMap branchMapE) val
        -- Deterministic case
        -- Could replace this with value env
        extendedEnvD = (name, Constant (makeTypeInfo{rType = TFloat, pType = Deterministic}) (detGenerate env thetas decl)):env

likelihood globalEnv env thetas d branchMap (VBranch v1 v2 x) = BranchedProbability (lf v1) (lf v2) x
  where lf = likelihood globalEnv env thetas d branchMap

likelihood _ _ _ (ThetaI _ _ _) _ _ = error "typing error in probability - ThetaI"
likelihood _ _ _ (Cons _ _ _) _ _ = error "typing error in probability - Cons (maybe value is not list)"
likelihood _ _ _ (Normal _) _ _ = error "typing error in probability - Normal"
likelihood _ _ _ (Uniform _) _ _ = error "typing error in probability - Uniform"


-- TODO change to venv lookup
getInvValue :: (Floating a, Num a, Fractional a, Ord a) => FEnv a -> Env a -> Env a -> Thetas a -> Expr a -> String -> Value a -> a -> (Value a, a, BranchMap a)
getInvValue _ _ _ _ expr v _ _
  | Set.notMember v (witnessedVars (getTypeInfo expr)) = error "witnessed var not in deducible"
getInvValue fenv globalEnv env thetas (Var _ name) var val cor_factor = if name == var
                                                                            then (val, abs cor_factor, Map.empty)
                                                                            else error "False variable in var encountered"
getInvValue fenv globalEnv env thetas (InjF _ name params) var val cor_factor = error "Not yet implemented"

getInvValue fenv globalEnv env thetas (PlusF ti expr1 expr2) var (VFloat val) cor_factor
  | var `elem` witnessedVars (getTypeInfo expr1) = getInvValue fenv globalEnv env thetas expr1 var (VFloat $ val - val2) cor_factor
  | var `elem` witnessedVars (getTypeInfo expr2) = getInvValue fenv globalEnv env thetas expr2 var (VFloat $ val - val1)  cor_factor
  where (VFloat val2) = detGenerate env thetas expr2
        (VFloat val1) = detGenerate env thetas expr1
getInvValue fenv globalEnv env thetas (MultF ti expr1 expr2) var (VFloat val) cor_factor
  | notElem var (witnessedVars ti) || pType ti == Bottom = error "Cannot calculate inverse value in this mult expression"
  | var `elem` witnessedVars (getTypeInfo expr1) = getInvValue fenv globalEnv env thetas expr1 var (VFloat $ val/ val2) (cor_factor/val2)
  | var `elem` witnessedVars (getTypeInfo expr2) = getInvValue fenv globalEnv env thetas expr2 var (VFloat $ val/ val1)  (cor_factor/val1)
  where (VFloat val2) = detGenerate env thetas expr2
        (VFloat val1) = detGenerate env thetas expr1
getInvValue fenv globalEnv env thetas (Cons ti fst rst) var (VList (fst_v:rst_v)) cor_factor
  | notElem var (witnessedVars ti) || pType ti == Bottom = error "Cannot calculate inverse value in this cons expression"
  | var `elem` witnessedVars (getTypeInfo fst) = getInvValue fenv globalEnv env thetas fst var fst_v cor_factor
  | var `elem` witnessedVars (getTypeInfo rst) = getInvValue fenv globalEnv env thetas rst var (VList rst_v) cor_factor
getInvValue fenv globalEnv env thetas (LetIn ti name decl expr) var val cor_factor =
  getInvValue fenv globalEnv env thetas expr var val cor_factor
-- Correction factor not correctly calculated since its not used atm
getInvValue fenv globalEnv env thetas ee@(IfThenElse ti cond tr fl) var val cor_factor
  | var `elem` witnessedVars (getTypeInfo  tr) && var `elem` witnessedVars (getTypeInfo  fl) = (VBranch leftVal rightVal var, 1, Map.singleton ee [var])
  -- TODO make these two cases below useful
  | otherwise = error "non-witnessed if-then-else branches"
  -- TODO: What if subtrees have more branches
  where (leftVal, leftCor, _) = getInvValue fenv globalEnv env thetas tr var val cor_factor
        (rightVal, rightCor, _) = getInvValue fenv globalEnv env thetas fl var val cor_factor
getInvValue _ _ _ _ _ _ _ _ = error "bij inv not implemented for expr here"