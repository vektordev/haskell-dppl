module SPLL.IRCompiler where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.IROptimizer
import PredefinedFunctions
import Control.Monad.Supply
import SPLL.Typing.PType 
import SPLL.InferenceRule (algName)
import Debug.Trace
import Data.Maybe
import Control.Monad.Writer.Lazy
import Control.Monad.Reader
import Data.Functor.Identity
import Data.Number.Erf (erf)
import SPLL.AutoNeural

-- SupplyT needs to be a transformer, because Supply does not implement Functor correctly
type CompilerMonad a = WriterT [(String, IRExpr)] (SupplyT Int Identity) a

type CompilationResult = (IRExpr, IRExpr, IRExpr)

-- (name, ((RType of (Var name)), (Has _gen _prop _integ (if applicable) functions)))
type TypeEnv = [(String, (RType, Bool))]

-- perhaps as an explicit lambda in the top of the expression, otherwise we'll get trouble generating code.
-- TODO: How do we deal with top-level lambdas in binding here?
--  TL-Lambdas are presumably to be treated differently than non-TL, at least as far as prob is concerned.
envToIR :: CompilerConfig -> Program -> [(String, IRExpr)]
envToIR conf p = 
  concatMap (makeAutoNeural conf) (neurals p) ++ 
  concatMap (\(name, binding) ->
    let typeEnv = getGlobalTypeEnv p
        pt = pType $ getTypeInfo binding
        rt = rType $ getTypeInfo binding in
      if (pt == Deterministic || pt == Integrate) && (isOnlyNumbers rt) then
        [(name ++ "_integ", postProcess conf (IRLambda "low" (IRLambda "high" (runCompile conf (toIRIntegrateSave conf typeEnv binding (IRVar "low") (IRVar "high")))))),
        (name ++ "_prob",postProcess conf (IRLambda "sample" (runCompile conf (toIRProbability conf typeEnv binding (IRVar "sample"))))),
        (name ++ "_gen", postProcess conf (fst $ runIdentity $ runSupplyVars $ runWriterT (toIRGenerate typeEnv binding)))]
      else if pt == Deterministic || pt == Integrate || pt == Prob then
        [(name ++ "_prob",postProcess conf ((IRLambda "sample" (runCompile conf (toIRProbability conf typeEnv binding (IRVar "sample")))))),
        (name ++ "_gen", postProcess conf (fst $ runIdentity $ runSupplyVars $ runWriterT $ toIRGenerate typeEnv binding))]
      else
        [(name ++ "_gen", postProcess conf ( fst $ runIdentity $ runSupplyVars $ runWriterT $ toIRGenerate typeEnv binding))]) (functions p)


runCompile :: CompilerConfig -> CompilerMonad CompilationResult -> IRExpr
runCompile conf codeGen = generateLetInBlock conf (runWriterT codeGen)
  
generateLetInBlock :: CompilerConfig -> (SupplyT Int Identity) (CompilationResult, [(String, IRExpr)]) -> IRExpr
generateLetInBlock conf codeGen = 
  case m of 
    (IRLambda _ _) -> (foldr (\(var, val) expr  -> IRLetIn var val expr) m binds) --Dont make tuple out of lambdas, as the snd (and thr) element don't contain information anyway
    _ -> if countBranches conf && not (isLambda m) then
            (foldr (\(var, val) expr  -> IRLetIn var val expr) (IRTCons m (IRTCons dim bc)) binds)
          else
            (foldr (\(var, val) expr  -> IRLetIn var val expr) (IRTCons m dim) binds)
  where ((m, dim, bc), binds) = runIdentity $ runSupplyVars codeGen

-- Return type (name, rType, hasInferenceFunctions)
getGlobalTypeEnv :: Program -> TypeEnv
getGlobalTypeEnv p = funcEnv ++ neuralEnv
  where funcEnv = map (\(name, expr) -> (name, (rType (getTypeInfo expr), True))) (functions p)
        neuralEnv = map (\(name, rt, _) -> (name, (rt, False))) (neurals p)

runSupplyVars :: (Monad m) => SupplyT Int m a -> m a
runSupplyVars codeGen = runSupplyT codeGen (+1) 1


mkVariable :: String -> CompilerMonad  Varname
mkVariable suffix = do
  varID <- demand
  return ("l_" ++ show varID ++ "_" ++ suffix)

hasAlgorithm :: [Tag] -> String -> Bool
hasAlgorithm tags alg = alg `elem` ([algName a | Alg a <- tags])
--hasAlgorithm tags alg = not $ null $ filter (== alg) [a | Alg a <- tags]

const0 :: IRExpr
const0 = IRConst (VFloat 0)

--in this implementation, I'll forget about the distinction between PDFs and Probabilities. Might need to fix that later.
toIRProbability :: CompilerConfig -> TypeEnv -> Expr -> IRExpr -> CompilerMonad CompilationResult
--toIRProbability conf typeEnv expr sample | trace (show expr) False = undefined
toIRProbability conf typeEnv (IfThenElse t cond left right) sample = do
  var_condT_p <- mkVariable "condT"
  var_condF_p <- mkVariable "condF"
  (condTrueExpr, condTrueDim, condTrueBranches) <- toIRProbability conf typeEnv cond (IRConst (VBool True))
  (condFalseExpr, condFalseDim, condFalseBranches) <- toIRProbability conf typeEnv cond (IRConst (VBool False))
  (leftExpr, leftDim, leftBranches) <- toIRProbability conf typeEnv left sample
  (rightExpr, rightDim, rightBranches) <- toIRProbability conf typeEnv right sample
  let branches = (IROp OpPlus condTrueBranches ((IROp OpPlus leftBranches rightBranches)))
  -- p(y) = if p_cond < thresh then p_else(y) * (1-p_cond(y)) else if p_cond > 1 - thresh then p_then(y) * p_cond(y) else p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
  let thr = topKThreshold conf
  case thr of
    Just thresh -> do
      mul1 <- (condTrueExpr, condTrueDim) `multP` (leftExpr, leftDim)
      mul2 <- (condFalseExpr, condFalseDim) `multP` (rightExpr, rightDim)
      add <- mul1 `addP` mul2
      let returnExpr = IRIf
            (IROp OpLessThan (IRVar var_condT_p) (IRConst (VFloat thresh)))
            (fst mul2)
            (IRIf (IROp OpGreaterThan (IRVar var_condT_p) (IRConst (VFloat (1-thresh))))
              (fst mul1)
              (fst add))
      let returnDim = IRIf
            (IROp OpLessThan (IRVar var_condT_p) (IRConst (VFloat thresh)))
            (snd mul2)
            (IRIf (IROp OpGreaterThan (IRVar var_condT_p) (IRConst (VFloat (1-thresh))))
              (snd mul1)
              (snd add))
      tell [(var_condT_p, condTrueExpr), (var_condF_p, condFalseExpr)]
      return (returnExpr, returnDim, branches)
    -- p(y) = p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
    Nothing -> do
      mul1 <- (condTrueExpr, condTrueDim) `multP` (leftExpr, leftDim)
      mul2 <- (condFalseExpr, condFalseDim) `multP` (rightExpr, rightDim)
      returnExpr <- mul1 `addP` mul2
      tell [(var_condT_p, condTrueExpr), (var_condF_p, condFalseExpr)]
      return (fst returnExpr, snd returnExpr, branches)
toIRProbability conf typeEnv (GreaterThan (TypeInfo {rType = t, tags = extras}) left right) sample
  --TODO: Find a better lower bound than just putting -9999999
  | extras `hasAlgorithm` "greaterThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate typeEnv left
    tell [(var, l)]
    (integrate, _, integrateBranches) <- toIRIntegrate conf typeEnv right (IRConst (VFloat (-9999999))) (IRVar var)
    var2 <- mkVariable "rhs_integral"
    let returnExpr = 
          (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)))
    tell [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | extras `hasAlgorithm` "greaterThanRight" = do --p(x | var >= const
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate typeEnv right
    tell [(var, r)]
    (integrate, _, integrateBranches) <- toIRIntegrate conf typeEnv left (IRConst (VFloat (-9999999))) (IRVar var)
    var2 <- mkVariable "lhs_integral"
    let returnExpr = (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)) (IRVar var2))
    tell [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
toIRProbability conf typeEnv (LessThan (TypeInfo {rType = t, tags = extras}) left right) sample
  --TODO: Find a better lower bound than just putting -9999999
  | extras `hasAlgorithm` "lessThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate typeEnv left
    tell [(var, l)]
    (integrate, _, integrateBranches) <- toIRIntegrate conf typeEnv right (IRVar var) (IRConst (VFloat (9999999)))
    var2 <- mkVariable "rhs_integral"
    let returnExpr = (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)))
    tell [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | extras `hasAlgorithm` "lessThanRight" = do --p(x | var >= const
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate typeEnv right
    tell [(var, r)]
    (integrate, _, integrateBranches) <- toIRIntegrate conf typeEnv left (IRVar var) (IRConst (VFloat (9999999)))
    var2 <- mkVariable "lhs_integral"
    tell [(var2, integrate)]
    let returnExpr = (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))  (IRVar var2))
    return (returnExpr, const0, integrateBranches)
toIRProbability conf typeEnv (MultF (TypeInfo {rType = TFloat, tags = extras}) left right) sample
  | extras `hasAlgorithm` "multLeft" = do
    var <- mkVariable ""
    l <- toIRGenerate typeEnv left
    tell [(var, l)]
    (rightExpr, rightDim, rightBranches) <- toIRProbability conf typeEnv right (IROp OpDiv sample (IRVar var))
    let returnExpr = IROp OpDiv rightExpr (IRUnaryOp OpAbs (IRVar var)) 
    return (returnExpr, rightDim, rightBranches)
  | extras `hasAlgorithm` "multRight" = do
    var <- mkVariable ""
    r <- toIRGenerate typeEnv right
    tell [(var, r)]
    (leftExpr, leftDim, leftBranches) <- toIRProbability conf typeEnv left (IROp OpDiv sample (IRVar var))
    let returnExpr = IROp OpDiv leftExpr (IRUnaryOp OpAbs (IRVar var))
    return (returnExpr, leftDim, leftBranches)
toIRProbability conf typeEnv (PlusF (TypeInfo {rType = TFloat, tags = extras}) left right) sample
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    l <- toIRGenerate typeEnv left
    tell [(var, l)]
    (rightExpr, rightDim, rightBranches) <- toIRProbability conf typeEnv right (IROp OpSub sample (IRVar var))
    return (rightExpr, rightDim, rightBranches)
  | extras `hasAlgorithm` "plusRight" = do
    var <- mkVariable ""
    r <- toIRGenerate typeEnv right
    tell [(var, r)]
    (leftExpr, leftDim, leftBranches) <- toIRProbability conf typeEnv left (IROp OpSub sample (IRVar var))
    return (leftExpr, leftDim, leftBranches)
toIRProbability conf typeEnv (PlusI (TypeInfo {rType = TInt, tags = extras}) left right) sample
  | extras `hasAlgorithm` "enumeratePlusLeft" = do
    --Solving enumPlusLeft works by enumerating all left hand side choices.
    -- We then invert the addition to infer the right hand side.
    -- TODO: Theoretical assessment whether there's a performance or other difference between enumLeft and enumRight.
    let extrasLeft = tags $ getTypeInfo left
    let extrasRight = tags $ getTypeInfo right
    let enumListL = head $ [x | EnumList x <- extrasLeft]
    let enumListR = head $ [x | EnumList x <- extrasRight]
    enumVar <- mkVariable "enum"
  
    -- We need to unfold the monad stack, because the EnumSum Works like a lambda expression and has a local scope
    irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (do
      --the subexpr in the loop must compute p(enumVar| left) * p(inverse | right)
      (pLeft, _, _) <- toIRProbability conf typeEnv left (IRVar enumVar)
      (pRight, _, _) <- toIRProbability conf typeEnv right (IROp OpSub sample (IRVar enumVar))
      let returnExpr = case topKThreshold conf of
            Nothing -> IRIf (IRElementOf (IROp OpSub sample (IRVar enumVar)) (IRConst (fmap failConversion (VList enumListR)))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
            Just thr -> IRIf (IROp OpAnd (IRElementOf (IROp OpSub sample (IRVar enumVar)) (IRConst (fmap failConversion (VList enumListR)))) (IROp OpGreaterThan pLeft (IRConst (VFloat thr)))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
      -- TODO correct branch counting
      return (returnExpr, const0, const0)))
    return (IREnumSum enumVar (fmap failConversion (VList enumListL)) $ IRTFst irTuple, const0, const0)
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    (rightExpr, _, rightBranches) <- toIRProbability conf typeEnv right (IROp OpSub sample (IRVar var))
    l <- toIRGenerate typeEnv left
    tell [(var, l)]
    return (rightExpr, const0, rightBranches)
toIRProbability conf typeEnv (ExpF TypeInfo {rType = TFloat} f) sample = do --FIXME correct Inference
  error "deprecated: Use InjF instead"
toIRProbability conf typeEnv (NegF (TypeInfo {rType = TFloat, tags = extra}) f) sample =
  toIRProbability conf typeEnv f (IRUnaryOp OpNeg sample)
toIRProbability conf typeEnv (Not (TypeInfo {rType = TBool}) f) sample =
  toIRProbability conf typeEnv f (IRUnaryOp OpNot sample)
toIRProbability conf typeEnv (ReadNN _ name symbol) sample = do
  -- Same code as for calling a top level function
  var <- mkVariable "callNN"
  sym <- toIRGenerate typeEnv symbol
  tell [(var, IRInvoke (IRApply (IRApply (IRVar (name ++ "_prob")) sym) sample))]
  if countBranches conf then
    return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
  else
    return (IRTFst (IRVar var), IRTSnd (IRVar var), const0)
toIRProbability conf typeEnv (Normal t) sample = return (IRDensity IRNormal sample, IRConst $ VFloat 1, const0)
toIRProbability conf typeEnv (Uniform t) sample = return (IRDensity IRUniform sample, IRConst $ VFloat 1, const0)
toIRProbability conf typeEnv (Lambda t name subExpr) sample = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      -- Lambda parameter is a function
      let newTypeEnv = (name, (paramRType, True)):typeEnv
      irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (toIRProbability conf newTypeEnv subExpr sample))
      return (IRLambda name irTuple, const0, const0)
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv
      irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (toIRProbability conf newTypeEnv subExpr sample))
      return (IRLambda name irTuple, const0, const0)
toIRProbability conf typeEnv (Apply TypeInfo{rType=rt} l v) sample = do
  vIR <- toIRGenerate typeEnv v
  (lIR, _, _) <- toIRProbability conf typeEnv l sample -- Dim and BC are irrelevant here. We need to extract these from the return tuple
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> if countBranches conf then
           return (IRTFst (IRInvoke (IRApply lIR vIR)), IRTFst (IRTSnd (IRInvoke (IRApply lIR vIR))), IRTSnd (IRTSnd (IRInvoke (IRApply lIR vIR))))
         else
           return (IRTFst (IRInvoke (IRApply lIR vIR)), IRTSnd (IRInvoke (IRApply lIR vIR)), const0)
toIRProbability conf typeEnv (Cons _ hdExpr tlExpr) sample = do
  (headP, headDim, headBranches) <- toIRProbability conf typeEnv hdExpr (IRHead sample)
  (tailP, tailDim, tailBranches) <- toIRProbability conf typeEnv tlExpr (IRTail sample)
  mult <- (headP, headDim)  `multP` (tailP, tailDim)
  return (IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (fst mult), IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (snd mult), IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (IROp OpPlus headBranches tailBranches))
  --return (IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (fst mult), IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (snd mult), IROp OpPlus headBranches tailBranches)
toIRProbability conf typeEnv (TCons _ t1Expr t2Expr) sample = do
  (t1P, t1Dim, t1Branches) <- toIRProbability conf typeEnv t1Expr (IRTFst sample)
  (t2P, t2Dim, t2Branches) <- toIRProbability conf typeEnv t2Expr (IRTSnd sample)
  mult <- (t1P, t1Dim) `multP` (t2P, t2Dim)
  return (fst mult, snd mult, IROp OpPlus t1Branches t2Branches)
toIRProbability conf typeEnv (InjF _ name [param]) sample = do
  fPair <- instantiate mkVariable name  -- FPair of the InjF with unique names
  let FPair (_, [inv]) = fPair
  let FDecl (_, [v], _, invExpr, [(_, invDerivExpr)]) = inv
  let letInBlock = IRLetIn v sample invExpr
  (paramExpr, paramDim, paramBranches) <- toIRProbability conf typeEnv param letInBlock
  let returnExpr = IRLetIn v sample (IROp OpMult paramExpr (IRUnaryOp OpAbs invDerivExpr))
  return (returnExpr, paramDim, paramBranches)
toIRProbability conf typeEnv (InjF TypeInfo {rType=TFloat, tags=extras} name [param1, param2]) sample
  | extras `hasAlgorithm` "injF2Left" = do
  fPair <- instantiate mkVariable name -- FPair of the InjF with unique names
  let FPair (fwd, inversions) = fPair
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v3==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, invDerivs) = invDecl
  let Just invDeriv = lookup v1 invDerivs
  leftExpr <- toIRGenerate typeEnv param1
  let (detVar, sampleVar) = if x2 == v2 then (x2, x3) else (x3, x2)
  let letInBlock = IRLetIn detVar leftExpr (IRLetIn sampleVar sample invExpr)
  (paramExpr, paramDim, paramBranches) <- toIRProbability conf typeEnv param2 letInBlock
  let returnExpr = IRLetIn detVar leftExpr (IRLetIn sampleVar sample (IROp OpMult paramExpr (IRUnaryOp OpAbs invDeriv)))
  return (returnExpr, paramDim, paramBranches) --FIXME
toIRProbability conf typeEnv (InjF TypeInfo {rType=TFloat, tags=extras} name [param1, param2]) sample
  | extras `hasAlgorithm` "injF2Right" = do
  fPair <- instantiate mkVariable name -- FPair of the InjF with unique names
  let FPair (fwd, inversions) = fPair 
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v2==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, invDerivs) = invDecl
  let Just invDeriv = lookup v1 invDerivs
  leftExpr <- toIRGenerate typeEnv param2
  let (detVar, sampleVar) = if x2 == v3 then (x2, x3) else (x3, x2)
  let letInBlock = IRLetIn detVar leftExpr (IRLetIn sampleVar sample invExpr)
  (paramExpr, paramDim, paramBranches) <- toIRProbability conf typeEnv param1 letInBlock
  let returnExpr = IRLetIn detVar leftExpr (IRLetIn sampleVar sample (IROp OpMult paramExpr (IRUnaryOp OpAbs invDeriv)))
  return (returnExpr, paramDim, paramBranches)
toIRProbability conf typeEnv (InjF TypeInfo {tags=extras} name [left, right]) sample
  | extras `hasAlgorithm` "injF2Enumerable" = do
  -- Get all possible values for subexpressions
  let extrasLeft = tags $ getTypeInfo left
  let extrasRight = tags $ getTypeInfo right
  let enumListL = head $ [x | EnumList x <- extrasLeft]
  let enumListR = head $ [x | EnumList x <- extrasRight]

  fPair <- instantiate mkVariable name -- FPair of the InjF with unique names
  let FPair (fwd, inversions) = fPair
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  -- We get the inversion to the right side
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v3==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, _) = invDecl

  -- We now compute
  -- for each e in leftEnum:
  --   sum += if invExpr(e, sample) in rightEnum then pLeft(e) * pRight(sample - e) else 0
  -- For that we name e like the lhs of
  -- We need to unfold the monad stack, because the EnumSum Works like a lambda expression and has a local scope
  irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (do
    --the subexpr in the loop must compute p(enumVar| left) * p(inverse | right)
    (pLeft, _, _) <- toIRProbability conf typeEnv left (IRVar x2)
    (pRight, _, _) <- toIRProbability conf typeEnv right (IROp OpSub sample (IRVar x2))
    tell [(x3, sample)]
    let returnExpr = case topKThreshold conf of
          Nothing -> IRIf (IRElementOf invExpr (IRConst (fmap failConversion (VList enumListR)))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
          Just thr -> IRIf (IROp OpAnd (IRElementOf invExpr (IRConst (fmap failConversion (VList enumListR)))) (IROp OpGreaterThan pLeft (IRConst (VFloat thr)))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
    -- TODO correct branch counting
    return (returnExpr, const0, const0)))
  uniquePrefix <- mkVariable ""
  let enumSumExpr = IREnumSum x2 (fmap failConversion (VList enumListL)) $ IRTFst irTuple
  return (irMap (uniqueify [x2, x3] uniquePrefix) enumSumExpr, const0, const0)
toIRProbability conf typeEnv (Null _) sample = do
  expr <- indicator (IROp OpEq sample (IRConst $ VList []))
  return (expr, const0, const0)
toIRProbability conf typeEnv (Constant _ value) sample = do
  expr <- indicator (IROp OpEq sample (IRConst (fmap failConversion value)))
  return (expr, const0, const0)
toIRProbability conf typeEnv (Var _ n) sample = do
  -- Variable might be a function
  case lookup n typeEnv of
    -- Var is a function
    Just(TArrow _ _, _) -> do
      var <- mkVariable "call"
      tell [(var, IRApply (IRVar (n ++ "_prob")) sample)]
      -- The return value is still a function. No need to do dim and branch counting here
      return (IRVar var, const0, const0)
    -- Var is a top level declaration (an therefor has a _prob function)
    Just (_, True) -> do
      var <- mkVariable "call"
      tell [(var, IRInvoke (IRApply (IRVar (n ++ "_prob")) sample))]
      if countBranches conf then
          return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
        else
          return (IRTFst (IRVar var), IRTSnd (IRVar var), const0)
    -- Var is a local variable
    Just (_, False) -> do
      expr <- indicator (IROp OpEq sample (IRVar n))
      return (expr, const0, const0)
    Nothing -> error ("Could not find name in TypeEnv: " ++ n)
toIRProbability conf typeEnv (ThetaI _ a i) sample = do
  a' <- toIRGenerate typeEnv a
  expr <- indicator (IROp OpEq sample (IRTheta a' i))
  return (expr, const0, const0)
toIRProbability conf typeEnv (Subtree _ a i) sample = error "Cannot infer prob on subtree expression. Please check your syntax"
toIRProbability conf typeEnv x sample = error ("found no way to convert to IR: " ++ show x)

multP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
multP (aM, aDim) (bM, bDim) = return (IROp OpMult aM bM, IROp OpPlus aDim bDim)

addP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
addP (aM, aDim) (bM, bDim) = do
  pVarA <- mkVariable "pA"
  pVarB <- mkVariable "pB"
  dimVarA <- mkVariable "dimA"
  dimVarB <- mkVariable "dimB"
  tell [(pVarA, aM), (pVarB, bM), (dimVarA, aDim), (dimVarB, bDim)]
  return (IRIf (IROp OpEq (IRVar pVarA) (IRConst (VFloat 0))) (IRVar pVarB)
           (IRIf (IROp OpEq (IRVar pVarB) (IRConst (VFloat 0))) (IRVar pVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar pVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar pVarB)
           (IROp OpPlus (IRVar pVarA) (IRVar pVarB))))),
           -- Dim
           IRIf (IROp OpEq (IRVar pVarA) (IRConst (VFloat 0))) (IRVar dimVarB)
           (IRIf (IROp OpEq (IRVar pVarB) (IRConst (VFloat 0))) (IRVar dimVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar dimVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar dimVarB)
           (IRVar dimVarA)))))

subP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
subP (aM, aDim) (bM, bDim) = do
  pVarA <- mkVariable "pA"
  pVarB <- mkVariable "pB"
  dimVarA <- mkVariable "dimA"
  dimVarB <- mkVariable "dimB"
  tell [(pVarA, aM), (pVarB, bM), (dimVarA, aDim), (dimVarB, bDim)]
  return (IRIf (IROp OpEq (IRVar pVarA) (IRConst (VFloat 0))) (IRVar pVarB)
         (IRIf (IROp OpEq (IRVar pVarB) (IRConst (VFloat 0))) (IRVar pVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar pVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar pVarB)
         (IROp OpSub (IRVar pVarA) (IRVar pVarB))))),
         -- Dim
         IRIf (IROp OpEq (IRVar pVarA) (IRConst (VFloat 0))) (IRVar dimVarB)
         (IRIf (IROp OpEq (IRVar pVarB) (IRConst (VFloat 0))) (IRVar dimVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar dimVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar dimVarB)
         (IRVar dimVarA)))))

packParamsIntoLetinsProb :: [String] -> [Expr] -> IRExpr -> IRExpr -> Supply Int IRExpr
--packParamsIntoLetinsProb [] [] expr _ = do
--  return expr
--packParamsIntoLetinsProb [] _ _ _ = error "More parameters than variables"
--packParamsIntoLetinsProb _ [] _ _ = error "More variables than parameters"
--packParamsIntoLetinsProb (v:vars) (p:params) expr sample = do
--  e <- packParamsIntoLetinsProb vars params expr sample
--  return $ IRLetIn v sample e --TODO sample austauschen durch teil von sample falls multivariable
packParamsIntoLetinsProb [v] [p] expr sample = do
  return $ IRLetIn v sample expr    --FIXME sample to auch toIRProbt werden

indicator :: IRExpr -> CompilerMonad  IRExpr
indicator condition = return $ IRIf condition (IRConst $ VFloat 1) (IRConst $ VFloat 0)

-- Must be used in conjunction with irMap, as it does not recurse
uniqueify :: [Varname] -> String -> IRExpr -> IRExpr
uniqueify vars prefix (IRVar name) | name `elem` vars = IRVar (prefix ++ name)
uniqueify vars prefix (IRLetIn name boundExpr bodyExpr) | name `elem` vars = IRLetIn (prefix ++ name) (uniqueify vars prefix boundExpr) (uniqueify vars prefix bodyExpr)
uniqueify vars prefix (IREnumSum name lst bodyExpr) | name `elem` vars = IREnumSum (prefix ++ name) lst (uniqueify vars prefix bodyExpr)
uniqueify _ _ e = e

--folding detGen and Gen into one, as the distinction is one to make sure things that are det are indeed det.
-- That's what the type system is for though.
toIRGenerate :: TypeEnv -> Expr -> CompilerMonad  IRExpr
toIRGenerate typeEnv (IfThenElse _ cond left right) = do
  c <- toIRGenerate typeEnv cond
  l <- toIRGenerate typeEnv left
  r <- toIRGenerate typeEnv right
  return $ IRIf c l r
toIRGenerate typeEnv (LetIn _ n v b) = do
  v' <- toIRGenerate typeEnv v
  b' <- toIRGenerate typeEnv b
  return $ IRLetIn n v' b'
toIRGenerate typeEnv (GreaterThan _ left right) = do
  l <- toIRGenerate typeEnv left
  r <- toIRGenerate typeEnv right
  return $ IROp OpGreaterThan l r
toIRGenerate typeEnv (LessThan _ left right) = do
  l <- toIRGenerate typeEnv left
  r <- toIRGenerate typeEnv right
  return $ IROp OpLessThan l r
toIRGenerate typeEnv (PlusF _ left right) = do
  l <- toIRGenerate typeEnv left
  r <- toIRGenerate typeEnv right
  return $ IROp OpPlus l r
toIRGenerate typeEnv (PlusI _ left right) = do
  l <- toIRGenerate typeEnv left
  r <- toIRGenerate typeEnv right
  return $ IROp OpPlus l r
toIRGenerate typeEnv (MultF _ left right) = do
  l <- toIRGenerate typeEnv left
  r <- toIRGenerate typeEnv right
  return $ IROp OpMult l r
toIRGenerate typeEnv (MultI _ left right) = do
  l <- toIRGenerate typeEnv left
  r <- toIRGenerate typeEnv right
  return $ IROp OpMult l r
toIRGenerate typeEnv (ExpF _ f) = do
  f' <- toIRGenerate typeEnv f
  return $ IRUnaryOp OpExp f'
toIRGenerate typeEnv (NegF _ f) = do
  f' <- toIRGenerate typeEnv f
  return $ IRUnaryOp OpNeg f'
toIRGenerate typeEnv (Not _ f) = do
  f' <- toIRGenerate typeEnv f
  return $ IRUnaryOp OpNot f'
toIRGenerate typeEnv (ThetaI _ a ix) = do
  a' <- toIRGenerate typeEnv a
  return $ IRTheta a' ix
toIRGenerate typeEnv (Subtree _ a ix) = do
  a' <- toIRGenerate typeEnv a
  return $ IRSubtree a' ix
toIRGenerate typeEnv (Constant _ x) = return (IRConst (fmap failConversion x))
toIRGenerate typeEnv (Null _) = return $ IRConst (VList [])
toIRGenerate typeEnv (Cons _ hd tl) = do
  h <- toIRGenerate typeEnv hd
  t <- toIRGenerate typeEnv tl
  return $ IRCons h t
toIRGenerate typeEnv (TCons _ t1 t2) = do
  t1' <- toIRGenerate typeEnv t1
  t2' <- toIRGenerate typeEnv t2
  return $ IRTCons t1' t2'
toIRGenerate typeEnv (Uniform _) = return $ IRSample IRUniform
toIRGenerate typeEnv (Normal _) = return $ IRSample IRNormal
toIRGenerate typeEnv (InjF _ name params) = do
  -- Assuming that the logic within packParamsIntoLetinsGen typeEnv is correct.
  -- You will need to process vars and params, followed by recursive calls to fwdExpr.
  fPair <- instantiate mkVariable name
  let FPair (fwd, _) = fPair
  let FDecl (_, vars, _, fwdExpr, _) = fwd
  prefix <- mkVariable ""
  packParamsIntoLetinsGen typeEnv vars params fwdExpr
toIRGenerate typeEnv (Var _ name) = do
  case lookup name typeEnv of
    -- Var is a function
    Just (TArrow _ _, _) ->
      return $ IRVar (name ++ "_gen")
    -- Var is a top level declaration (an therefor has a _gen function)
    Just (_, True) -> do
      return $ IRInvoke (IRVar (name ++ "_gen"))
    -- Var is a local variable
    Just (_, False) -> do
      return $ IRVar name
    Nothing -> error ("Could not find name in TypeEnv: " ++ name)
toIRGenerate typeEnv (Lambda t name subExpr) = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      let newTypeEnv = (name, (paramRType, True)):typeEnv
      irTuple <- toIRGenerate newTypeEnv subExpr
      return $ IRLambda name irTuple
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv
      irTuple <- toIRGenerate newTypeEnv subExpr
      return $ IRLambda name irTuple
toIRGenerate typeEnv (Apply TypeInfo {rType=rt} l v) = do
  l' <- toIRGenerate typeEnv l
  v' <- toIRGenerate typeEnv v
  case rt of
    TArrow _ _ -> return $ IRApply l' v'
    _ -> return $ IRInvoke $ IRApply l' v'
toIRGenerate typeEnv (ReadNN _ name subexpr) = do
  sub <- toIRGenerate typeEnv subexpr
  return $ IRInvoke (IRApply (IRVar (name ++ "_gen")) sub)
toIRGenerate typeEnv x = error ("found no way to convert to IRGen: " ++ show x)

packParamsIntoLetinsGen :: TypeEnv -> [String] -> [Expr] -> IRExpr -> CompilerMonad  IRExpr
packParamsIntoLetinsGen typeEnv [] [] expr = return $ expr
packParamsIntoLetinsGen typeEnv [] _ _ = error "More parameters than variables"
packParamsIntoLetinsGen typeEnv _ [] _ = error "More variables than parameters"
packParamsIntoLetinsGen typeEnv (v:vars) (p:params) expr = do
  pExpr <- toIRGenerate typeEnv p
  e <- packParamsIntoLetinsGen typeEnv vars params expr
  return $ IRLetIn v pExpr e
 
--Adds an additional check that the bounds are not equal
--We need this bounds check only once, because no invertible transformation can make the bounds be equal when they were not
--TODO: Some InjF could lead to CoV, which would make the bounds check at the to wrong
toIRIntegrateSave :: CompilerConfig -> TypeEnv -> Expr -> IRExpr -> IRExpr -> CompilerMonad CompilationResult
toIRIntegrateSave conf typeEnv (Lambda t name subExpr) low high = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      let newTypeEnv = (name, (paramRType, True)):typeEnv
      irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (toIRIntegrateSave conf newTypeEnv subExpr low high))
      return (IRLambda name irTuple, const0, const0)
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv
      irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (toIRIntegrateSave conf newTypeEnv subExpr low high))
      return (IRLambda name irTuple, const0, const0)
toIRIntegrateSave conf typeEnv expr lower higher = do 
  (prob, probDim, probBC) <- toIRProbability conf typeEnv expr lower
  (integ, integDim, integBC) <- toIRIntegrate conf typeEnv expr lower higher
  return (IRIf (IROp OpEq lower higher) prob integ, IRIf (IROp OpEq lower higher) probDim integDim, IRIf (IROp OpEq lower higher) probBC integBC)


toIRIntegrate :: CompilerConfig -> TypeEnv -> Expr -> IRExpr -> IRExpr -> CompilerMonad CompilationResult
toIRIntegrate conf typeEnv expr@(Uniform _) lower higher = do
  (density, _, _) <- toIRProbability conf typeEnv expr lower
  --let expr = IRIf (IROp OpEq lower higher) density (IROp OpSub (IRCumulative IRUniform higher) (IRCumulative IRUniform lower))
  let expr = (IROp OpSub (IRCumulative IRUniform higher) (IRCumulative IRUniform lower))
  return (expr, IRIf (IROp OpEq lower higher) (IRConst $ VFloat 1) const0, const0)
toIRIntegrate conf typeEnv expr@(Normal _) lower higher = do
  (density, _, _) <- toIRProbability conf typeEnv expr lower
  --let expr = IRIf (IROp OpEq lower higher) density (IROp OpSub (IRCumulative IRNormal higher) (IRCumulative IRNormal lower))
  let expr = (IROp OpSub (IRCumulative IRNormal higher) (IRCumulative IRNormal lower))
  return (expr, IRIf (IROp OpEq lower higher) (IRConst $ VFloat 1) const0, const0)
toIRIntegrate conf typeEnv (MultF (TypeInfo {tags = extras}) left right) lower higher
  | extras `hasAlgorithm` "multLeft" = do
    var <- mkVariable ""
    (rightExpr, _, rightBranches) <- toIRIntegrate conf typeEnv right (IROp OpDiv lower (IRVar var)) (IROp OpDiv higher (IRVar var))
    l <- toIRGenerate typeEnv left
    tell [(var, l)]
    return (rightExpr, const0, rightBranches)
  | extras `hasAlgorithm` "multRight" = do
    var <- mkVariable ""
    (leftExpr, _, leftBranches) <- toIRIntegrate conf typeEnv left (IROp OpDiv lower (IRVar var)) (IROp OpDiv higher (IRVar var))
    r <- toIRGenerate typeEnv right
    tell [(var, r)]
    return (leftExpr, const0, leftBranches)
toIRIntegrate conf typeEnv (PlusF TypeInfo {tags = extras} left right) lower higher
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    (rightExpr, _, rightBranches) <- toIRIntegrate conf typeEnv right (IROp OpSub lower (IRVar var)) (IROp OpSub higher (IRVar var))
    l <- toIRGenerate typeEnv left
    tell [(var, l)]
    return (rightExpr, const0, rightBranches)
  | extras `hasAlgorithm` "plusRight" = do
    var <- mkVariable ""
    (leftExpr, _, leftBranches) <- toIRIntegrate conf typeEnv left (IROp OpSub lower (IRVar var)) (IROp OpSub higher (IRVar var))
    r <- toIRGenerate typeEnv right
    tell [(var, r)]
    return (leftExpr, const0, leftBranches)
toIRIntegrate conf typeEnv (NegF _ a) low high = do
  toIRIntegrate conf typeEnv a (IRUnaryOp OpNeg high) (IRUnaryOp OpNeg low)
toIRIntegrate conf typeEnv (ExpF _ a) low high = do
  error "deprecated: Use InjF instead"
toIRIntegrate conf typeEnv (TCons _ t1Expr t2Expr) low high = do
  (t1P, t1Dim,  t1Branches) <- toIRIntegrateSave conf typeEnv t1Expr (IRTFst low) (IRTFst high)
  (t2P, t2Dim,  t2Branches) <- toIRIntegrateSave conf typeEnv t2Expr (IRTSnd low) (IRTSnd high)
  (productP, productDim) <- (t1P, t1Dim) `multP` (t2P, t2Dim)
  return (productP, productDim, IROp OpPlus t1Branches t2Branches)
toIRIntegrate conf typeEnv (IfThenElse _ cond left right) low high = do
  var_cond_p <- mkVariable "cond"
  (condExpr, _, condBranches) <- toIRProbability conf typeEnv cond (IRConst (VBool True))
  (leftExpr, _, leftBranches) <- toIRIntegrate conf typeEnv left low high
  (rightExpr, _, rightBranches) <- toIRIntegrate conf typeEnv right low high
  let thr = topKThreshold conf
  case thr of
    Just thresh -> do
        tell [(var_cond_p, condExpr)]
        return
          (IRIf (IROp OpLessThan (IRVar var_cond_p) (IRConst (VFloat thresh)))
            (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr)
            (IRIf (IROp OpGreaterThan (IRVar var_cond_p) (IRConst (VFloat (1-thresh))))
              (IROp OpMult (IRVar var_cond_p) leftExpr)
              (IROp OpPlus
                (IROp OpMult (IRVar var_cond_p) leftExpr)
                (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr))), const0, IROp OpPlus condBranches (IROp OpPlus leftBranches rightBranches) )
    -- p(y) = p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
    Nothing -> do
        tell [(var_cond_p, condExpr)]
        return
          (IROp OpPlus
            (IROp OpMult (IRVar var_cond_p) leftExpr)
            (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr), const0, IROp OpPlus condBranches (IROp OpPlus leftBranches rightBranches) )
toIRIntegrate conf typeEnv (Cons _ hdExpr tlExpr) low high = do
    (headP, headDim, headBranches) <- toIRIntegrateSave conf typeEnv hdExpr (IRHead low) (IRHead high)
    (tailP, tailDim, tailBranches) <- toIRIntegrate conf typeEnv tlExpr (IRTail low) (IRTail high)
    (multP, multDim) <- (headP, headDim) `multP` (tailP, tailDim)
    return (IRIf (IROp OpOr (IROp OpEq low (IRConst $ VList [])) (IROp OpEq high (IRConst $ VList []))) (IRConst $ VFloat 0) multP, multDim, IROp OpPlus headBranches tailBranches)
toIRIntegrate conf typeEnv (Null _) low high = do
  ind <- indicator (IROp OpAnd (IROp OpEq low (IRConst $ VList [])) (IROp OpEq high (IRConst $ VList [])))
  return (ind, const0, const0)
toIRIntegrate conf typeEnv (Constant _ value) low high = do
  ind <- indicator (IROp OpAnd (IROp OpLessThan low (IRConst (fmap failConversion value))) (IROp OpGreaterThan high (IRConst (fmap failConversion value)))) --TODO What to do if low and high are equal?
  return (ind, const0, const0)
toIRIntegrate conf typeEnv (ThetaI _ a i) low high = do
  a' <-  toIRGenerate typeEnv a
  let val = IRTheta a' i
  ind <- indicator (IROp OpAnd (IROp OpLessThan low val) (IROp OpGreaterThan high val)) --TODO What to do if low and high are equal?
  return (ind, const0, const0)
toIRIntegrate conf typeEnv (InjF _ name [param]) low high = do  --TODO Multivariable
  fPair <- instantiate mkVariable name  
  let FPair (_, [inv]) = fPair
  let FDecl (_, [v], _, invExpr, [(_, invDerivExpr)]) = inv
  prefix <- mkVariable ""
  let letInBlockLow = IRLetIn v low invExpr
  let letInBlockHigh = IRLetIn v high invExpr
  (paramExpr, _, paramBranches) <- toIRIntegrate conf typeEnv param letInBlockLow letInBlockHigh
  return (paramExpr, const0, paramBranches)
toIRIntegrate conf typeEnv (InjF TypeInfo {rType=TFloat, tags=extras} name [param1, param2]) low high
  | extras `hasAlgorithm` "injF2Left" = do  
  fPair <- instantiate mkVariable name  
  let FPair (fwd, inversions) = fPair
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v3==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, invDerivs) = invDecl
  let Just invDeriv = lookup v1 invDerivs
  leftExpr <- toIRGenerate typeEnv param1
  let (detVar, sampleVar) = if x2 == v2 then (x2, x3) else (x3, x2)
  let letInBlockLow = IRLetIn detVar leftExpr (IRLetIn sampleVar low invExpr)
  let letInBlockHigh = IRLetIn detVar leftExpr (IRLetIn sampleVar high invExpr)
  (paramExpr, _, paramBranches) <- toIRIntegrate conf typeEnv param2 letInBlockLow letInBlockHigh
  return (paramExpr, const0, paramBranches)
toIRIntegrate conf typeEnv (InjF TypeInfo {rType=TFloat, tags=extras} name [param1, param2]) low high
  | extras `hasAlgorithm` "injF2Right" = do 
  fPair <- instantiate mkVariable name
  let FPair (fwd, inversions) = fPair
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v2==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, invDerivs) = invDecl
  let Just invDeriv = lookup v1 invDerivs
  leftExpr <- toIRGenerate typeEnv param2
  let (detVar, sampleVar) = if x2 == v3 then (x2, x3) else (x3, x2)
  let letInBlockLow = IRLetIn detVar leftExpr (IRLetIn sampleVar low invExpr)
  let letInBlockHigh = IRLetIn detVar leftExpr (IRLetIn sampleVar high invExpr)
  (paramExpr, _, paramBranches) <- toIRIntegrate conf typeEnv param1 letInBlockLow letInBlockHigh
  return (paramExpr, const0, paramBranches)
toIRIntegrate conf typeEnv (Lambda t name subExpr) low high = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      let newTypeEnv = (name, (paramRType, True)):typeEnv
      irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (toIRIntegrate conf newTypeEnv subExpr low high))
      return (IRLambda name irTuple, const0, const0)
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv
      irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (toIRIntegrate conf newTypeEnv subExpr low high))
      return (IRLambda name irTuple, const0, const0)
toIRIntegrate conf typeEnv (Apply TypeInfo{rType=rt} l v) low high = do
  vIR <- toIRGenerate typeEnv v
  (lIR, _, _) <- toIRIntegrate conf typeEnv l low high -- Dim and BC are irrelevant here. We need to extract these from the return tuple
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> if countBranches conf then
           return (IRTFst (IRInvoke (IRApply lIR vIR)), IRTFst (IRTSnd (IRInvoke (IRApply lIR vIR))), IRTSnd (IRTSnd (IRInvoke (IRApply lIR vIR))))
         else
           return (IRTFst (IRInvoke (IRApply lIR vIR)), IRTSnd (IRInvoke (IRApply lIR vIR)), const0)
toIRIntegrate conf typeEnv (Var _ n) low high = do
  -- Variable might be a function
  case lookup n typeEnv of
   -- Var is a function
   Just(TArrow _ _, _) -> do
     var <- mkVariable "call"
     tell [(var, IRApply (IRApply (IRVar (n ++ "_integ")) low) high)]
     -- The return value is still a function. No need to do dim and branch counting here
     return (IRVar var, const0, const0)
   -- Var is a top level declaration (an therefor has a _prob function)
   Just (_, True) -> do
     var <- mkVariable "call"
     tell [(var, IRInvoke (IRApply (IRApply (IRVar (n ++ "_integ")) low) high))]
     if countBranches conf then
         return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
       else
         return (IRTFst (IRVar var), IRTSnd (IRVar var), const0)
   -- Var is a local variable
   Just (_, False) -> do
    ind <- indicator (IROp OpAnd (IROp OpLessThan low (IRVar n)) (IROp OpGreaterThan high (IRVar n))) --TODO What to do if low and high are equal?
    return (ind, const0, const0)
   Nothing -> error ("Could not find name in TypeEnv: " ++ n)
toIRIntegrate _ _ x _ _ = error ("found no way to convert to IRIntegrate: " ++ show x)

