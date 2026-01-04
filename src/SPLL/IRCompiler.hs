module SPLL.IRCompiler (
  envToIR
)where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import SPLL.Lang.Types hiding (HornClause)
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.IROptimizer
import PredefinedFunctions
import SPLL.Typing.PType
import SPLL.InferenceRule (algName)
import Debug.Trace
import Data.Maybe
import Control.Monad.Writer.Lazy
import Control.Monad.Reader
import Data.Functor.Identity
import Data.Number.Erf (erf)
import SPLL.AutoNeural
import Data.Functor
import SPLL.Typing.ForwardChaining
import Data.List
import SPLL.Typing.AlgebraicDataTypes
import Data.Bifunctor (Bifunctor(bimap))
import Utils
import Control.Monad (foldM)

type CompilerMonad a = WriterT [(String, IRExpr)] Supply a

type CompilationResult = (IRExpr, IRExpr, IRExpr)

-- (name, ((RType of (Var name)), (Has _gen _prop _integ (if applicable) functions)))
type TypeEnv = [(String, (RType, Bool))]

data CompilerMetadata = CompilerMetadata {
  compilerConfig :: CompilerConfig,
  fcData :: FCData,
  typeEnv :: TypeEnv,
  adtDecls :: [ADTDecl]
}

envToIR :: CompilerConfig -> Program -> IREnv
envToIR conf@CompilerConfig{noIntegrate=noInteg, noProbability=noProb, noGenerate=noGen} p@Program{adts=adts} = optimizeEnv conf $ IREnv (-- map optimizer over all second elements of the tuples
  map (makeAutoNeural conf) (neurals p) ++
  map (\(name, binding) ->
    let typeEnv = getGlobalTypeEnv p
        pt = pType $ getTypeInfo binding
        rt = rType $ getTypeInfo binding in
      IRFunGroup {groupName=name,
       integFun =
        if not noInteg && (pt == Deterministic || pt == Integrate) then
          Just (toIntegDecl name (IRLambda "sample" (runCompile (meta typeEnv) (toIRInferenceSave (meta typeEnv) True binding (IRVar "sample")))))
        else Nothing,
        probFun =
          if not noProb && (pt == Deterministic || pt == Integrate || pt == Prob) then
            Just (toProbDecl name (IRLambda "sample" (runCompile (meta typeEnv) (toIRInferenceSave (meta typeEnv) False binding (IRVar "sample")))))
          else Nothing,
        genFun = 
          if not noGen then
            Just (toGenDecl name (fst $ evalSupply $ runWriterT $ toIRGenerate (meta typeEnv) binding))
          else
            Nothing,
        groupDoc="Function group " ++ name}) (functions p)) adts

  where
    toGenDecl name expr = (expr, "Generates a random sample of the " ++ name ++ " function")
    toProbDecl name expr =
      (expr, "Calculates the probability of the sample parameter being returned from the " ++ name ++ "function")
    toIntegDecl name expr = (expr, "Calculates the probability of sample of " ++ name ++ " falling in between the parameters low and high")
    fcDat = progToFCData p
    meta typeEnv = CompilerMetadata conf fcDat typeEnv adts


runCompile :: CompilerMetadata -> CompilerMonad CompilationResult -> IRExpr
runCompile meta codeGen = generateLetInBlock meta (evalSupply $ runWriterT $ do
  (p, d, bc) <- codeGen
  case p of 
    IRLambda _ _ -> return (p, d, bc)
    _ -> tell [("l_p", p), ("l_d", d), ("l_bc", bc)] >>
                return (IRVar "l_p", IRVar "l_d", IRVar "l_bc")
  --
  )

generateLetInBlock :: CompilerMetadata -> (CompilationResult, [(String, IRExpr)]) -> IRExpr
generateLetInBlock meta codeGen =
  case m of
    (IRLambda _ _) -> (foldr (\(var, val) expr  -> IRLetIn var val expr) m binds) --Dont make tuple out of lambdas, as the snd (and thr) element don't contain information anyway
    _ -> if cb && not (isLambda m) then do
            generateLetInExpr binds (IRTCons m (IRTCons dim bc))
          else
            generateLetInExpr binds (IRTCons m dim)
  where 
    ((m, dim, bc), binds) = codeGen
    cb = countBranches (compilerConfig meta)

generateLetInExpr ::  [(Varname, IRExpr)] -> IRExpr -> IRExpr
generateLetInExpr binds e = foldr (\(var, val) expr  -> IRLetIn var val expr) e binds

-- Return type (name, rType, hasInferenceFunctions)
getGlobalTypeEnv :: Program -> TypeEnv
getGlobalTypeEnv p = funcEnv ++ implicitFuncEnv ++ neuralEnv
  where funcEnv = map (\(name, expr) -> (name, (rType (getTypeInfo expr), True))) (functions p)
        implicitFuncEnv = map (\(name, rt) -> (name, (rt, False))) (implicitFunctionsRTypeProg p)
        neuralEnv = map (\(name, rt, _) -> (name, (rt, False))) (neurals p)

mkVariable :: String -> CompilerMonad  Varname
mkVariable suffix = do
  varID <- demandUniqueNumber
  return ("l_" ++ show varID ++ "_" ++ suffix)

setVariables :: [(String, IRExpr)] -> CompilerMonad ()
setVariables = tell

hasAlgorithm :: [Tag] -> String -> Bool
hasAlgorithm tags alg = alg `elem` ([algName a | Alg a <- tags])
--hasAlgorithm tags alg = not $ null $ filter (== alg) [a | Alg a <- tags]

const0 :: IRExpr
const0 = IRConst (VFloat 0)

negInf :: IRExpr
negInf = IRConst (VFloat (-9999999))

posInf :: IRExpr
posInf = IRConst (VFloat 9999999)

renameVar :: String -> String -> IRExpr -> IRExpr
renameVar old new = irMap (renameVar' old new)

renameVar' :: String -> String -> IRExpr -> IRExpr
renameVar' old new (IRVar n) | n == old = IRVar new
renameVar' _ _ x = x

toIRInferenceSave :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad CompilationResult
toIRInferenceSave meta cumulative (Lambda t name subExpr) sample = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      let newTypeEnv = (name, (paramRType, True)):typeEnv meta
      irTuple <- lift (runWriterT (toIRInferenceSave meta {typeEnv=newTypeEnv} cumulative subExpr sample)) <&> generateLetInBlock meta
      return (IRLambda name irTuple, const0, const0)
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv meta
      irTuple <- lift (runWriterT (toIRInferenceSave meta {typeEnv=newTypeEnv} cumulative subExpr sample)) <&> generateLetInBlock meta
      return (IRLambda name irTuple, const0, const0)
toIRInferenceSave meta cumulative expr sample = do
  (probExpr, probDim, probBranches) <- toIRInference meta cumulative expr sample
  return $ (IRIf (IRUnaryOp OpIsAny sample) (IRConst (VFloat 1)) probExpr, IRIf (IRUnaryOp OpIsAny sample) const0 probDim, IRIf (IRUnaryOp OpIsAny sample) const0 probBranches)

--in this implementation, I'll forget about the distinction between PDFs and Probabilities. Might need to fix that later.
toIRInference :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad CompilationResult
--toIRInference meta cumulative expr sample | trace (show expr) False = undefined
-- CDFs on Booleans make little sense. We define that False < True. Therefor cdf(True) = 1 and cdf(False) = pdf(False)
toIRInference meta True expr sample | rType (getTypeInfo expr) == TBool = do
  (pFalse, _, bcFalse) <- toIRInference meta False expr (IRConst (VBool False))
  return (IRIf sample (IRConst (VFloat 1)) pFalse, const0, bcFalse)
toIRInference meta False (Normal t) sample = return (IRDensity IRNormal sample, IRIf (IRUnaryOp OpIsAny sample) const0 (IRConst $ VFloat 1), const0)
toIRInference meta False (Uniform t) sample = return (IRDensity IRUniform sample, IRIf (IRUnaryOp OpIsAny sample) const0 (IRConst $ VFloat 1), const0)
toIRInference meta True (Normal t) sample = return (IRCumulative IRNormal sample, const0, const0)
toIRInference meta True (Uniform t) sample = return (IRCumulative IRUniform sample, const0, const0)
toIRInference meta False (Constant TypeInfo {rType=rt} value) sample = do
  let comp = case rt of
              TFloat -> IROp OpApprox sample (IRConst (fmap failConversion value))
              _ -> IROp OpEq sample (IRConst (fmap failConversion value))
  expr <- indicator comp
  return (expr, const0, const0)
toIRInference meta True (Constant TypeInfo {rType=rt} value) sample = return (compareValueExpr rt (IRConst (valueToIR value)) sample, const0, const0)
toIRInference meta True (ThetaI _ a i) sample = do
  a' <- toIRGenerate meta a
  return (IRIf (IROp OpLessThan sample (IRTheta a' i)) (IRConst $ VFloat 0) (IRConst $ VFloat 1), const0, const0)
toIRInference meta False (ThetaI _ a i) sample = do
  a' <- toIRGenerate meta a
  expr <- indicator (IROp OpApprox sample (IRTheta a' i))
  return (expr, const0, const0)
toIRInference meta cumulative (IfThenElse t cond left right) sample = do
  var_condT_p <- mkVariable "condT"
  var_condF_p <- mkVariable "condF"
  (condTrueExpr, condTrueDim, condTrueBranches) <- toIRInference meta False  cond (IRConst (VBool True))
  (condFalseExpr, condFalseDim, condFalseBranches) <- toIRInference meta False cond (IRConst (VBool False))
  (leftExpr, leftDim, leftBranches) <- toIRInference meta cumulative left sample
  (rightExpr, rightDim, rightBranches) <- toIRInference meta cumulative right sample
  let branches = (IROp OpPlus condTrueBranches ((IROp OpPlus leftBranches rightBranches)))
  setVariables [(var_condT_p, condTrueExpr), (var_condF_p, condFalseExpr)]
  -- p(y) = if p_cond < thresh then p_else(y) * (1-p_cond(y)) else if p_cond > 1 - thresh then p_then(y) * p_cond(y) else p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
  let thr = topKThreshold (compilerConfig meta)

  -- We need to restart the monad stack, because variables inside the branches may not be valid outside
  -- E.g. if length(a) > 0 then a[0] else ...
  -- If we were to access a[0] outside of the branch we would error
  ((mul1Raw, leftBranches), binds1) <- lift (runWriterT (do
    (leftExpr, leftDim, branches) <- toIRInference meta cumulative left sample
    (IRVar var_condT_p, condTrueDim) `multP` (leftExpr, leftDim) <&> (\x -> (x, branches)))) -- We need the branches outside of this scope. Append it to the tuple
  let mul1 = bimap (generateLetInExpr binds1) (generateLetInExpr binds1) mul1Raw
  ((mul2Raw, rightBranches), binds2) <- lift (runWriterT (do
    (rightExpr, rightDim, branches) <- toIRInference meta cumulative right sample
    (IRVar var_condF_p, condFalseDim) `multP` (rightExpr, rightDim) <&> (\x -> (x, branches)))) -- We need the branches outside of this scope. Append it to the tuple
  let mul2 = bimap (generateLetInExpr binds2) (generateLetInExpr binds2) mul2Raw
  -- If probability of this branch is 0 then set the product to 0 manually. This branch could throw an error multiplied by 0
  let zeroCheck c = IRIf (IROp OpApprox c const0) const0
  let mul1Zeroed = bimap (zeroCheck condTrueExpr) (zeroCheck condTrueExpr) mul1
  let mul2Zeroed = bimap (zeroCheck condFalseExpr) (zeroCheck condFalseExpr) mul2
  (addExpr, addDim) <- mul1Zeroed `addP` mul2Zeroed
  let branches = (IROp OpPlus condTrueBranches ((IROp OpPlus leftBranches rightBranches)))
  case thr of
    Just thresh -> do
      let returnExpr = IRIf
            (IROp OpLessThan (IRVar var_condT_p) (IRConst (VFloat thresh)))
            -- If probability of this branch is 0 then set the product to 0 manually. This branch could throw an error multiplied by 0
            (IRIf (IROp OpApprox condFalseExpr const0) const0 (fst mul2))
            (IRIf (IROp OpGreaterThan (IRVar var_condT_p) (IRConst (VFloat (1-thresh))))
              (IRIf (IROp OpApprox condTrueExpr const0) const0 (fst mul1))
              addExpr)
      let returnDim = IRIf
            (IROp OpLessThan (IRVar var_condT_p) (IRConst (VFloat thresh)))
            (IRIf (IROp OpApprox condFalseExpr const0) const0 (snd mul2))
            (IRIf (IROp OpGreaterThan (IRVar var_condT_p) (IRConst (VFloat (1-thresh))))
              (IRIf (IROp OpApprox condTrueExpr const0) const0 (snd mul1))
              addDim)
      return (returnExpr, returnDim, branches)
    -- p(y) = p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
    Nothing -> do
      return (addExpr, addDim, branches)
toIRInference meta False (GreaterThan (TypeInfo {rType = t, tags = extras}) left right) sample
  | extras `hasAlgorithm` "greaterThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate meta left
    setVariables [(var, l)]
    (integrate, _, integrateBranches) <- toIRInference meta True right (IRVar var)
    var2 <- mkVariable "rhs_integral"
    let returnExpr = IRIf sample (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))  
    setVariables [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | extras `hasAlgorithm` "greaterThanRight" = do --p(x | var >= const)
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate meta right
    setVariables [(var, r)]
    (integrate, _, integrateBranches) <- toIRInference meta True left (IRVar var)
    var2 <- mkVariable "lhs_integral"
    let returnExpr = IRIf sample (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)) (IRVar var2)
    setVariables [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
toIRInference meta False (LessThan (TypeInfo {rType = t, tags = extras}) left right) sample
  | extras `hasAlgorithm` "lessThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate meta left
    setVariables [(var, l)]
    (integrate, _, integrateBranches) <- toIRInference meta True right (IRVar var)
    var2 <- mkVariable "rhs_integral"
    let returnExpr = IRIf sample (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)) (IRVar var2) 
    setVariables [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | extras `hasAlgorithm` "lessThanRight" = do --p(x | var >= const)
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate meta right
    setVariables [(var, r)]
    (integrate, _, integrateBranches) <- toIRInference meta True left (IRVar var)
    var2 <- mkVariable "lhs_integral"
    setVariables [(var2, integrate)]
    let returnExpr = IRIf sample (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))  
    return (returnExpr, const0, integrateBranches)
toIRInference meta cumulative (Not (TypeInfo {rType = TBool}) f) sample =
  toIRInference meta cumulative f (IRUnaryOp OpNot sample)
toIRInference meta cumulative (And (TypeInfo {rType = TBool}) a b) sample = do
  (aP, aDim, aBC) <- toIRInference meta cumulative a (IRConst $ VBool True)
  (bP, bDim, bBC) <- toIRInference meta cumulative b (IRConst $ VBool True)
  (resP, resDim) <- (aP, aDim) `multP` (bP, bDim)
  return $ (IRIf sample resP (IROp OpSub (IRConst $ VFloat 1) resP), resDim, IROp OpPlus aBC bBC)
toIRInference meta cumulative (Or (TypeInfo {rType = TBool}) a b) sample = do
  (aP, aDim, aBC) <- toIRInference meta cumulative a (IRConst $ VBool False)
  (bP, bDim, bBC) <- toIRInference meta cumulative b (IRConst $ VBool False)
  (resP, resDim) <- (aP, aDim) `multP` (bP, bDim)
  return $ (IRIf sample (IROp OpSub (IRConst $ VFloat 1) resP) resP, resDim, IROp OpPlus aBC bBC)  -- p(a || b == True) == 1 - p(a == False) * p(b == False)
toIRInference meta cumulative (ReadNN _ name symbol) sample = do
  -- Same code as for calling a top level function
  var <- mkVariable "callNN"
  sym <- toIRGenerate meta symbol
  setVariables [(var, IRInvoke (IRApply (IRApply (IRVar (name ++ "_auto_prob")) sym) sample))]
  if countBranches (compilerConfig meta) then
    return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
  else
    return (IRTFst (IRVar var), IRTSnd (IRVar var), const0)
toIRInference meta cumulative (Lambda t name subExpr) sample = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      -- Lambda parameter is a function
      let newTypeEnv = (name, (paramRType, True)):typeEnv meta
      irTuple <- lift (runWriterT (toIRInference meta {typeEnv=newTypeEnv} cumulative subExpr sample)) <&> generateLetInBlock meta
      return (IRLambda name irTuple, const0, const0)
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv meta
      irTuple <- lift (runWriterT (toIRInference meta {typeEnv=newTypeEnv} cumulative subExpr sample)) <&> generateLetInBlock meta
      return (IRLambda name irTuple, const0, const0)
-- Deterministic lambda and bound expression PDF
toIRInference meta False (Apply TypeInfo{rType=rt} l v) sample | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  lIR <- toIRGenerate meta l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      retExpr <- indicator (IROp OpEq (IRInvoke (IRApply lIR vIR)) sample)
      return (retExpr, const0, const0)
-- Deterministic lambda and bound expression CDF
toIRInference meta True (Apply TypeInfo{rType=rt} l v) sample | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  lIR <- toIRGenerate meta l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      return (compareValueExpr rt (IRInvoke $ IRApply lIR vIR) sample, const0, const0)
-- Deterministic bound expression
toIRInference meta cumulative (Apply TypeInfo{rType=rt} l v) sample | pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  (lIR, _, _) <- toIRInference meta cumulative l sample -- Dim and BC are irrelevant here. We need to extract these from the return tuple
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      retVal <- mkVariable "call"
      setVariables [(retVal, IRInvoke (IRApply lIR vIR))]
      if countBranches (compilerConfig meta) then
        return (IRTFst (IRVar retVal), IRTFst (IRTSnd (IRVar retVal)), IRTSnd (IRTSnd (IRVar retVal)))
      else
        return (IRTFst (IRVar retVal), IRTSnd (IRVar retVal), const0)
-- Probabilistic bound expression
toIRInference meta cumulative (Apply TypeInfo{rType=rt, chainName=aChainName} l v) sample | isTArrow (rType(getTypeInfo v)) && (pType (getTypeInfo v) == Prob || pType (getTypeInfo v) == Integrate) = do
  lIR <- toIRGenerate meta l
  (vIR, _, _) <- toIRInference meta cumulative v sample
  applied <- mkVariable "call"
  setVariables [(applied, IRInvoke $ IRApply lIR vIR)]
  if countBranches (compilerConfig meta) then
    return (IRTFst (IRVar applied), IRTFst (IRTSnd (IRVar applied)), IRTSnd (IRTSnd (IRVar applied)))
  else
    return (IRTFst (IRVar applied), IRTSnd (IRVar applied), const0)
  where 
    isTArrow (TArrow _ _) = True
    isTArrow _ = False
toIRInference meta cumulative (Apply TypeInfo{rType=rt, chainName=aChainName} l v) sample | pType (getTypeInfo v) == Prob || pType (getTypeInfo v) == Integrate = do
  -- This is the probabilistic inference of a known, deterministic lambda with a probabilistic parameter
  -- The inference looks like this: p(l(v) == sample) = p(l^-1(sample) == v)
  -- The inverse can not be created using recursive descend, therefor we use forward chaining for the inverse only
  -- Chain name of the callable
  let clauses = fcData meta
  let adts = adtDecls meta
  let lChainName = chainName (getTypeInfo l)
  -- The FC algorith uses the body of the lambda as a starting point. This is no problem, because the body of the lamdbda is always equivalent to this apply
  let (LambdaInfo _ lBodyCN, _) = findEquivalentLambda (fcData meta) lChainName
  
  -- This logic is here to wrap the expression back into lambdas if the lambda we look at returns a lambda
  let (LambdaInfo toInvCN lambdaBodyCN, tag) = findEquivalentLambda (fcData meta) lChainName
  let (boundVar, lambdaVars) = unwrapLambdas (fcData meta) lambdaBodyCN
  let wrapInLambdas ex = foldr IRLambda ex lambdaVars

  -- Inverse of the callable as a lambda
  let (invExprP, invExprCoV) = toInvExpr clauses adts lChainName
  let appliedCoV = IRInvoke $ IRApply (IRLambda (boundVar ++ tag) invExprCoV) sample
  let lInv = IRLambda (boundVar ++ tag) invExprP
  -- Apply the sample to the inverse
  let appliedSample = IRInvoke (IRApply lInv sample)
  -- Do probabilistic inference using the applied inverse
  (p, dim, bc) <- toIRInference meta cumulative v appliedSample

  let scale x = if not cumulative 
                  then IROp OpMult x (IRIf (IROp OpEq dim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs appliedCoV)) 
                  else IRIf (IROp OpGreaterThan appliedCoV const0) x (IROp OpSub (IRConst (VFloat 1)) x)
  case rt of
    TArrow _ _ -> return (if countBranches (compilerConfig meta) then wrapInLambdas (IRTCons (scale p) (IRTCons dim bc)) else wrapInLambdas (IRTCons (scale p) dim), const0, const0)
    _ -> return (wrapInLambdas $ scale p, wrapInLambdas dim, wrapInLambdas bc)
  -- Forward chaining may have messed with the structure of the expression. We may have too many or too few lambdas.
  -- Every lambda, which is not applied, inside of the callable should be present in the retuned IRExpr. 
  -- Exclude the lambda, which is applied here and all lambdas, which are already present
  {-let Just lBound = findBoundVariable clauses lChainName
  let freeVars = (getUnappliedLambdas clauses lChainName \\ [lBound]) \\ findLambdaVars p
  let wrapInLambdas ex = foldr IRLambda ex freeVars
  -- If the parameter is a lambda, the return value here is a lambda.
  -- We find the bound variable in the program and apply its value here
  let (retP, retD, retBC) = case rType (getTypeInfo v) of
        TArrow _ _ -> do
          let ret = IRInvoke (applyLambdas clauses adts p)
          if countBranches (compilerConfig meta) then 
            (IRTFst ret, IRTFst (IRTSnd ret), IRTFst (IRTSnd ret)) 
          else 
            (IRTFst ret, IRTSnd ret, const0)
        _ -> (p, d, bc)
  -- If the result is a function, we must wrap the return into a tuple
  case rt of
    TArrow _ _ -> return (wrapInLambdas (if countBranches (compilerConfig meta) then IRTCons retP (IRTCons retD retBC) else IRTCons retP retD), const0, const0)
    _ -> return (wrapInLambdas retP, wrapInLambdas retD, wrapInLambdas retBC)-}
  
toIRInference meta cumulative (Apply TypeInfo{rType=rt} l v) sample = error "This instance of apply is not yet implemented"
toIRInference meta cumulative (Cons _ hdExpr tlExpr) sample = do
  headTuple <- lift (runWriterT (toIRInferenceSave meta cumulative hdExpr (IRHead sample))) <&> generateLetInBlock meta
  tailTuple <- lift (runWriterT (toIRInferenceSave meta cumulative tlExpr (IRTail sample))) <&> generateLetInBlock meta
  let dim = if countBranches (compilerConfig meta) then IRTFst . IRTSnd else IRTSnd
  mult <- (IRTFst headTuple, dim headTuple)  `multP` (IRTFst tailTuple, dim tailTuple)
  return (IRIf (IROp OpEq sample (IRConst $ VList EmptyList)) (IRConst $ VFloat 0) (fst mult), IRIf (IROp OpEq sample (IRConst $ VList EmptyList)) (IRConst $ VFloat 0) (snd mult), IRIf (IROp OpEq sample (IRConst $ VList EmptyList)) (IRConst $ VFloat 0) (IROp OpPlus (IRTSnd (IRTSnd headTuple)) (IRTSnd (IRTSnd tailTuple))))
  --return (IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (fst mult), IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (snd mult), IROp OpPlus headBranches tailBranches)
toIRInference meta cumulative (TCons _ t1Expr t2Expr) sample = do
  (t1P, t1Dim, t1Branches) <- toIRInferenceSave meta cumulative t1Expr (IRTFst sample)
  (t2P, t2Dim, t2Branches) <- toIRInferenceSave meta cumulative t2Expr (IRTSnd sample)
  mult <- (t1P, t1Dim) `multP` (t2P, t2Dim)
  return (fst mult, snd mult, IROp OpPlus t1Branches t2Branches)
toIRInference meta False (InjF TypeInfo {tags=extras} name [left, right]) sample
  | extras `hasAlgorithm` "injF2Enumerable" = do
  -- Get all possible values for subexpressions
  let extrasLeft = tags $ getTypeInfo left
  let extrasRight = tags $ getTypeInfo right
  let enumListL = head $ [x | EnumList x <- extrasLeft]
  let enumListR = head $ [x | EnumList x <- extrasRight]

  fPair <- instantiate mkVariable (adtDecls meta) name -- FPair of the InjF with unique names
  let FPair fwd inversions = fPair
  let FDecl {inputVars=[v2, v3], outputVars=[v1]} = fwd
  -- We get the inversion to the right side
  let [invDecl] = filter (\(FDecl {outputVars=[w1]}) -> v3==w1) inversions   --This should only return one inversion
  let FDecl {inputVars=[x2, x3], body=invExpr} = invDecl

  -- We now compute
  -- for each e in leftEnum:
  --   sum += if invExpr(e, sample) in rightEnum then pLeft(e) * pRight(sample - e) else 0
  -- For that we name e like the lhs of
  -- We need to unfold the monad stack, because the EnumSum Works like a lambda expression and has a local scope
  irTuple <- lift (runWriterT (do
    -- the subexpr in the loop must compute p(enumVar| left) * p(inverse | right)
    setVariables [(x3, sample)]
    (pLeft, _, _) <- toIRInference meta False left (IRVar x2)
    (pRight, _, _) <- toIRInference meta False right invExpr
    
    let returnExpr = case topKThreshold (compilerConfig meta) of
          Nothing -> IRIf (IRElementOf invExpr (IRConst (fmap failConversion (constructVList enumListR)))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
          Just thr -> IRIf (IROp OpAnd (IRElementOf invExpr (IRConst (fmap failConversion (constructVList enumListR)))) (IROp OpGreaterThan pLeft (IRConst (VFloat thr)))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
    let branchesExpr = case topKThreshold (compilerConfig meta) of
          Nothing -> IRIf (IRElementOf invExpr (IRConst (fmap failConversion (constructVList enumListR)))) (IRConst (VFloat 1)) (IRConst (VFloat 0))
          Just thr -> IRIf (IROp OpAnd (IRElementOf invExpr (IRConst (fmap failConversion (constructVList enumListR)))) (IROp OpGreaterThan pLeft (IRConst (VFloat thr)))) (IRConst (VFloat 1)) (IRConst (VFloat 0))
    return (returnExpr, const0, branchesExpr)
    )) <&> generateLetInBlock meta
  uniquePrefix <- mkVariable ""
  let enumSumExpr = IREnumSum x2 (fmap failConversion (constructVList enumListL)) $ IRTFst irTuple
  let branchCountSum = IREnumSum x2 (fmap failConversion (constructVList enumListL)) $ IRTSnd (IRTSnd irTuple)
  return (irMap (uniqueify [x2, x3] uniquePrefix) enumSumExpr, const0, irMap (uniqueify [x2, x3] uniquePrefix) branchCountSum)
-- For the cumulative case we cant get around two enum sums
toIRInference meta True (InjF TypeInfo {tags=extras} name [left, right]) sample
  | extras `hasAlgorithm` "injF2Enumerable" = do
  -- Get all possible values for subexpressions
  let extrasLeft = tags $ getTypeInfo left
  let extrasRight = tags $ getTypeInfo right
  let enumListL = head $ [x | EnumList x <- extrasLeft]
  let enumListR = head $ [x | EnumList x <- extrasRight]

  fPair <- instantiate mkVariable (adtDecls meta) name -- FPair of the InjF with unique names
  let FPair fwd _ = fPair
  let FDecl {inputVars=[v1, v2], body=f} = fwd
  (irTuple, _, _) <- do
    (pLeft, _, _) <- toIRInference meta False left (IRVar v1)
    (pRight, _, _) <- toIRInference meta False right (IRVar v2)
    let returnExpr = IRIf (IROp OpLessThan sample f) (IRConst (VFloat 0)) (IROp OpMult pLeft pRight)
    return (returnExpr, const0, const0)
  return (IREnumSum v1 (fmap failConversion (constructVList enumListL)) $ IREnumSum v2 (fmap failConversion (constructVList enumListR)) irTuple, const0, const0)
toIRInference meta cumulative (InjF _ name params) sample | isHigherOrder (adtDecls meta) name = do
  let adts = adtDecls meta
  -- FPair of the InjF with unique names
  fPair <- instantiate mkVariable adts name
  -- Unary InjF has a single inversion
  let FPair _ [inv] = fPair
  let FDecl {inputVars=inVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=derivs} = inv
  --Handle the function being in different positions of the signature
  let aPoss = [0 .. (length params - 1)] \\ getFunctionParamIdx adts name
  let aPos = case aPoss of
        [n] -> n
        x -> error $ "Expected exectly one non-ho parameter, but got " ++ show (length x)
  let a = params !! aPos
  let aVar = inVars !! aPos
  let fs = map (params !!) (getFunctionParamIdx adts name)
  let fVars = map (inVars !!) (getFunctionParamIdx adts name)
  let Just invDerivExpr = lookup aVar derivs
  -- Set sample value to the variable name in the InjF
  setVariables [(aVar, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Create all inverses of the ho functions and save them on the variable stack
  -- Then create a substitution that substitutes f^-1 to f_prob. All substitutions are then composed in the fold
  renVar <- foldM (\sub tup -> createHOInverse (fcData meta) adts tup <&> (.) sub) id (zip fVars fs)
  (paramExpr, paramDim, paramBranches) <- probF meta cumulative a invExpr
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula
  let scale x = if not cumulative 
                  then IROp OpMult x (IRIf (IROp OpEq paramDim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs invDerivExpr)) 
                  else IRIf (IROp OpGreaterThan invDerivExpr (const0)) x (IROp OpSub (IRConst (VFloat 1)) x)
  let returnP = scale paramExpr
  let appTestExpr e = IRIf appTest e const0
  return (renVar (appTestExpr returnP), renVar (appTestExpr paramDim), renVar (appTestExpr paramBranches))
toIRInference meta False e@(InjF TypeInfo {tags=extras, rType=rt} name params) sample
  | isNothing (getProbIndex params) = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is equal to the sample
  expr <- toIRGenerate meta e
  let cmp = case rt of
        TFloat -> OpApprox
        _ -> OpEq
  retExpr <- indicator $ IROp cmp expr sample
  return (retExpr, const0, const0)
toIRInference meta True e@(InjF TypeInfo {tags=extras, rType=rt} name params) sample
  | isNothing (getProbIndex params) = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is less than the sample
  expr <- toIRGenerate meta e
  return (compareValueExpr rt expr sample, const0, const0)
toIRInference meta cumulative e@(InjF TypeInfo {tags=extras} name params) sample
  | isJust (getProbIndex params) = do
  -- FPair of the InjF with unique names
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) name
  let FDecl{inputVars=inVars, outputVars=[v1]} = fwd
  -- Index of the deterministic and the probabilistic parameter (Left -> 0, Right -> 1)
  let Just probIdx = getProbIndex params
  let detIdxs = [0..length params - 1] \\ [probIdx]
  -- Find the inversion with all deterministic input parameters
  let [invDecl] = filter (\FDecl {outputVars=[w1]} -> (inVars !! probIdx)==w1) inversions   --This should only return one inversion
  let FDecl {inputVars=invVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=invDerivs} = invDecl
  -- All deterministic variable names
  let detVars = filter (v1 /=) invVars
  let detEs = map (params !!) detIdxs

  -- Find the relevant derivative of the inversion
  let Just invDeriv = lookup v1 invDerivs
  -- Generate the probabilistic sub expressions
  mapM_ (\(eVar, e) -> toIRGenerate meta e >>= \x -> setVariables [(eVar, x)]) (zip detVars detEs)
  setVariables [(v1, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Get the probabilistic inference expression of the non-deterministic subexpression
  (paramExpr, paramDim, paramBranches) <- probF meta cumulative (params !! probIdx) invExpr
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula if dim > 0
  let scale x = if not cumulative 
                  then IROp OpMult x (IRIf (IROp OpEq paramDim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs invDeriv)) 
                  else IRIf (IROp OpGreaterThan invDeriv (const0)) x (IROp OpSub (IRConst (VFloat 1)) x)
  let returnP = scale paramExpr  
  let appTestExpr e = IRIf appTest e const0
  return (appTestExpr returnP, appTestExpr paramDim, appTestExpr paramBranches)
toIRInference meta cumulative (Null _) sample = do
  expr <- indicator (IROp OpEq sample (IRConst $ VList EmptyList))
  return (expr, const0, const0)
toIRInference meta cumulative (Var TypeInfo {rType=rt} n) sample = do
  -- Variable might be a function
  let functionSuffix = if cumulative then "_integ" else "_prob"
  case lookup n (typeEnv meta) of
    -- Var is a function
    Just(TArrow _ _, hasInference) -> do
      var <- mkVariable "call"
      let name = if hasInference then n ++ functionSuffix else n
      setVariables [(var, IRApply (IRVar name) sample)]
      -- The return value is still a function. No need to do dim and branch counting here
      return (IRVar var, const0, const0)
    -- var is a function without a inference function
    Just(TArrow _ _, False) -> do
      var <- mkVariable "call"
      setVariables [(var, IRApply (IRVar n) sample)]
      -- The return value is still a function. No need to do dim and branch counting here
      return (IRVar var, const0, const0)
    -- Var is a top level declaration (an therefor has a _prob function)
    Just (_, True) -> do
      var <- mkVariable "call"
      setVariables [(var, IRInvoke (IRApply (IRVar (n ++ functionSuffix)) sample))]
      if countBranches (compilerConfig meta) then
          return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
        else
          return (IRTFst (IRVar var), IRTSnd (IRVar var), const0)
    -- Var is a local variable
    Just (_, False) -> do
      if cumulative then
        return (compareValueExpr rt (IRVar n) sample, const0, const0)
      else do
        let comp = case rt of
              TFloat -> IROp OpApprox sample (IRVar n)
              _ -> IROp OpEq sample (IRVar n)
        expr <- indicator comp
        return (expr, const0, const0)
    Nothing -> error ("Could not find name in TypeEnv: " ++ n)
toIRInference meta cumulative (Subtree _ a i) sample = error "Cannot infer prob on subtree expression. Please check your syntax"
toIRInference meta cumulative (Error t e) sample = return (IRError e, const0, const0)
toIRInference meta cumulative x sample = error ("found no way to convert to IR: " ++ show x)

multP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
multP (aM, aDim) (bM, bDim) = return (IROp OpMult aM bM, IROp OpPlus aDim bDim)

addP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
addP (aM, aDim) (bM, bDim) = do
  pVarA <- mkVariable "pA"
  pVarB <- mkVariable "pB"
  dimVarA <- mkVariable "dimA"
  dimVarB <- mkVariable "dimB"
  setVariables [(pVarA, aM), (pVarB, bM), (dimVarA, aDim), (dimVarB, bDim)]
  return (IRIf (IROp OpApprox (IRVar pVarA) (IRConst (VFloat 0))) (IRVar pVarB)
           (IRIf (IROp OpApprox (IRVar pVarB) (IRConst (VFloat 0))) (IRVar pVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar pVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar pVarB)
           (IROp OpPlus (IRVar pVarA) (IRVar pVarB))))),
           -- Dim
           IRIf (IROp OpApprox (IRVar pVarA) (IRConst (VFloat 0))) (IRVar dimVarB)
           (IRIf (IROp OpApprox (IRVar pVarB) (IRConst (VFloat 0))) (IRVar dimVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar dimVarA)
           (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar dimVarB)
           (IRVar dimVarA)))))

subP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
subP (aM, aDim) (bM, bDim) = do
  pVarA <- mkVariable "pA"
  pVarB <- mkVariable "pB"
  dimVarA <- mkVariable "dimA"
  dimVarB <- mkVariable "dimB"
  setVariables [(pVarA, aM), (pVarB, bM), (dimVarA, aDim), (dimVarB, bDim)]
  return (IRIf (IROp OpApprox (IRVar pVarA) (IRConst (VFloat 0))) (IRVar pVarB)
         (IRIf (IROp OpApprox (IRVar pVarB) (IRConst (VFloat 0))) (IRVar pVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar pVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar pVarB)
         (IROp OpSub (IRVar pVarA) (IRVar pVarB))))),
         -- Dim
         IRIf (IROp OpApprox (IRVar pVarA) (IRConst (VFloat 0))) (IRVar dimVarB)
         (IRIf (IROp OpApprox (IRVar pVarB) (IRConst (VFloat 0))) (IRVar dimVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar dimVarA)
         (IRIf (IROp OpLessThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar dimVarB)
         (IRVar dimVarA)))))

createHOInverse :: FCData -> [ADTDecl]-> (String, Expr) -> CompilerMonad (IRExpr -> IRExpr)
createHOInverse fcData adts (fVar, f) = do
  let (inverseF, inverseCoV) = toInvExpr fcData adts (chainName $ getTypeInfo f)
  let (LambdaInfo _ lBodyChainName, tag) = findEquivalentLambda fcData (chainName $ getTypeInfo f)
  let inverseLambdaProb = IRLambda (lBodyChainName ++ tag) inverseF
  let inverseLambdaCoV = IRLambda (lBodyChainName ++ tag) inverseCoV
  -- Rename all occurances of f^-1 from the definition to f_prob
  let renVar = renameVar (fVar ++ "^-1") (fVar ++ "_prob")
  let renDeriv = renameVar (fVar ++ "^-1'") (fVar ++ "_prob_deriv")
  setVariables [(fVar ++ "_prob", inverseLambdaProb), (fVar ++ "_prob_deriv", inverseLambdaCoV)]
  return (renVar . renDeriv)

getProbIndex :: [Expr] -> Maybe Int
--getProbIndex es | traceShow es False = undefined
getProbIndex es =
  case filter (\(p, _) -> p == Prob || p == Integrate) zipped of
    [(_, i)] -> Just i
    [] -> Nothing
    _ -> error "More than one probabilistic argument found"
  where
    pt x = pType (getTypeInfo x)
    pTypes = map pt es
    zipped = zip pTypes [0..]

compareValueExpr :: RType -> IRExpr -> IRExpr -> IRExpr
compareValueExpr TFloat v sample = IRIf (IROp OpLessThan sample v) (IRConst $ VFloat 0) (IRConst $ VFloat 1)
compareValueExpr TInt v sample = IRIf (IROp OpLessThan sample v) (IRConst $ VFloat 0) (IRConst $ VFloat 1)
compareValueExpr (Tuple ft st) v sample = IROp OpMult (compareValueExpr ft (IRTFst v) (IRTFst sample)) (compareValueExpr st (IRTSnd v) (IRTSnd sample))
compareValueExpr (TEither lr rr) v sample =
  IRIf (IRIsLeft v)
    (IRIf (IRIsLeft sample) (compareValueExpr lr (IRFromLeft v) (IRFromLeft sample)) (IRConst $ VFloat 0))
    (IRIf (IRIsRight sample) (compareValueExpr rr (IRFromRight v) (IRFromRight sample)) (IRConst $ VFloat 0))
compareValueExpr (TVarR _) v sample = IRIf (IROp OpLessThan sample v) (IRConst $ VFloat 0) (IRConst $ VFloat 1)
compareValueExpr (TADT _) _ _= IRError "Not yet implemented" -- TODO implement for ADTs
compareValueExpr rt _ _ = error $ "Comparison not implemented for type: " ++ show rt
  


packParamsIntoLetinsProb :: [String] -> [Expr] -> IRExpr -> IRExpr -> Supply IRExpr
--packParamsIntoLetinsProb [] [] expr _ = do
--  return expr
--packParamsIntoLetinsProb [] _ _ _ = error "More parameters than variables"
--packParamsIntoLetinsProb _ [] _ _ = error "More variables than parameters"
--packParamsIntoLetinsProb (v:vars) (p:params) expr sample = do
--  e <- packParamsIntoLetinsProb vars params expr sample
--  return $ IRLetIn v sample e --TODO sample austauschen durch teil von sample falls multivariable
packParamsIntoLetinsProb [v] [p] expr sample = do
  return $ IRLetIn v sample expr    --FIXME sample to auch toIRProbt werden

findLambdaVars :: IRExpr -> [String]
findLambdaVars (IRLambda n expr) = n:findLambdaVars expr
findLambdaVars expr = concatMap findLambdaVars (getIRSubExprs expr)
  

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
toIRGenerate :: CompilerMetadata -> Expr -> CompilerMonad  IRExpr
toIRGenerate meta (IfThenElse _ cond left right) = do
  c <- toIRGenerate meta cond
  l <- toIRGenerate meta left
  r <- toIRGenerate meta right
  return $ IRIf c l r
toIRGenerate meta (LetIn _ n v b) = do
  v' <- toIRGenerate meta v
  b' <- toIRGenerate meta b
  return $ IRLetIn n v' b'
toIRGenerate meta (GreaterThan _ left right) = do
  l <- toIRGenerate meta left
  r <- toIRGenerate meta right
  return $ IROp OpGreaterThan l r
toIRGenerate meta (LessThan _ left right) = do
  l <- toIRGenerate meta left
  r <- toIRGenerate meta right
  return $ IROp OpLessThan l r
toIRGenerate meta (Not _ f) = do
  f' <- toIRGenerate meta f
  return $ IRUnaryOp OpNot f'
toIRGenerate meta (And _ a b) = do
  a' <- toIRGenerate meta a
  b' <- toIRGenerate meta b
  return $ IROp OpAnd a' b'
toIRGenerate meta (Or _ a b) = do
  a' <- toIRGenerate meta a
  b' <- toIRGenerate meta b
  return $ IROp OpOr a' b'
toIRGenerate meta (ThetaI _ a ix) = do
  a' <- toIRGenerate meta a
  return $ IRTheta a' ix
toIRGenerate meta (Subtree _ a ix) = do
  a' <- toIRGenerate meta a
  return $ IRSubtree a' ix
toIRGenerate meta (Constant _ x) = return (IRConst (fmap failConversion x))
toIRGenerate meta (Null _) = return $ IRConst (VList EmptyList)
toIRGenerate meta (Cons _ hd tl) = do
  h <- toIRGenerate meta hd
  t <- toIRGenerate meta tl
  return $ IRCons h t
toIRGenerate meta (TCons _ t1 t2) = do
  t1' <- toIRGenerate meta t1
  t2' <- toIRGenerate meta t2
  return $ IRTCons t1' t2'
toIRGenerate meta (Uniform _) = return $ IRSample IRUniform
toIRGenerate meta (Normal _) = return $ IRSample IRNormal
toIRGenerate meta (InjF _ name params) = do
  -- Assuming that the logic within packParamsIntoLetinsGen typeEnv is correct.
  -- You will need to process vars and params, followed by recursive calls to fwdExpr.
  fPair <- instantiate mkVariable (adtDecls meta) name
  let FPair fwd _ = fPair
  let FDecl {inputVars=vars, body=fwdExpr} = fwd
  prefix <- mkVariable ""
  letInBlock <- packParamsIntoLetinsGen meta vars params fwdExpr
  return $ irMap (uniqueify vars prefix) letInBlock
  where
    Just fPair = lookup name (globalFEnv (adtDecls meta))
    FPair fwd _ = fPair
    FDecl {inputVars=vars, body=fwdExpr} = fwd
toIRGenerate meta (Var _ name) = do
  case lookup name (typeEnv meta) of
    -- Var is a function
    Just (TArrow _ _, hasInference) ->
      let fullName = if hasInference then name ++ "_gen" else name in
        return $ IRVar fullName
    -- Var is a top level declaration (an therefor has a _gen function)
    Just (_, True) -> do
      return $ IRInvoke (IRVar (name ++ "_gen"))
    -- Var is a local variable
    Just (_, False) -> do
      return $ IRVar name
    Nothing -> error ("Could not find name in TypeEnv: " ++ name)
toIRGenerate meta (Lambda t name subExpr) = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      let newTypeEnv = (name, (paramRType, True)):typeEnv meta
      irTuple <- toIRGenerate meta{typeEnv=newTypeEnv} subExpr
      return $ IRLambda name irTuple
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv meta
      irTuple <- toIRGenerate meta{typeEnv=newTypeEnv} subExpr
      return $ IRLambda name irTuple
toIRGenerate meta (Apply TypeInfo {rType=rt} l v) = do
  l' <- toIRGenerate meta l
  v' <- toIRGenerate meta v
  case rt of
    TArrow _ _ -> return $ IRApply l' v'
    _ -> return $ IRInvoke $ IRApply l' v'
toIRGenerate meta (ReadNN _ name subexpr) = do
  sub <- toIRGenerate meta subexpr
  return $ IRInvoke (IRApply (IRVar (name ++ "_auto_gen")) sub)
toIRGenerate meta (Error _ e) = return $ IRError e
toIRGenerate meta x = error ("found no way to convert to IRGen: " ++ show x)


packParamsIntoLetinsGen :: CompilerMetadata -> [String] -> [Expr] -> IRExpr -> CompilerMonad  IRExpr
packParamsIntoLetinsGen meta [] [] expr = return $ expr
packParamsIntoLetinsGen meta [] _ _ = error "More parameters than variables"
packParamsIntoLetinsGen meta _ [] _ = error "More variables than parameters"
packParamsIntoLetinsGen meta (v:vars) (p:params) expr = do
  pExpr <- toIRGenerate meta p
  e <- packParamsIntoLetinsGen meta vars params expr
  return $ IRLetIn v pExpr e
{-
--Adds an additional check that the bounds are not equal
--We need this bounds check only once, because no invertible transformation can make the bounds be equal when they were not
--TODO: Some InjF could lead to CoV, which would make the bounds check at the to wrong
toIRIntegrateSave :: CompilerMetadata -> Expr -> IRExpr -> IRExpr -> CompilerMonad CompilationResult
toIRIntegrateSave conf clauses typeEnv adts (Lambda t name subExpr) low high = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      let newTypeEnv = (name, (paramRType, True)):typeEnv
      irTuple <- lift (runWriterT (toIRIntegrateSave conf clauses newTypeEnv adts subExpr low high)) <&> generateLetInBlock conf
      return (IRLambda name irTuple, const0, const0)
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv
      irTuple <- lift (runWriterT (toIRIntegrateSave conf clauses newTypeEnv adts subExpr low high)) <&> generateLetInBlock conf
      return (IRLambda name irTuple, const0, const0)
toIRIntegrateSave conf clauses typeEnv adts expr lower higher = do
  (prob, probDim, probBC) <- toIRInference meta cumulative expr lower
  (integ, integDim, integBC) <- toIRIntegrate meta expr lower higher
  let eqCheck = IRIf (IROp OpEq lower higher)
  let anyCheck = IRIf (IROp OpAnd (IRUnaryOp OpIsAny lower) (IRUnaryOp OpIsAny higher))
  return (anyCheck (IRConst $ VFloat 1) (eqCheck prob integ), anyCheck (IRConst $ VFloat 0) (eqCheck probDim integDim), anyCheck (IRConst $ VFloat 0) (eqCheck probBC integBC))


toIRIntegrate :: CompilerMetadata -> Expr -> IRExpr -> IRExpr -> CompilerMonad CompilationResult
toIRIntegrate meta expr@(Uniform _) lower higher = do
  (density, _, _) <- toIRInference meta cumulative expr lower
  --let expr = IRIf (IROp OpEq lower higher) density (IROp OpSub (IRCumulative IRUniform higher) (IRCumulative IRUniform lower))
  let expr = (IROp OpSub (IRCumulative IRUniform higher) (IRCumulative IRUniform lower))
  return (expr, IRIf (IROp OpEq lower higher) (IRConst $ VFloat 1) const0, const0)
toIRIntegrate meta expr@(Normal _) lower higher = do
  (density, _, _) <- toIRInference meta cumulative expr lower
  --let expr = IRIf (IROp OpEq lower higher) density (IROp OpSub (IRCumulative IRNormal higher) (IRCumulative IRNormal lower))
  let expr = (IROp OpSub (IRCumulative IRNormal higher) (IRCumulative IRNormal lower))
  return (expr, IRIf (IROp OpEq lower higher) (IRConst $ VFloat 1) const0, const0)
toIRIntegrate meta (TCons _ t1Expr t2Expr) low high = do
  (t1P, t1Dim,  t1Branches) <- toIRIntegrateSave conf clauses typeEnv adts t1Expr (IRTFst low) (IRTFst high)
  (t2P, t2Dim,  t2Branches) <- toIRIntegrateSave conf clauses typeEnv adts t2Expr (IRTSnd low) (IRTSnd high)
  (productP, productDim) <- (t1P, t1Dim) `multP` (t2P, t2Dim)
  return (productP, productDim, IROp OpPlus t1Branches t2Branches)
toIRIntegrate meta (IfThenElse _ cond left right) low high = do
  var_cond_p <- mkVariable "cond"
  (condExpr, _, condBranches) <- toIRInference meta cumulative cond (IRConst (VBool True))
  (leftExpr, _, leftBranches) <- toIRIntegrate meta left low high
  (rightExpr, _, rightBranches) <- toIRIntegrate meta right low high
  let thr = topKThreshold conf
  case thr of
    Just thresh -> do
        setVariables [(var_cond_p, condExpr)]
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
        setVariables [(var_cond_p, condExpr)]
        return
          (IROp OpPlus
            (IROp OpMult (IRVar var_cond_p) leftExpr)
            (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr), const0, IROp OpPlus condBranches (IROp OpPlus leftBranches rightBranches) )
toIRIntegrate meta (Cons _ hdExpr tlExpr) low high = do
  headTuple <- lift (runWriterT (toIRIntegrateSave conf clauses typeEnv adts hdExpr (IRHead low) (IRHead high))) <&> generateLetInBlock conf
  tailTuple <- lift (runWriterT (toIRIntegrateSave conf clauses typeEnv adts tlExpr (IRTail low) (IRTail high))) <&> generateLetInBlock conf
  let dim = if countBranches (compilerConfig meta) then IRTFst . IRTSnd else IRTSnd
  (multP, multDim) <- (IRTFst headTuple, dim headTuple)  `multP` (IRTFst tailTuple, dim tailTuple)
  return (IRIf (IROp OpOr (IROp OpEq low (IRConst $ VList EmptyList)) (IROp OpEq high (IRConst $ VList EmptyList))) (IRConst $ VFloat 0) multP, multDim, IROp OpPlus (IRTSnd (IRTSnd headTuple)) (IRTSnd (IRTSnd tailTuple)))
toIRIntegrate meta (Null _) low high = do
  ind <- indicator (IROp OpAnd (IROp OpEq low (IRConst $ VList EmptyList)) (IROp OpEq high (IRConst $ VList EmptyList)))
  return (ind, const0, const0)
toIRIntegrate meta (Constant _ value) low high = do
  ind <- indicator (IROp OpAnd (IROp OpLessThan low (IRConst (fmap failConversion value))) (IROp OpGreaterThan high (IRConst (fmap failConversion value)))) --TODO What to do if low and high are equal?
  return (ind, const0, const0)
toIRIntegrate meta (ThetaI _ a i) low high = do
  a' <-  toIRGenerate meta a
  let val = IRTheta a' i
  ind <- indicator (IROp OpAnd (IROp OpLessThan low val) (IROp OpGreaterThan high val)) --TODO What to do if low and high are equal?
  return (ind, const0, const0)
toIRIntegrate meta (InjF _ name params) low high | isHigherOrder adts name = do
  -- FPair of the InjF with unique names
  fPair <- instantiate mkVariable adts name
  -- Unary InjF has a single inversion
  let FPair _ [inv] = fPair
  let FDecl {inputVars=inVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=derivs} = inv
  --Handle the function being in different positions of the signature
  let aPoss = [0 .. (length params - 1)] \\ getFunctionParamIdx adts name
  let aPos = case aPoss of
        [n] -> n
        x -> error $ "Expected exectly one non-ho parameter, but got " ++ show (length x)
  let a = params !! aPos
  let aVar = inVars !! aPos
  let fs = map (params !!) (getFunctionParamIdx adts name)
  let fVars = map (inVars !!) (getFunctionParamIdx adts name)
  let Just invDerivExpr = lookup aVar derivs
  -- Set sample value to the variable name in the InjF
  let letInBlockLow = IRLetIn aVar low invExpr
  let letInBlockHigh = IRLetIn aVar high invExpr
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let integF = if decons then toIRIntegrateSave else toIRIntegrate
  -- Create all inverses of the ho functions and save them on the variable stack
  -- Then create a substitution that substitutes f^-1 to f_prob. All substitutions are then composed in the fold
  renVar <- foldM (\sub tup -> createHOInverse clauses adts tup <&> (.) sub) id (zip fVars fs)
  (paramExpr, paramDim, paramBranches) <- integF conf clauses typeEnv adts a letInBlockLow letInBlockHigh
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula
  let returnP = IROp OpMult paramExpr (IRUnaryOp OpSign invDerivExpr)
  let appTestExpr e = IRIf appTest e const0
  return (renVar (appTestExpr returnP), const0, renVar (appTestExpr paramBranches))
toIRIntegrate meta (InjF _ name [param]) low high = do
  -- FPair of the InjF with unique names
  fPair <- instantiate mkVariable adts name
  -- Unary InjF has a single inversion
  let FPair _ [inv] = fPair
  let FDecl {inputVars=[v], body=invExpr, applicability=appTest, deconstructing=decons, derivatives=[(_, invDerivExpr)]} = inv
  -- Set sample value to the variable name in the InjF
  let letInBlockLow = IRLetIn v low invExpr
  let letInBlockHigh = IRLetIn v high invExpr
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let integF = if decons then toIRIntegrateSave else toIRIntegrate
  -- Get the probabilistic inference code for the parameter
  (paramExpr, paramDim, paramBranches) <- integF conf clauses typeEnv adts param letInBlockLow letInBlockHigh
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula
  let returnP = IROp OpMult paramExpr (IRUnaryOp OpSign invDerivExpr)
  let appTestExpr e = IRIf appTest e const0
  return (appTestExpr returnP, const0, appTestExpr paramBranches)
toIRIntegrate meta e@(InjF TypeInfo {tags=extras, rType=rt} name params) low high
  | isNothing (getProbIndex params) = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is equal to the sample
  expr <- toIRGenerate meta e
  retExpr <- indicator $ IROp OpAnd (IROp OpLessThan low expr) (IROp OpGreaterThan high expr)
  return (retExpr, const0, const0)
toIRIntegrate meta (InjF TypeInfo {tags=extras} name params) low high
  | isJust (getProbIndex params) = do
  -- FPair of the InjF with unique names
  FPair fwd inversions <- instantiate mkVariable adts name
  let FDecl{inputVars=inVars, outputVars=[v1]} = fwd
  -- Index of the deterministic and the probabilistic parameter (Left -> 0, Right -> 1)
  let Just probIdx = getProbIndex params
  let detIdxs = [0..length params - 1] \\ [probIdx]
  -- Find the inversion with all deterministic input parameters
  let [invDecl] = filter (\FDecl {outputVars=[w1]} -> (inVars !! probIdx)==w1) inversions   --This should only return one inversion
  let FDecl {inputVars=invVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=invDerivs} = invDecl
  -- All deterministic variable names
  let detVars = filter (v1 /=) invVars
  let detEs = map (params !!) detIdxs

  -- Find the relevant derivative of the inversion
  let Just invDeriv = lookup v1 invDerivs
  -- Generate the probabilistic sub expressions
  mapM_ (\(eVar, e) -> toIRGenerate meta e >>= \x -> setVariables [(eVar, x)]) (zip detVars detEs)
  let letInBlockLow = IRLetIn v1 low invExpr
  let letInBlockHigh = IRLetIn v1 high invExpr
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let integF = if decons then toIRIntegrateSave else toIRIntegrate
  -- Get the probabilistic inference expression of the non-deterministic subexpression
  (paramExpr, paramDim, paramBranches) <- integF conf clauses typeEnv adts (params !! probIdx) letInBlockLow letInBlockHigh
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula if dim > 0
  let returnP = IROp OpMult paramExpr (IRIf (IROp OpEq paramDim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs invDeriv))
  let appTestExpr e = IRIf appTest e const0
  return (appTestExpr returnP, appTestExpr paramDim, appTestExpr paramBranches)
toIRIntegrate meta (Lambda t name subExpr) low high = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      let newTypeEnv = (name, (paramRType, True)):typeEnv
      irTuple <- lift (runWriterT (toIRIntegrate conf clauses newTypeEnv adts subExpr low high)) <&> generateLetInBlock conf
      return (IRLambda name irTuple, const0, const0)
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv
      irTuple <- lift (runWriterT (toIRIntegrate conf clauses newTypeEnv adts subExpr low high)) <&> generateLetInBlock conf
      return (IRLambda name irTuple, const0, const0)
toIRIntegrate meta (Apply TypeInfo{rType=rt} l v) low high | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  lIR <- toIRGenerate meta l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      retExpr <- indicator (IROp OpAnd (IROp OpLessThan (IRInvoke (IRApply lIR vIR)) high) (IROp OpGreaterThan (IRInvoke (IRApply lIR vIR)) low))
      return (retExpr, const0, const0)
toIRIntegrate meta (Apply TypeInfo{rType=rt} l v) low high | pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  (lIR, _, _) <- toIRIntegrate meta l low high -- Dim and BC are irrelevant here. We need to extract these from the return tuple
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      retVal <- mkVariable "call"
      setVariables [(retVal, IRInvoke (IRApply lIR vIR))]
      if countBranches (compilerConfig meta) then
        return (IRTFst (IRVar retVal), IRTFst (IRTSnd (IRVar retVal)), IRTSnd (IRTSnd (IRVar retVal)))
      else
        return (IRTFst (IRVar retVal), IRTSnd (IRVar retVal), const0)

toIRIntegrate meta (Apply TypeInfo{rType=rt} l v) low high | pType (getTypeInfo v) == Integrate = do
  let lChainName = chainName (getTypeInfo l)
  let lInv = IRLambda lChainName (toInvExpr clauses adts lChainName)
  let appliedSampleLow = IRInvoke (IRApply lInv low)
  let appliedSampleHigh = IRInvoke (IRApply lInv high)
  toIRIntegrate meta v appliedSampleLow appliedSampleHigh
toIRIntegrate meta (Apply TypeInfo{rType=rt} l v) low high = error "This instance if apply is not yet implemented"
toIRIntegrate meta (Var _ n) low high = do
  -- Variable might be a function
  case lookup n typeEnv of
   -- Var is a function
   Just(TArrow _ _, hasInference) -> do
     var <- mkVariable "call"
     let name = if hasInference then n ++ "_integ" else n
     setVariables [(var, IRApply (IRApply (IRVar name) low) high)]
     -- The return value is still a function. No need to do dim and branch counting here
     return (IRVar var, const0, const0)
   Just(TArrow _ _, False) -> do
     var <- mkVariable "call"
     setVariables [(var, IRApply (IRApply (IRVar n) low) high)]
     -- The return value is still a function. No need to do dim and branch counting here
     return (IRVar var, const0, const0)
   -- Var is a top level declaration (an therefor has a _prob function)
   Just (_, True) -> do
     var <- mkVariable "call"
     setVariables [(var, IRInvoke (IRApply (IRApply (IRVar (n ++ "_integ")) low) high))]
     if countBranches (compilerConfig meta) then
         return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
       else
         return (IRTFst (IRVar var), IRTSnd (IRVar var), const0)
   -- Var is a local variable
   Just (_, False) -> do
    ind <- indicator (IROp OpAnd (IROp OpLessThan low (IRVar n)) (IROp OpGreaterThan high (IRVar n))) --TODO What to do if low and high are equal?
    return (ind, const0, const0)
   Nothing -> error ("Could not find name in TypeEnv: " ++ n)
toIRIntegrate meta (Error t e) low high = return (IRError e, const0, const0)
toIRIntegrate _ x _ _ = error ("found no way to convert to IRIntegrate: " ++ show x)
-}