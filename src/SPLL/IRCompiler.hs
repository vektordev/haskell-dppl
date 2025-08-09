module SPLL.IRCompiler where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import SPLL.Lang.Types hiding (HornClause)
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
import Data.Functor
import SPLL.Typing.ForwardChaining
import Data.List
import SPLL.Typing.AlgebraicDataTypes

-- SupplyT needs to be a transformer, because Supply does not implement Functor correctly
type CompilerMonad a = WriterT [(String, IRExpr)] (SupplyT Int Identity) a

type CompilationResult = (IRExpr, IRExpr, IRExpr)

-- (name, ((RType of (Var name)), (Has _gen _prop _integ (if applicable) functions)))
type TypeEnv = [(String, (RType, Bool))]

-- perhaps as an explicit lambda in the top of the expression, otherwise we'll get trouble generating code.
-- TODO: How do we deal with top-level lambdas in binding here?
--  TL-Lambdas are presumably to be treated differently than non-TL, at least as far as prob is concerned.
envToIR :: CompilerConfig -> Program -> IREnv
envToIR conf p@Program{adts=adts} = optimizeEnv conf $ IREnv (-- map optimizer over all second elements of the tuples
  map (makeAutoNeural conf) (neurals p) ++
  map (\(name, binding) ->
    let typeEnv = getGlobalTypeEnv p
        pt = pType $ getTypeInfo binding
        rt = rType $ getTypeInfo binding in
      IRFunGroup {groupName=name,
       integFun =
        if (pt == Deterministic || pt == Integrate) && (isOnlyNumbers rt) then
          Just (toIntegDecl name (IRLambda "low" (IRLambda "high" (runCompile conf (toIRIntegrateSave conf clauses typeEnv adts binding (IRVar "low") (IRVar "high"))))))
        else Nothing,
        probFun =
          if pt == Deterministic || pt == Integrate || pt == Prob then
            Just (toProbDecl name (IRLambda "sample" (runCompile conf (toIRProbabilitySave conf clauses typeEnv adts binding (IRVar "sample")))))
          else Nothing,
        genFun = toGenDecl name (fst $ runIdentity $ runSupplyVars $ runWriterT $ toIRGenerate adts typeEnv binding),
        groupDoc="Function group " ++ name}) (functions p)) adts

  where
    toGenDecl name expr = (expr, "Generates a random sample of the " ++ name ++ " function")
    toProbDecl name expr =
      (expr, "Calculates the probability of the sample parameter being returned from the " ++ name ++ "function")
    toIntegDecl name expr = (expr, "Calculates the probability of sample of " ++ name ++ " falling in between the parameters low and high")
    clauses = progToHornClauses p


runCompile :: CompilerConfig -> CompilerMonad CompilationResult -> IRExpr
runCompile conf codeGen = generateLetInBlock conf (runIdentity $ runSupplyVars $ runWriterT $ codeGen)

generateLetInBlock :: CompilerConfig -> (CompilationResult, [(String, IRExpr)]) -> IRExpr
generateLetInBlock conf codeGen =
  case m of
    (IRLambda _ _) -> (foldr (\(var, val) expr  -> IRLetIn var val expr) m binds) --Dont make tuple out of lambdas, as the snd (and thr) element don't contain information anyway
    _ -> if countBranches conf && not (isLambda m) then
            (foldr (\(var, val) expr  -> IRLetIn var val expr) (IRTCons m (IRTCons dim bc)) binds)
          else
            (foldr (\(var, val) expr  -> IRLetIn var val expr) (IRTCons m dim) binds)
  where ((m, dim, bc), binds) = codeGen

-- Return type (name, rType, hasInferenceFunctions)
getGlobalTypeEnv :: Program -> TypeEnv
getGlobalTypeEnv p = funcEnv ++ implicitFuncEnv ++ neuralEnv
  where funcEnv = map (\(name, expr) -> (name, (rType (getTypeInfo expr), True))) (functions p)
        implicitFuncEnv = map (\(name, rt) -> (name, (rt, False))) (implicitFunctionsRTypeProg p)
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

negInf :: IRExpr
negInf = IRConst (VFloat (-9999999))

posInf :: IRExpr
posInf = IRConst (VFloat 9999999)

renameVar :: String -> String -> IRExpr -> IRExpr
renameVar old new = irMap (renameVar' old new)

renameVar' :: String -> String -> IRExpr -> IRExpr
renameVar' old new (IRVar n) | n == old = IRVar new
renameVar' _ _ x = x

toIRProbabilitySave :: CompilerConfig -> [[HornClause]] -> TypeEnv -> [ADTDecl] -> Expr -> IRExpr -> CompilerMonad CompilationResult
toIRProbabilitySave conf clauses typeEnv adts (Lambda t name subExpr) sample = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      let newTypeEnv = (name, (paramRType, True)):typeEnv
      irTuple <- lift (runWriterT (toIRProbabilitySave conf clauses newTypeEnv adts subExpr sample)) <&> generateLetInBlock conf
      return (IRLambda name irTuple, const0, const0)
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv
      irTuple <- lift (runWriterT (toIRProbabilitySave conf clauses newTypeEnv adts subExpr sample)) <&> generateLetInBlock conf
      return (IRLambda name irTuple, const0, const0)
toIRProbabilitySave conf clauses typeEnv adts expr sample = do
  (probExpr, probDim, probBranches) <- toIRProbability conf clauses typeEnv adts expr sample
  return $ (IRIf (IRUnaryOp OpIsAny sample) (IRConst (VFloat 1)) probExpr, IRIf (IRUnaryOp OpIsAny sample) const0 probDim, IRIf (IRUnaryOp OpIsAny sample) const0 probBranches)

--in this implementation, I'll forget about the distinction between PDFs and Probabilities. Might need to fix that later.
toIRProbability :: CompilerConfig -> [[HornClause]] -> TypeEnv -> [ADTDecl] -> Expr -> IRExpr -> CompilerMonad CompilationResult
--toIRProbability conf clauses typeEnv adts expr sample | trace (show expr) False = undefined
toIRProbability conf clauses typeEnv adts (IfThenElse t cond left right) sample = do
  var_condT_p <- mkVariable "condT"
  var_condF_p <- mkVariable "condF"
  (condTrueExpr, condTrueDim, condTrueBranches) <- toIRProbability conf clauses typeEnv adts cond (IRConst (VBool True))
  (condFalseExpr, condFalseDim, condFalseBranches) <- toIRProbability conf clauses typeEnv adts cond (IRConst (VBool False))
  (leftExpr, leftDim, leftBranches) <- toIRProbability conf clauses typeEnv adts left sample
  (rightExpr, rightDim, rightBranches) <- toIRProbability conf clauses typeEnv adts right sample
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
toIRProbability conf clauses typeEnv adts (GreaterThan (TypeInfo {rType = t, tags = extras}) left right) sample
  | extras `hasAlgorithm` "greaterThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate adts typeEnv left
    tell [(var, l)]
    (integrate, _, integrateBranches) <- toIRIntegrate conf clauses typeEnv adts right negInf (IRVar var)
    var2 <- mkVariable "rhs_integral"
    let returnExpr = IRIf sample (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))
    tell [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | extras `hasAlgorithm` "greaterThanRight" = do --p(x | var >= const
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate adts typeEnv right
    tell [(var, r)]
    (integrate, _, integrateBranches) <- toIRIntegrate conf clauses typeEnv adts left negInf (IRVar var)
    var2 <- mkVariable "lhs_integral"
    let returnExpr = IRIf sample (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)) (IRVar var2)
    tell [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
toIRProbability conf clauses typeEnv adts (LessThan (TypeInfo {rType = t, tags = extras}) left right) sample
  | extras `hasAlgorithm` "lessThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate adts typeEnv left
    tell [(var, l)]
    (integrate, _, integrateBranches) <- toIRIntegrate conf clauses typeEnv adts right (IRVar var) posInf
    var2 <- mkVariable "rhs_integral"
    let returnExpr = IRIf sample (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))
    tell [(var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | extras `hasAlgorithm` "lessThanRight" = do --p(x | var >= const
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate adts typeEnv right
    tell [(var, r)]
    (integrate, _, integrateBranches) <- toIRIntegrate conf clauses typeEnv adts left (IRVar var) posInf
    var2 <- mkVariable "lhs_integral"
    tell [(var2, integrate)]
    let returnExpr = IRIf sample (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))  (IRVar var2)
    return (returnExpr, const0, integrateBranches)
toIRProbability conf clauses typeEnv adts (Not (TypeInfo {rType = TBool}) f) sample =
  toIRProbability conf clauses typeEnv adts f (IRUnaryOp OpNot sample)
toIRProbability conf clauses typeEnv adts (And (TypeInfo {rType = TBool}) a b) sample = do
  (aP, aDim, aBC) <- toIRProbability conf clauses typeEnv adts a (IRConst $ VBool True)
  (bP, bDim, bBC) <- toIRProbability conf clauses typeEnv adts b (IRConst $ VBool True)
  (resP, resDim) <- (aP, aDim) `multP` (bP, bDim)
  return $ (IRIf sample resP (IROp OpSub (IRConst $ VFloat 1) resP), resDim, IROp OpPlus aBC bBC)
toIRProbability conf clauses typeEnv adts (Or (TypeInfo {rType = TBool}) a b) sample = do
  (aP, aDim, aBC) <- toIRProbability conf clauses typeEnv adts a (IRConst $ VBool False)
  (bP, bDim, bBC) <- toIRProbability conf clauses typeEnv adts b (IRConst $ VBool False)
  (resP, resDim) <- (aP, aDim) `multP` (bP, bDim)
  return $ (IRIf sample (IROp OpSub (IRConst $ VFloat 1) resP) resP, resDim, IROp OpPlus aBC bBC)  -- p(a || b == True) == 1 - p(a == False) * p(b == False)
toIRProbability conf clauses typeEnv adts (Normal t) sample = return (IRDensity IRNormal sample, IRIf (IRUnaryOp OpIsAny sample) const0 (IRConst $ VFloat 1), const0)
toIRProbability conf clauses typeEnv adts (Uniform t) sample = return (IRDensity IRUniform sample, IRIf (IRUnaryOp OpIsAny sample) const0 (IRConst $ VFloat 1), const0)
toIRProbability conf clauses typeEnv adts (ReadNN _ name symbol) sample = do
  -- Same code as for calling a top level function
  var <- mkVariable "callNN"
  sym <- toIRGenerate adts typeEnv symbol
  tell [(var, IRInvoke (IRApply (IRApply (IRVar (name ++ "_auto_prob")) sym) sample))]
  if countBranches conf then
    return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
  else
    return (IRTFst (IRVar var), IRTSnd (IRVar var), const0)
toIRProbability conf clauses typeEnv adts (Lambda t name subExpr) sample = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      -- Lambda parameter is a function
      let newTypeEnv = (name, (paramRType, True)):typeEnv
      irTuple <- lift (runWriterT (toIRProbability conf clauses newTypeEnv adts subExpr sample)) <&> generateLetInBlock conf
      return (IRLambda name irTuple, const0, const0)
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv
      irTuple <- lift (runWriterT (toIRProbability conf clauses newTypeEnv adts subExpr sample)) <&> generateLetInBlock conf
      return (IRLambda name irTuple, const0, const0)
toIRProbability conf clauses typeEnv adts (Apply TypeInfo{rType=rt} l v) sample | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate adts typeEnv v
  lIR <- toIRGenerate adts typeEnv l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      retExpr <- indicator (IROp OpEq (IRInvoke (IRApply lIR vIR)) sample)
      return (retExpr, const0, const0)
toIRProbability conf clauses typeEnv adts (Apply TypeInfo{rType=rt} l v) sample | pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate adts typeEnv v
  (lIR, _, _) <- toIRProbability conf clauses typeEnv adts l sample -- Dim and BC are irrelevant here. We need to extract these from the return tuple
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> do
      retVal <- mkVariable "call"
      tell [(retVal, IRInvoke (IRApply lIR vIR))]
      if countBranches conf then
        return (IRTFst (IRVar retVal), IRTFst (IRTSnd (IRVar retVal)), IRTSnd (IRTSnd (IRVar retVal)))
      else
        return (IRTFst (IRVar retVal), IRTSnd (IRVar retVal), const0)

toIRProbability conf clauses typeEnv adts (Apply TypeInfo{rType=rt} l v) sample | pType (getTypeInfo v) == Prob || pType (getTypeInfo v) == Integrate = do
  let lChainName = chainName (getTypeInfo l)
  let lInv = IRLambda lChainName (toInvExpr clauses adts lChainName)
  let appliedSample = IRInvoke (IRApply lInv sample)
  toIRProbability conf clauses typeEnv adts v appliedSample
toIRProbability conf clauses typeEnv adts (Apply TypeInfo{rType=rt} l v) sample = error "This instance if apply is not yet implemented"
toIRProbability conf clauses typeEnv adts (Cons _ hdExpr tlExpr) sample = do
  headTuple <- lift (runWriterT (toIRProbabilitySave conf clauses typeEnv adts hdExpr (IRHead sample))) <&> generateLetInBlock conf
  tailTuple <- lift (runWriterT (toIRProbabilitySave conf clauses typeEnv adts tlExpr (IRTail sample))) <&> generateLetInBlock conf
  let dim = if countBranches conf then IRTFst . IRTSnd else IRTSnd
  mult <- (IRTFst headTuple, dim headTuple)  `multP` (IRTFst tailTuple, dim tailTuple)
  return (IRIf (IROp OpEq sample (IRConst $ VList EmptyList)) (IRConst $ VFloat 0) (fst mult), IRIf (IROp OpEq sample (IRConst $ VList EmptyList)) (IRConst $ VFloat 0) (snd mult), IRIf (IROp OpEq sample (IRConst $ VList EmptyList)) (IRConst $ VFloat 0) (IROp OpPlus (IRTSnd (IRTSnd headTuple)) (IRTSnd (IRTSnd tailTuple))))
  --return (IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (fst mult), IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (snd mult), IROp OpPlus headBranches tailBranches)
toIRProbability conf clauses typeEnv adts (TCons _ t1Expr t2Expr) sample = do
  (t1P, t1Dim, t1Branches) <- toIRProbabilitySave conf clauses typeEnv adts t1Expr (IRTFst sample)
  (t2P, t2Dim, t2Branches) <- toIRProbabilitySave conf clauses typeEnv adts t2Expr (IRTSnd sample)
  mult <- (t1P, t1Dim) `multP` (t2P, t2Dim)
  return (fst mult, snd mult, IROp OpPlus t1Branches t2Branches)
toIRProbability conf clauses typeEnv adts (InjF TypeInfo {tags=extras} name [left, right]) sample
  | extras `hasAlgorithm` "injF2Enumerable" = do
  -- Get all possible values for subexpressions
  let extrasLeft = tags $ getTypeInfo left
  let extrasRight = tags $ getTypeInfo right
  let enumListL = head $ [x | EnumList x <- extrasLeft]
  let enumListR = head $ [x | EnumList x <- extrasRight]

  fPair <- instantiate mkVariable adts name -- FPair of the InjF with unique names
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
    (pLeft, _, _) <- toIRProbability conf clauses typeEnv adts left (IRVar x2)
    (pRight, _, _) <- toIRProbability conf clauses typeEnv adts right (IROp OpSub sample (IRVar x2))
    tell [(x3, sample)]
    let returnExpr = case topKThreshold conf of
          Nothing -> IRIf (IRElementOf invExpr (IRConst (fmap failConversion (constructVList enumListR)))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
          Just thr -> IRIf (IROp OpAnd (IRElementOf invExpr (IRConst (fmap failConversion (constructVList enumListR)))) (IROp OpGreaterThan pLeft (IRConst (VFloat thr)))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
    let branchesExpr = case topKThreshold conf of
          Nothing -> IRIf (IRElementOf invExpr (IRConst (fmap failConversion (constructVList enumListR)))) (IRConst (VFloat 1)) (IRConst (VFloat 0))
          Just thr -> IRIf (IROp OpAnd (IRElementOf invExpr (IRConst (fmap failConversion (constructVList enumListR)))) (IROp OpGreaterThan pLeft (IRConst (VFloat thr)))) (IRConst (VFloat 1)) (IRConst (VFloat 0))
    return (returnExpr, const0, branchesExpr)
    )) <&> generateLetInBlock conf
  uniquePrefix <- mkVariable ""
  let enumSumExpr = IREnumSum x2 (fmap failConversion (constructVList enumListL)) $ IRTFst irTuple
  let branchCountSum = IREnumSum x2 (fmap failConversion (constructVList enumListL)) $ IRTSnd (IRTSnd irTuple)
  return (irMap (uniqueify [x2, x3] uniquePrefix) enumSumExpr, const0, irMap (uniqueify [x2, x3] uniquePrefix) branchCountSum)
toIRProbability conf clauses typeEnv adts (InjF _ name params) sample | isHigherOrder adts name = do
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
  tell [(aVar, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRProbabilitySave else toIRProbability
  -- Create all inverses of the ho functions and save them on the variable stack
  -- Then create a substitution that substitutes f^-1 to f_prob. All substitutions are then composed in the fold
  renVar <- foldM (\sub tup -> createHOInverse clauses adts tup <&> (.) sub) id (zip fVars fs)
  (paramExpr, paramDim, paramBranches) <- probF conf clauses typeEnv adts a invExpr
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula
  let returnP = IROp OpMult paramExpr (IRIf (IROp OpEq paramDim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs invDerivExpr))
  let appTestExpr e = IRIf appTest e const0
  return (renVar (appTestExpr returnP), renVar (appTestExpr paramDim), renVar (appTestExpr paramBranches))
toIRProbability conf clauses typeEnv adts (InjF _ name [param]) sample = do
  -- FPair of the InjF with unique names
  fPair <- instantiate mkVariable adts name
  -- Unary InjF has a single inversion
  let FPair _ [inv] = fPair
  let FDecl {inputVars=[v], body=invExpr, applicability=appTest, deconstructing=decons, derivatives=[(_, invDerivExpr)]} = inv
  -- Set sample value to the variable name in the InjF
  tell [(v, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRProbabilitySave else toIRProbability
  -- Get the probabilistic inference code for the parameter
  (paramExpr, paramDim, paramBranches) <- probF conf clauses typeEnv adts param invExpr
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula
  let returnP = IROp OpMult paramExpr (IRIf (IROp OpEq paramDim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs invDerivExpr))
  let appTestExpr e = IRIf appTest e const0
  return (appTestExpr returnP, appTestExpr paramDim, appTestExpr paramBranches)
toIRProbability conf clauses typeEnv adts e@(InjF TypeInfo {tags=extras, rType=rt} name params) sample
  | isNothing (getProbIndex params) = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is equal to the sample
  expr <- toIRGenerate adts typeEnv e
  let cmp = case rt of
        TFloat -> OpApprox
        _ -> OpEq
  retExpr <- indicator $ IROp cmp expr sample
  return (retExpr, const0, const0)
toIRProbability conf clauses typeEnv adts e@(InjF TypeInfo {tags=extras} name params) sample
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
  mapM_ (\(eVar, e) -> toIRGenerate adts typeEnv e >>= \x -> tell [(eVar, x)]) (zip detVars detEs)
  tell [(v1, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRProbabilitySave else toIRProbability
  -- Get the probabilistic inference expression of the non-deterministic subexpression
  (paramExpr, paramDim, paramBranches) <- probF conf clauses typeEnv adts (params !! probIdx) invExpr
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula if dim > 0
  let returnP = IROp OpMult paramExpr (IRIf (IROp OpEq paramDim const0) (IRConst (VFloat 1)) (IRUnaryOp OpAbs invDeriv))
  let appTestExpr e = IRIf appTest e const0
  return (appTestExpr returnP, appTestExpr paramDim, appTestExpr paramBranches)
toIRProbability conf clauses typeEnv adts (Null _) sample = do
  expr <- indicator (IROp OpEq sample (IRConst $ VList EmptyList))
  return (expr, const0, const0)
toIRProbability conf clauses typeEnv adts (Constant TypeInfo {rType=rt} value) sample = do
  let comp = case rt of
              TFloat -> IROp OpApprox sample (IRConst (fmap failConversion value))
              _ -> IROp OpEq sample (IRConst (fmap failConversion value))
  expr <- indicator comp
  return (expr, const0, const0)
toIRProbability conf clauses typeEnv adts (Var TypeInfo {rType=rt} n) sample = do
  -- Variable might be a function
  case lookup n typeEnv of
    -- Var is a function
    Just(TArrow _ _, hasInference) -> do
      var <- mkVariable "call"
      let name = if hasInference then n ++ "_prob" else n
      tell [(var, IRApply (IRVar name) sample)]
      -- The return value is still a function. No need to do dim and branch counting here
      return (IRVar var, const0, const0)
    -- var is a function without a inference function
    Just(TArrow _ _, False) -> do
      var <- mkVariable "call"
      tell [(var, IRApply (IRVar n) sample)]
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
      let comp = case rt of
              TFloat -> IROp OpApprox sample (IRVar n)
              _ -> IROp OpEq sample (IRVar n)
      expr <- indicator comp
      return (expr, const0, const0)
    Nothing -> error ("Could not find name in TypeEnv: " ++ n)
toIRProbability conf clauses typeEnv adts (ThetaI _ a i) sample = do
  a' <- toIRGenerate adts typeEnv a
  expr <- indicator (IROp OpApprox sample (IRTheta a' i))
  return (expr, const0, const0)
toIRProbability conf clauses typeEnv adts (Subtree _ a i) sample = error "Cannot infer prob on subtree expression. Please check your syntax"
toIRProbability conf clauses typeEnv adts x sample = error ("found no way to convert to IR: " ++ show x)

multP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
multP (aM, aDim) (bM, bDim) = return (IROp OpMult aM bM, IROp OpPlus aDim bDim)

addP :: (IRExpr, IRExpr) -> (IRExpr, IRExpr) -> CompilerMonad (IRExpr, IRExpr)
addP (aM, aDim) (bM, bDim) = do
  pVarA <- mkVariable "pA"
  pVarB <- mkVariable "pB"
  dimVarA <- mkVariable "dimA"
  dimVarB <- mkVariable "dimB"
  tell [(pVarA, aM), (pVarB, bM), (dimVarA, aDim), (dimVarB, bDim)]
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
  tell [(pVarA, aM), (pVarB, bM), (dimVarA, aDim), (dimVarB, bDim)]
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

createHOInverse :: [[HornClause]] -> [ADTDecl]-> (String, Expr) -> CompilerMonad (IRExpr -> IRExpr)
createHOInverse clauses adts (fVar, f) = do
  let inverseF = toInvExpr clauses adts (chainName $ getTypeInfo f)
  let inverseLambda = IRLambda (chainName $ getTypeInfo f) inverseF
  -- Rename all occurances of f^-1 from the definition to f_prob
  let renVar = renameVar (fVar ++ "^-1") (fVar ++ "_prob")
  tell [(fVar ++ "_prob", inverseLambda)]
  return $ renVar

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
toIRGenerate :: [ADTDecl] -> TypeEnv -> Expr -> CompilerMonad  IRExpr
toIRGenerate adts typeEnv (IfThenElse _ cond left right) = do
  c <- toIRGenerate adts typeEnv cond
  l <- toIRGenerate adts typeEnv left
  r <- toIRGenerate adts typeEnv right
  return $ IRIf c l r
toIRGenerate adts typeEnv (LetIn _ n v b) = do
  v' <- toIRGenerate adts typeEnv v
  b' <- toIRGenerate adts typeEnv b
  return $ IRLetIn n v' b'
toIRGenerate adts typeEnv (GreaterThan _ left right) = do
  l <- toIRGenerate adts typeEnv left
  r <- toIRGenerate adts typeEnv right
  return $ IROp OpGreaterThan l r
toIRGenerate adts typeEnv (LessThan _ left right) = do
  l <- toIRGenerate adts typeEnv left
  r <- toIRGenerate adts typeEnv right
  return $ IROp OpLessThan l r
toIRGenerate adts typeEnv (Not _ f) = do
  f' <- toIRGenerate adts typeEnv f
  return $ IRUnaryOp OpNot f'
toIRGenerate adts typeEnv (And _ a b) = do
  a' <- toIRGenerate adts typeEnv a
  b' <- toIRGenerate adts typeEnv b
  return $ IROp OpAnd a' b'
toIRGenerate adts typeEnv (Or _ a b) = do
  a' <- toIRGenerate adts typeEnv a
  b' <- toIRGenerate adts typeEnv b
  return $ IROp OpOr a' b'
toIRGenerate adts typeEnv (ThetaI _ a ix) = do
  a' <- toIRGenerate adts typeEnv a
  return $ IRTheta a' ix
toIRGenerate adts typeEnv (Subtree _ a ix) = do
  a' <- toIRGenerate adts typeEnv a
  return $ IRSubtree a' ix
toIRGenerate adts typeEnv (Constant _ x) = return (IRConst (fmap failConversion x))
toIRGenerate adts typeEnv (Null _) = return $ IRConst (VList EmptyList)
toIRGenerate adts typeEnv (Cons _ hd tl) = do
  h <- toIRGenerate adts typeEnv hd
  t <- toIRGenerate adts typeEnv tl
  return $ IRCons h t
toIRGenerate adts typeEnv (TCons _ t1 t2) = do
  t1' <- toIRGenerate adts typeEnv t1
  t2' <- toIRGenerate adts typeEnv t2
  return $ IRTCons t1' t2'
toIRGenerate adts typeEnv (Uniform _) = return $ IRSample IRUniform
toIRGenerate adts typeEnv (Normal _) = return $ IRSample IRNormal
toIRGenerate adts typeEnv (InjF _ name params) = do
  -- Assuming that the logic within packParamsIntoLetinsGen typeEnv is correct.
  -- You will need to process vars and params, followed by recursive calls to fwdExpr.
  fPair <- instantiate mkVariable adts name
  let FPair fwd _ = fPair
  let FDecl {inputVars=vars, body=fwdExpr} = fwd
  prefix <- mkVariable ""
  letInBlock <- packParamsIntoLetinsGen adts typeEnv vars params fwdExpr
  return $ irMap (uniqueify vars prefix) letInBlock
  where
    Just fPair = lookup name (globalFEnv adts)
    FPair fwd _ = fPair
    FDecl {inputVars=vars, body=fwdExpr} = fwd
toIRGenerate adts typeEnv (Var _ name) = do
  case lookup name typeEnv of
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
toIRGenerate adts typeEnv (Lambda t name subExpr) = do
  let (TArrow paramRType _) = rType t
  case paramRType of
    TArrow (TArrow _ _) _ -> do
      let newTypeEnv = (name, (paramRType, True)):typeEnv
      irTuple <- toIRGenerate adts newTypeEnv subExpr
      return $ IRLambda name irTuple
    _ -> do
      let newTypeEnv = (name, (paramRType, False)):typeEnv
      irTuple <- toIRGenerate adts newTypeEnv subExpr
      return $ IRLambda name irTuple
toIRGenerate adts typeEnv (Apply TypeInfo {rType=rt} l v) = do
  l' <- toIRGenerate adts typeEnv l
  v' <- toIRGenerate adts typeEnv v
  case rt of
    TArrow _ _ -> return $ IRApply l' v'
    _ -> return $ IRInvoke $ IRApply l' v'
toIRGenerate adts typeEnv (ReadNN _ name subexpr) = do
  sub <- toIRGenerate adts typeEnv subexpr
  return $ IRInvoke (IRApply (IRVar (name ++ "_auto_gen")) sub)
toIRGenerate adts typeEnv x = error ("found no way to convert to IRGen: " ++ show x)

packParamsIntoLetinsGen :: [ADTDecl] -> TypeEnv -> [String] -> [Expr] -> IRExpr -> CompilerMonad  IRExpr
packParamsIntoLetinsGen adts typeEnv [] [] expr = return $ expr
packParamsIntoLetinsGen adts typeEnv [] _ _ = error "More parameters than variables"
packParamsIntoLetinsGen adts typeEnv _ [] _ = error "More variables than parameters"
packParamsIntoLetinsGen adts typeEnv (v:vars) (p:params) expr = do
  pExpr <- toIRGenerate adts typeEnv p
  e <- packParamsIntoLetinsGen adts typeEnv vars params expr
  return $ IRLetIn v pExpr e

--Adds an additional check that the bounds are not equal
--We need this bounds check only once, because no invertible transformation can make the bounds be equal when they were not
--TODO: Some InjF could lead to CoV, which would make the bounds check at the to wrong
toIRIntegrateSave :: CompilerConfig -> [[HornClause]] -> TypeEnv -> [ADTDecl] -> Expr -> IRExpr -> IRExpr -> CompilerMonad CompilationResult
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
  (prob, probDim, probBC) <- toIRProbability conf clauses typeEnv adts expr lower
  (integ, integDim, integBC) <- toIRIntegrate conf clauses typeEnv adts expr lower higher
  let eqCheck = IRIf (IROp OpEq lower higher)
  let anyCheck = IRIf (IROp OpAnd (IRUnaryOp OpIsAny lower) (IRUnaryOp OpIsAny higher))
  return (anyCheck (IRConst $ VFloat 1) (eqCheck prob integ), anyCheck (IRConst $ VFloat 0) (eqCheck probDim integDim), anyCheck (IRConst $ VFloat 0) (eqCheck probBC integBC))


toIRIntegrate :: CompilerConfig -> [[HornClause]] -> TypeEnv -> [ADTDecl] -> Expr -> IRExpr -> IRExpr -> CompilerMonad CompilationResult
toIRIntegrate conf clauses typeEnv adts expr@(Uniform _) lower higher = do
  (density, _, _) <- toIRProbability conf clauses typeEnv adts expr lower
  --let expr = IRIf (IROp OpEq lower higher) density (IROp OpSub (IRCumulative IRUniform higher) (IRCumulative IRUniform lower))
  let expr = (IROp OpSub (IRCumulative IRUniform higher) (IRCumulative IRUniform lower))
  return (expr, IRIf (IROp OpEq lower higher) (IRConst $ VFloat 1) const0, const0)
toIRIntegrate conf clauses typeEnv adts expr@(Normal _) lower higher = do
  (density, _, _) <- toIRProbability conf clauses typeEnv adts expr lower
  --let expr = IRIf (IROp OpEq lower higher) density (IROp OpSub (IRCumulative IRNormal higher) (IRCumulative IRNormal lower))
  let expr = (IROp OpSub (IRCumulative IRNormal higher) (IRCumulative IRNormal lower))
  return (expr, IRIf (IROp OpEq lower higher) (IRConst $ VFloat 1) const0, const0)
toIRIntegrate conf clauses typeEnv adts (TCons _ t1Expr t2Expr) low high = do
  (t1P, t1Dim,  t1Branches) <- toIRIntegrateSave conf clauses typeEnv adts t1Expr (IRTFst low) (IRTFst high)
  (t2P, t2Dim,  t2Branches) <- toIRIntegrateSave conf clauses typeEnv adts t2Expr (IRTSnd low) (IRTSnd high)
  (productP, productDim) <- (t1P, t1Dim) `multP` (t2P, t2Dim)
  return (productP, productDim, IROp OpPlus t1Branches t2Branches)
toIRIntegrate conf clauses typeEnv adts (IfThenElse _ cond left right) low high = do
  var_cond_p <- mkVariable "cond"
  (condExpr, _, condBranches) <- toIRProbability conf clauses typeEnv adts cond (IRConst (VBool True))
  (leftExpr, _, leftBranches) <- toIRIntegrate conf clauses typeEnv adts left low high
  (rightExpr, _, rightBranches) <- toIRIntegrate conf clauses typeEnv adts right low high
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
toIRIntegrate conf clauses typeEnv adts (Cons _ hdExpr tlExpr) low high = do
  headTuple <- lift (runWriterT (toIRIntegrateSave conf clauses typeEnv adts hdExpr (IRHead low) (IRHead high))) <&> generateLetInBlock conf
  tailTuple <- lift (runWriterT (toIRIntegrateSave conf clauses typeEnv adts tlExpr (IRTail low) (IRTail high))) <&> generateLetInBlock conf
  let dim = if countBranches conf then IRTFst . IRTSnd else IRTSnd
  (multP, multDim) <- (IRTFst headTuple, dim headTuple)  `multP` (IRTFst tailTuple, dim tailTuple)
  return (IRIf (IROp OpOr (IROp OpEq low (IRConst $ VList EmptyList)) (IROp OpEq high (IRConst $ VList EmptyList))) (IRConst $ VFloat 0) multP, multDim, IROp OpPlus (IRTSnd (IRTSnd headTuple)) (IRTSnd (IRTSnd tailTuple)))
toIRIntegrate conf clauses typeEnv adts (Null _) low high = do
  ind <- indicator (IROp OpAnd (IROp OpEq low (IRConst $ VList EmptyList)) (IROp OpEq high (IRConst $ VList EmptyList)))
  return (ind, const0, const0)
toIRIntegrate conf clauses typeEnv adts (Constant _ value) low high = do
  ind <- indicator (IROp OpAnd (IROp OpLessThan low (IRConst (fmap failConversion value))) (IROp OpGreaterThan high (IRConst (fmap failConversion value)))) --TODO What to do if low and high are equal?
  return (ind, const0, const0)
toIRIntegrate conf clauses typeEnv adts (ThetaI _ a i) low high = do
  a' <-  toIRGenerate adts typeEnv a
  let val = IRTheta a' i
  ind <- indicator (IROp OpAnd (IROp OpLessThan low val) (IROp OpGreaterThan high val)) --TODO What to do if low and high are equal?
  return (ind, const0, const0)
toIRIntegrate conf clauses typeEnv adts (InjF _ name params) low high | isHigherOrder adts name = do
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
toIRIntegrate conf clauses typeEnv adts (InjF _ name [param]) low high = do
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
toIRIntegrate conf clauses typeEnv adts e@(InjF TypeInfo {tags=extras, rType=rt} name params) low high
  | isNothing (getProbIndex params) = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is equal to the sample
  expr <- toIRGenerate adts typeEnv e
  retExpr <- indicator $ IROp OpAnd (IROp OpLessThan low expr) (IROp OpGreaterThan high expr)
  return (retExpr, const0, const0)
toIRIntegrate conf clauses typeEnv adts (InjF TypeInfo {tags=extras} name params) low high
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
  mapM_ (\(eVar, e) -> toIRGenerate adts typeEnv e >>= \x -> tell [(eVar, x)]) (zip detVars detEs)
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
toIRIntegrate conf clauses typeEnv adts (Lambda t name subExpr) low high = do
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
toIRIntegrate conf clauses typeEnv adts (Apply TypeInfo{rType=rt} l v) low high = do
  vIR <- toIRGenerate adts typeEnv v
  (lIR, _, _) <- toIRIntegrate conf clauses typeEnv adts l low high -- Dim and BC are irrelevant here. We need to extract these from the return tuple
  case rt of
    TArrow _ _ -> return (IRApply lIR vIR, const0, const0)
    _ -> if countBranches conf then
           return (IRTFst (IRInvoke (IRApply lIR vIR)), IRTFst (IRTSnd (IRInvoke (IRApply lIR vIR))), IRTSnd (IRTSnd (IRInvoke (IRApply lIR vIR))))
         else
           return (IRTFst (IRInvoke (IRApply lIR vIR)), IRTSnd (IRInvoke (IRApply lIR vIR)), const0)
toIRIntegrate conf clauses typeEnv adts (Var _ n) low high = do
  -- Variable might be a function
  case lookup n typeEnv of
   -- Var is a function
   Just(TArrow _ _, hasInference) -> do
     var <- mkVariable "call"
     let name = if hasInference then n ++ "_integ" else n
     tell [(var, IRApply (IRApply (IRVar name) low) high)]
     -- The return value is still a function. No need to do dim and branch counting here
     return (IRVar var, const0, const0)
   Just(TArrow _ _, False) -> do
     var <- mkVariable "call"
     tell [(var, IRApply (IRApply (IRVar n) low) high)]
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
toIRIntegrate _ _ _ _ x _ _ = error ("found no way to convert to IRIntegrate: " ++ show x)
