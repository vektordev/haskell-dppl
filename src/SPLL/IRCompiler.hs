module SPLL.IRCompiler where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
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

-- SupplyT needs to be a transformer, because Supply does not implement Functor correctly
type CompilerMonad a = WriterT [(String, IRExpr)] (SupplyT Int Identity) a

-- perhaps as an explicit lambda in the top of the expression, otherwise we'll get trouble generating code.
-- TODO: How do we deal with top-level lambdas in binding here?
--  TL-Lambdas are presumably to be treated differently than non-TL, at least as far as prob is concerned.
envToIR :: CompilerConfig -> Program -> [(String, IRExpr)] --FIXME add postProcess
envToIR conf p = concatMap (\(name, binding) ->
  let pt = pType $ getTypeInfo binding
      rt = rType $ getTypeInfo binding in
    if (pt == Deterministic || pt == Integrate) && (isOnlyNumbers rt) then
      [(name ++ "_integ", postProcess (IRLambda "low" (IRLambda "high" (runCompile conf (toIRIntegrate conf binding (IRVar "low") (IRVar "high")))))),
       (name ++ "_prob",postProcess (IRLambda "sample" (runCompile conf (toIRProbability conf binding (IRVar "sample"))))),
       (name ++ "_gen", postProcess (fst $ runIdentity $ runSupplyVars $ runWriterT (toIRGenerate binding)))]
    else if pt == Deterministic || pt == Integrate || pt == Prob then
      [(name ++ "_prob",postProcess  ((IRLambda "sample" (runCompile conf (toIRProbability conf binding (IRVar "sample")))))),
       (name ++ "_gen", postProcess (fst $ runIdentity $ runSupplyVars $ runWriterT $ toIRGenerate binding))]
    else
      [(name ++ "_gen", postProcess ( fst $ runIdentity $ runSupplyVars $ runWriterT $ toIRGenerate binding))]) (functions p)

type CompilationResult = (IRExpr, IRExpr, IRExpr)

runCompile :: CompilerConfig -> CompilerMonad CompilationResult -> IRExpr
runCompile conf codeGen = generateLetInBlock conf (runWriterT codeGen)
  
generateLetInBlock :: CompilerConfig -> (SupplyT Int Identity) (CompilationResult, [(String, IRExpr)]) -> IRExpr
generateLetInBlock conf codeGen = 
  case m of 
    (IRLambda _ _) -> returnize (foldr (\(var, val) expr  -> IRLetIn var val expr) m binds) --Dont make tuple out of lambdas, as the snd (and thr) element don't contain information anyway
    _ -> if countBranches conf && not (isLambda m) then
            returnize (foldr (\(var, val) expr  -> IRLetIn var val expr) (IRTCons m (IRTCons dim bc)) binds)
          else
            returnize (foldr (\(var, val) expr  -> IRLetIn var val expr) (IRTCons m dim) binds)
  where ((m, dim, bc), binds) = runIdentity $ runSupplyVars codeGen

  
runSupplyVars :: (Monad m) => SupplyT Int m a -> m a
runSupplyVars codeGen = runSupplyT codeGen (+1) 1

isValue :: IRExpr -> Bool
isValue (IRConst _) = True
isValue _ = False

isLambda :: IRExpr -> Bool
isLambda IRLambda {} = True
isLambda _ = False

unval :: IRExpr -> Value
unval (IRConst val) = val
unval _ = error "tried to unval a non-val"

--strip all top-level lambdas and collect the bound names.
--unwrapTLLambdas :: Expr t a -> ([Varname], Expr t a)
--unwrapTLLambdas (Lambda _ name subExpr) = (name : innerNames, unwrappedExpr)
--  where (innerNames, unwrappedExpr) = unwrapTLLambdas subExpr
--unwrapTLLambdas expr = ([], expr)

postProcess :: IRExpr -> IRExpr
--postProcess = id
postProcess = fixedPointIteration optimize

fixedPointIteration :: (Eq a, Show a) => (a -> a) -> a -> a
fixedPointIteration f x = if fx == x then x else fixedPointIteration f fx
  where fx = f x

optimize :: IRExpr -> IRExpr
optimize = irMap evalAll
--TODO: We can also optimize index magic, potentially here. i.e. a head tail tail x can be simplified.
--TODO: Unary operators
evalAll :: IRExpr -> IRExpr
evalAll expr@(IROp op leftV rightV)
  | isValue leftV && isValue rightV = IRConst (forceOp op (unval leftV) (unval rightV))
  | isValue leftV || isValue rightV = softForceLogic op leftV rightV
  | otherwise = expr 
evalAll (IRIf _ left right) | left == right = left
evalAll x@(IRIf cond left right) =
  if isValue cond
    then if unval cond == VBool True
      then left
      else right
    else x
evalAll x@(IRCons left right) =
  if isValue left && isValue right
    then let (VList tl) = unval right in IRConst (VList (unval left : tl))
    else x
evalAll (IRHead expr) =
  if isValue expr
    then let (VList (_:xs)) = unval expr in IRConst $ VList xs
    else IRHead expr
evalAll ex@(IRLetIn name val scope)
  | isSimple val = irMap (replace (IRVar name) val) scope
  | countUses name scope == 1 = irMap (replace (IRVar name) val) scope
  | countUses name scope == 0 = scope
  | otherwise = ex
evalAll (IRTCons (IRLambda n a) (IRLambda m b)) | n == m = IRLambda n (IRTCons a b)
evalAll (IRDensity IRNormal (IRConst (VFloat x))) = IRConst (VFloat ((1 / sqrt (2 * pi)) * exp (-0.5 * x * x)))
evalAll (IRCumulative IRNormal (IRConst (VFloat x))) = IRConst (VFloat ((1/2) * (1 + erf(x/sqrt(2)))))
evalAll (IRDensity IRUniform (IRConst (VFloat x))) = IRConst (VFloat (if x >= 0 && x <= 1 then 1 else 0))
evalAll (IRCumulative IRUniform (IRConst (VFloat x))) = IRConst (VFloat (if x < 0 then 0 else if x > 1 then 1 else x))
evalAll x = x
  
countUses :: String -> IRExpr -> Int
countUses var (IRVar a) | a == var = 1
countUses var expr = sum (map (countUses var) (getIRSubExprs expr))

isSimple :: IRExpr -> Bool
--isSimple (IRTheta a) = True
isSimple (IRVar a) = True
isSimple (IRConst a) = True
isSimple _ = False

replace :: Eq p => p -> p -> p -> p
replace find replace' expr = if find == expr then replace' else expr

softForceLogic :: Operand -> IRExpr -> IRExpr -> IRExpr
softForceLogic OpOr (IRConst (VBool True)) _ = IRConst (VBool True)
softForceLogic OpOr _ (IRConst (VBool True)) = IRConst (VBool True)
softForceLogic OpOr (IRConst (VBool False)) right = right
softForceLogic OpOr left (IRConst (VBool False)) = left
softForceLogic OpAnd (IRConst (VBool True)) right = right
softForceLogic OpAnd left (IRConst (VBool True)) = left
softForceLogic OpAnd (IRConst (VBool False)) _ = IRConst (VBool False)
softForceLogic OpAnd _ (IRConst (VBool False)) = IRConst (VBool False)
softForceLogic op left right = IROp op left right     -- Nothing can be done

forceOp :: Operand -> Value -> Value -> Value
forceOp OpEq x y = VBool (x == y)
forceOp OpMult (VInt x) (VInt y) = VInt (x*y)
forceOp OpMult (VFloat x) (VFloat y) = VFloat (x*y)
forceOp OpPlus (VInt x) (VInt y) = VInt (x+y)
forceOp OpPlus (VFloat x) (VFloat y) = VFloat (x+y)
forceOp OpDiv (VInt _) (VInt _) = error "tried to do integer division in forceOp"
forceOp OpDiv (VFloat x) (VFloat y) = VFloat (x/y)
forceOp OpSub (VInt x) (VInt y) = VInt (x-y)
forceOp OpSub (VFloat x) (VFloat y) = VFloat (x-y)
forceOp OpOr (VBool x) (VBool y) = VBool (x || y)
forceOp OpGreaterThan (VInt x) (VInt y) = VBool (x > y)
forceOp OpGreaterThan (VFloat x) (VFloat y) = VBool (x > y)
forceOp OpLessThan (VInt x) (VInt y) = VBool (x < y)
forceOp OpLessThan (VFloat x) (VFloat y) = VBool (x < y)
forceOp OpAnd (VBool x) (VBool y) = VBool (x && y)

returnize :: IRExpr -> IRExpr
--returnize e | trace (show e) False = undefined
returnize (IRIf cond left right) = IRIf cond (returnize left) (returnize right)
returnize (IRReturning expr) = IRReturning expr
returnize (IRLetIn name binding scope) = IRLetIn name binding (returnize scope)
returnize (IRLambda name expr) = IRLambda name (returnize expr)
returnize other = IRReturning other

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
toIRProbability :: CompilerConfig -> Expr -> IRExpr -> CompilerMonad CompilationResult
toIRProbability conf (IfThenElse t cond left right) sample = do
  var_cond_p <- mkVariable "cond"
  (condExpr, condDim, condBranches) <- toIRProbability conf cond (IRConst (VBool True))
  (leftExpr, leftDim, leftBranches) <- toIRProbability conf left sample
  (rightExpr, rightDim, rightBranches) <- toIRProbability conf right sample
  -- p(y) = if p_cond < thresh then p_else(y) * (1-p_cond(y)) else if p_cond > 1 - thresh then p_then(y) * p_cond(y) else p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
  let thr = topKThreshold conf
  case thr of
    Just thresh -> do
      mul1 <- (condExpr, condDim) `multP` (leftExpr, leftDim)
      sub <- (IRConst (VFloat 1), const0) `subP` (condExpr, condDim)
      mul2 <- sub `multP` (rightExpr, rightDim)
      add <- mul1 `addP` mul2
      let returnExpr = IRIf
            (IROp OpLessThan (IRVar var_cond_p) (IRConst (VFloat thresh)))
            (fst mul2)
            (IRIf (IROp OpGreaterThan (IRVar var_cond_p) (IRConst (VFloat (1-thresh))))
              (fst mul1)
              (fst add))
      let returnDim = IRIf
            (IROp OpLessThan (IRVar var_cond_p) (IRConst (VFloat thresh)))
            (snd mul2)
            (IRIf (IROp OpGreaterThan (IRVar var_cond_p) (IRConst (VFloat (1-thresh))))
              (snd mul1)
              (snd add))
      tell [(var_cond_p, condExpr)]
      return (returnExpr, returnDim, IROp OpPlus condExpr (IROp OpPlus leftExpr rightExpr))
    -- p(y) = p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
    Nothing -> do
      mul1 <- (condExpr, condDim) `multP` (leftExpr, leftDim)
      sub <- (IRConst (VFloat 1), const0) `subP` (condExpr, condDim)
      mul2 <- sub `multP` (rightExpr, rightDim)
      returnExpr <- mul1 `addP` mul2
      tell [(var_cond_p, condExpr)]
      return (fst returnExpr, snd returnExpr, IROp OpPlus condExpr (IROp OpPlus leftExpr rightExpr))
toIRProbability conf (GreaterThan (TypeInfo {rType = t, tags = extras}) left right) sample
  --TODO: Find a better lower bound than just putting -9999999
  | extras `hasAlgorithm` "greaterThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    (integrate, _, integrateBranches) <- toIRIntegrate conf right (IRConst (VFloat (-9999999))) (IRVar var)
    var2 <- mkVariable "rhs_integral"
    l <- toIRGenerate left
    let returnExpr = 
          (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)))
    tell [(var, l), (var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | extras `hasAlgorithm` "greaterThanRight" = do --p(x | var >= const
    var <- mkVariable "fixed_bound"
    (integrate, _, integrateBranches) <- toIRIntegrate conf left (IRConst (VFloat (-9999999))) (IRVar var)
    var2 <- mkVariable "lhs_integral"
    r <- toIRGenerate right
    let returnExpr = (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)) (IRVar var2))
    tell [(var, r), (var2, integrate)]
    return (returnExpr, const0, integrateBranches)
toIRProbability conf (LessThan (TypeInfo {rType = t, tags = extras}) left right) sample
  --TODO: Find a better lower bound than just putting -9999999
  | extras `hasAlgorithm` "lessThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    (integrate, _, integrateBranches) <- toIRIntegrate conf right (IRVar var) (IRConst (VFloat (9999999)))
    var2 <- mkVariable "rhs_integral"
    l <- toIRGenerate left
    let returnExpr = (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)))
    tell [(var, l), (var2, integrate)]
    return (returnExpr, const0, integrateBranches)
  | extras `hasAlgorithm` "lessThanRight" = do --p(x | var >= const
    var <- mkVariable "fixed_bound"
    (integrate, _, integrateBranches) <- toIRIntegrate conf left (IRVar var) (IRConst (VFloat (9999999)))
    var2 <- mkVariable "lhs_integral"
    r <- toIRGenerate right
    let returnExpr = (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))  (IRVar var2))
    tell [(var, r), (var2, integrate)]
    return (returnExpr, const0, integrateBranches)
toIRProbability conf (MultF (TypeInfo {rType = TFloat, tags = extras}) left right) sample
  | extras `hasAlgorithm` "multLeft" = do
    var <- mkVariable ""
    (rightExpr, rightDim, rightBranches) <- toIRProbability conf right (IROp OpDiv sample (IRVar var))
    let returnExpr = IROp OpDiv rightExpr (IRUnaryOp OpAbs (IRVar var)) 
    l <- toIRGenerate left
    tell [(var, l)]
    return (returnExpr, rightDim, rightBranches)
  | extras `hasAlgorithm` "multRight" = do
    var <- mkVariable ""
    (leftExpr, leftDim, leftBranches) <- toIRProbability conf left (IROp OpDiv sample (IRVar var))
    r <- toIRGenerate right
    let returnExpr = IROp OpDiv leftExpr (IRUnaryOp OpAbs (IRVar var))
    tell [(var, r)]
    return (returnExpr, leftDim, leftBranches)
toIRProbability conf (PlusF (TypeInfo {rType = TFloat, tags = extras}) left right) sample
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    (rightExpr, rightDim, rightBranches) <- toIRProbability conf right (IROp OpSub sample (IRVar var))
    l <- toIRGenerate left
    tell [(var, l)]
    return (rightExpr, rightDim, rightBranches)
  | extras `hasAlgorithm` "plusRight" = do
    var <- mkVariable ""
    (leftExpr, leftDim, leftBranches) <- toIRProbability conf left (IROp OpSub sample (IRVar var))
    r <- toIRGenerate right
    tell [(var, r)]
    return (leftExpr, leftDim, leftBranches)
toIRProbability conf (PlusI (TypeInfo {rType = TInt, tags = extras}) left right) sample
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
      (pLeft, _, _) <- toIRProbability conf left (IRVar enumVar)
      (pRight, _, _) <- toIRProbability conf right (IROp OpSub sample (IRVar enumVar))
      let returnExpr = case topKThreshold conf of
            Nothing -> IRIf (IRElementOf (IROp OpSub sample (IRVar enumVar)) (IRConst (VList enumListR))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
            Just thr -> IRIf (IROp OpAnd (IRElementOf (IROp OpSub sample (IRVar enumVar)) (IRConst (VList enumListR))) (IROp OpGreaterThan pLeft (IRConst (VFloat thr)))) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
      -- TODO correct branch counting
      return (returnExpr, const0, const0)))
    return (IREnumSum enumVar (VList enumListL) $ IRTFst irTuple, const0, const0)
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    (rightExpr, _, rightBranches) <- toIRProbability conf right (IROp OpSub sample (IRVar var))
    l <- toIRGenerate left
    tell [(var, l)]
    return (rightExpr, const0, rightBranches)
toIRProbability conf (ExpF TypeInfo {rType = TFloat} f) sample = do --FIXME correct Inference
  error "deprecated: Use InjF instead"
toIRProbability conf (NegF (TypeInfo {rType = TFloat, tags = extra}) f) sample =
  toIRProbability conf f (IRUnaryOp OpNeg sample)
toIRProbability conf (Not (TypeInfo {rType = TBool}) f) sample =
  toIRProbability conf f (IRUnaryOp OpNot sample)
toIRProbability conf (ReadNN _ name subexpr) sample = do
  mkInput <- toIRGenerate subexpr
  let returnExpr = (IRIndex (IREvalNN name mkInput) sample)
  return (returnExpr, const0, const0)
  --TODO: Assumption that subexpr is det.
toIRProbability conf (Normal t) sample = return (IRDensity IRNormal sample, IRConst $ VFloat 1, const0)
toIRProbability conf (Uniform t) sample = return (IRDensity IRUniform sample, IRConst $ VFloat 1, const0)
--TODO: assumption: These will be top-level lambdas:
toIRProbability conf (Lambda t name subExpr) sample = do
  irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (toIRProbability conf subExpr sample))
  return (IRLambda name irTuple, const0, const0)
toIRProbability conf (Apply _ l v) sample = do
  vIR <- toIRGenerate v
  (lIR, _, _) <- toIRProbability conf l sample -- Dim and BC are irrelevant here. We need to extract these from the return tuple
  if countBranches conf then
    return (IRTFst (IRApply lIR vIR), IRTFst (IRTSnd (IRApply lIR vIR)), IRTSnd (IRTSnd (IRApply lIR vIR)))
  else
    return (IRTFst (IRApply lIR vIR), IRTSnd (IRApply lIR vIR), const0)
toIRProbability conf (Cons _ hdExpr tlExpr) sample = do
  (headP, headDim, headBranches) <- toIRProbability conf hdExpr (IRHead sample)
  (tailP, tailDim, tailBranches) <- toIRProbability conf tlExpr (IRTail sample)
  mult <- (headP, headDim)  `multP` (tailP, tailDim)
  return (IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (fst mult), IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (snd mult), IROp OpPlus headBranches tailBranches)
toIRProbability conf (TCons _ t1Expr t2Expr) sample = do
  (t1P, t1Dim, t1Branches) <- toIRProbability conf t1Expr (IRTFst sample)
  (t2P, t2Dim, t2Branches) <- toIRProbability conf t2Expr (IRTSnd sample)
  mult <- (t1P, t1Dim) `multP` (t2P, t2Dim)
  return (fst mult, snd mult, IROp OpPlus t1Branches t2Branches)
toIRProbability conf (InjF _ name [param]) sample = do
  prefix <- mkVariable ""
  let letInBlock = irMap (uniqueify [v] prefix) (IRLetIn v sample invExpr)
  (paramExpr, paramDim, paramBranches) <- toIRProbability conf param letInBlock
  let returnExpr = IRLetIn v sample (IROp OpMult paramExpr invDerivExpr)
  return (returnExpr, paramDim, paramBranches)
  where Just fPair = lookup name globalFenv   --TODO error handling if nor found
        FPair (_, [inv]) = fPair
        FDecl (_, [v], _, invExpr, [(_, invDerivExpr)]) = inv
toIRProbability conf (InjF TypeInfo {rType=TFloat, tags=extras} name [param1, param2]) sample
  | extras `hasAlgorithm` "injF2Left" = do  --FIXME Left
  let Just fPair = lookup name globalFenv   --TODO error handling if not found
  let FPair (fwd, inversions) = fPair
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v3==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, invDerivs) = invDecl
  let Just invDeriv = lookup v1 invDerivs
  leftExpr <- toIRGenerate param1
  let (detVar, sampleVar) = if x2 == v2 then (x2, x3) else (x3, x2)
  let letInBlock = IRLetIn detVar leftExpr (IRLetIn sampleVar sample invExpr)
  (paramExpr, paramDim, paramBranches) <- toIRProbability conf param2 letInBlock
  let returnExpr = IRLetIn detVar leftExpr (IRLetIn sampleVar sample (IROp OpMult paramExpr invDeriv))
  uniquePrefix <- mkVariable ""
  return (irMap (uniqueify [v1, v2, v3] uniquePrefix) returnExpr, paramDim, paramBranches) --FIXME
toIRProbability conf (InjF TypeInfo {rType=TFloat, tags=extras} name [param1, param2]) sample
  | extras `hasAlgorithm` "injF2Right" = do  --FIXME Left
  let Just fPair = lookup name globalFenv   --TODO error handling if not found
  let FPair (fwd, inversions) = fPair
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v2==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, invDerivs) = invDecl
  let Just invDeriv = lookup v1 invDerivs
  leftExpr <- toIRGenerate param2
  let (detVar, sampleVar) = if x2 == v3 then (x2, x3) else (x3, x2)
  let letInBlock = IRLetIn detVar leftExpr (IRLetIn sampleVar sample invExpr)
  (paramExpr, paramDim, paramBranches) <- toIRProbability conf param1 letInBlock
  let returnExpr = IRLetIn detVar leftExpr (IRLetIn sampleVar sample (IROp OpMult paramExpr invDeriv))
  uniquePrefix <- mkVariable ""
  return (irMap (uniqueify [v1, v2, v3] uniquePrefix) returnExpr, paramDim, paramBranches)
toIRProbability conf (Null _) sample = do
  expr <- indicator (IROp OpEq sample (IRConst $ VList []))
  return (expr, const0, const0)
toIRProbability conf (Constant _ value) sample = do
  expr <- indicator (IROp OpEq sample (IRConst value))
  return (expr, const0, const0)
toIRProbability conf (Call _ name) sample = do
  var <- mkVariable "call"
  tell [(var, IRCall (name ++ "_prob") [sample])]
  if countBranches conf then
      return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
    else
      return (IRTFst (IRVar var), IRTSnd (IRVar var), const0)
toIRProbability conf (ThetaI _ a i) sample = do
  a' <- toIRGenerate a
  expr <- indicator (IROp OpEq sample (IRTheta a' i))
  return (expr, const0, const0)
toIRProbability conf (Subtree _ a i) sample = error "Cannot infer prob on subtree expression. Please check your syntax"
toIRProbability conf x sample = error ("found no way to convert to IR: " ++ show x)

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
           (IRIf (IROp OpGreaterThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar pVarA)
           (IRIf (IROp OpGreaterThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar pVarB)
           (IROp OpPlus (IRVar pVarA) (IRVar pVarB))))),
           -- Dim
           IRIf (IROp OpEq (IRVar pVarA) (IRConst (VFloat 0))) (IRVar dimVarB)
           (IRIf (IROp OpEq (IRVar pVarB) (IRConst (VFloat 0))) (IRVar dimVarA)
           (IRIf (IROp OpGreaterThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar dimVarA)
           (IRIf (IROp OpGreaterThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar dimVarB)
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
         (IRIf (IROp OpGreaterThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar pVarA)
         (IRIf (IROp OpGreaterThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar pVarB)
         (IROp OpSub (IRVar pVarA) (IRVar pVarB))))),
         -- Dim
         IRIf (IROp OpEq (IRVar pVarA) (IRConst (VFloat 0))) (IRVar dimVarB)
         (IRIf (IROp OpEq (IRVar pVarB) (IRConst (VFloat 0))) (IRVar dimVarA)
         (IRIf (IROp OpGreaterThan (IRVar dimVarA) (IRVar dimVarB)) (IRVar dimVarA)
         (IRIf (IROp OpGreaterThan (IRVar dimVarB) (IRVar dimVarA)) (IRVar dimVarB)
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
uniqueify _ _ e = e

--folding detGen and Gen into one, as the distinction is one to make sure things that are det are indeed det.
-- That's what the type system is for though.
toIRGenerate :: Expr -> CompilerMonad  IRExpr
toIRGenerate (IfThenElse _ cond left right) = do
  c <- toIRGenerate cond
  l <- toIRGenerate left
  r <- toIRGenerate right
  return $ IRIf c l r
toIRGenerate (LetIn _ n v b) = do
  v' <- toIRGenerate v
  b' <- toIRGenerate b
  return $ IRLetIn n v' b'
toIRGenerate (GreaterThan _ left right) = do
  l <- toIRGenerate left
  r <- toIRGenerate right
  return $ IROp OpGreaterThan l r
toIRGenerate (LessThan _ left right) = do
  l <- toIRGenerate left
  r <- toIRGenerate right
  return $ IROp OpLessThan l r
toIRGenerate (PlusF _ left right) = do
  l <- toIRGenerate left
  r <- toIRGenerate right
  return $ IROp OpPlus l r
toIRGenerate (PlusI _ left right) = do
  l <- toIRGenerate left
  r <- toIRGenerate right
  return $ IROp OpPlus l r
toIRGenerate (MultF _ left right) = do
  l <- toIRGenerate left
  r <- toIRGenerate right
  return $ IROp OpMult l r
toIRGenerate (MultI _ left right) = do
  l <- toIRGenerate left
  r <- toIRGenerate right
  return $ IROp OpMult l r
toIRGenerate (ExpF _ f) = do
  f' <- toIRGenerate f
  return $ IRUnaryOp OpExp f'
toIRGenerate (NegF _ f) = do
  f' <- toIRGenerate f
  return $ IRUnaryOp OpNeg f'
toIRGenerate (Not _ f) = do
  f' <- toIRGenerate f
  return $ IRUnaryOp OpNot f'
toIRGenerate (ThetaI _ a ix) = do
  a' <- toIRGenerate a
  return $ IRTheta a' ix
toIRGenerate (Subtree _ a ix) = do
  a' <- toIRGenerate a
  return $ IRSubtree a' ix
toIRGenerate (Constant _ x) = return $ IRConst x
toIRGenerate (Null _) = return $ IRConst (VList [])
toIRGenerate (Cons _ hd tl) = do
  h <- toIRGenerate hd
  t <- toIRGenerate tl
  return $ IRCons h t
toIRGenerate (TCons _ t1 t2) = do
  t1' <- toIRGenerate t1
  t2' <- toIRGenerate t2
  return $ IRTCons t1' t2'
toIRGenerate (Uniform _) = return $ IRSample IRUniform
toIRGenerate (Normal _) = return $ IRSample IRNormal
toIRGenerate (Call _ name) = return $ IRCall (name ++ "_gen") []
toIRGenerate (InjF _ name params) = do
  -- Assuming that the logic within packParamsIntoLetinsGen is correct.
  -- You will need to process vars and params, followed by recursive calls to fwdExpr.
  prefix <- mkVariable ""
  letInBlock <- packParamsIntoLetinsGen vars params fwdExpr
  return $ irMap (uniqueify vars prefix) letInBlock
  where
    Just fPair = lookup name globalFenv
    FPair (fwd, _) = fPair
    FDecl (_, vars, _, fwdExpr, _) = fwd
toIRGenerate (Var _ name) = return $ IRVar name
toIRGenerate (Lambda _ name subExpr) = do
  subExpr' <- toIRGenerate subExpr
  return $ IRLambda name subExpr'
toIRGenerate (Apply _ l v) = do
  l' <- toIRGenerate l
  v' <- toIRGenerate v
  return $ IRApply l' v'
toIRGenerate (ReadNN _ name subexpr) = do
  subexpr' <- toIRGenerate subexpr
  return $ IRCall "randomchoice" [IREvalNN name subexpr']
toIRGenerate x = error ("found no way to convert to IRGen: " ++ show x)

packParamsIntoLetinsGen :: [String] -> [Expr] -> IRExpr -> CompilerMonad  IRExpr
packParamsIntoLetinsGen [] [] expr = return $ expr
packParamsIntoLetinsGen [] _ _ = error "More parameters than variables"
packParamsIntoLetinsGen _ [] _ = error "More variables than parameters"
packParamsIntoLetinsGen (v:vars) (p:params) expr = do
  pExpr <- toIRGenerate p
  e <- packParamsIntoLetinsGen vars params expr
  return $ IRLetIn v pExpr e

bindLocal :: String -> IRExpr -> IRExpr -> CompilerMonad  IRExpr
bindLocal namestring binding inEx = do
  varName <- mkVariable namestring
  return $ IRLetIn varName binding inEx

toIRIntegrate :: CompilerConfig -> Expr -> IRExpr -> IRExpr -> CompilerMonad CompilationResult
toIRIntegrate conf (Uniform _) lower higher = do
  return (IROp OpSub (IRCumulative IRUniform higher) (IRCumulative IRUniform lower), const0, const0)
toIRIntegrate conf (Normal TypeInfo {}) lower higher = do
 return (IROp OpSub (IRCumulative IRNormal higher) (IRCumulative IRNormal lower), const0, const0)
toIRIntegrate conf (MultF (TypeInfo {tags = extras}) left right) lower higher
  | extras `hasAlgorithm` "multLeft" = do
    var <- mkVariable ""
    (rightExpr, _, rightBranches) <- toIRIntegrate conf right (IROp OpDiv lower (IRVar var)) (IRUnaryOp OpAbs (IROp OpDiv higher (IRVar var)))
    l <- toIRGenerate left
    tell [(var, l)]
    return (rightExpr, const0, rightBranches)
  | extras `hasAlgorithm` "multRight" = do
      var <- mkVariable ""
      (leftExpr, _, leftBranches) <- toIRIntegrate conf left (IROp OpDiv lower (IRVar var)) (IRUnaryOp OpAbs (IROp OpDiv higher (IRVar var)))
      r <- toIRGenerate right
      tell [(var, r)]
      return (leftExpr, const0, leftBranches)
toIRIntegrate conf (PlusF TypeInfo {tags = extras} left right) lower higher
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    (rightExpr, _, rightBranches) <- toIRIntegrate conf right (IROp OpSub lower (IRVar var)) (IROp OpSub higher (IRVar var))
    l <- toIRGenerate left
    tell [(var, l)]
    return (rightExpr, const0, rightBranches)
  | extras `hasAlgorithm` "plusRight" = do
      var <- mkVariable ""
      (leftExpr, _, leftBranches) <- toIRIntegrate conf left (IROp OpSub lower (IRVar var)) (IROp OpSub higher (IRVar var))
      r <- toIRGenerate right
      tell [(var, r)]
      return (leftExpr, const0, leftBranches)
toIRIntegrate conf (NegF _ a) low high = do
  toIRIntegrate conf a (IRUnaryOp OpNeg high) (IRUnaryOp OpNeg low)
toIRIntegrate conf (ExpF _ a) low high = do
  error "deprecated: Use InjF instead"
toIRIntegrate conf (TCons _ t1Expr t2Expr) low high = do
  (t1P, _,  t1Branches) <- toIRIntegrate conf t1Expr (IRTFst low) (IRTFst high)
  (t2P, _,  t2Branches) <- toIRIntegrate conf t2Expr (IRTSnd low) (IRTSnd high)
  return (IROp OpMult t1P t2P, const0, IROp OpPlus t1Branches t2Branches)
toIRIntegrate conf (IfThenElse _ cond left right) low high = do
  var_cond_p <- mkVariable "cond"
  (condExpr, _, condBranches) <- toIRProbability conf cond (IRConst (VBool True))
  (leftExpr, _, leftBranches) <- toIRIntegrate conf left low high
  (rightExpr, _, rightBranches) <- toIRIntegrate conf right low high
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
toIRIntegrate conf (Cons _ hdExpr tlExpr) low high = do
  (headP, _, headBranches) <- toIRIntegrate conf hdExpr (IRHead low) (IRHead high)
  (tailP, _, tailBranches) <- toIRIntegrate conf tlExpr (IRTail low) (IRTail high)
  return (IRIf (IROp OpOr (IROp OpEq low (IRConst $ VList [])) (IROp OpEq high (IRConst $ VList []))) (IRConst $ VFloat 0) (IROp OpMult headP tailP), const0, IROp OpPlus headBranches tailBranches)
toIRIntegrate conf (Null _) low high = do
  ind <- indicator (IROp OpAnd (IROp OpEq low (IRConst $ VList [])) (IROp OpEq high (IRConst $ VList [])))
  return (ind, const0, const0)
toIRIntegrate conf (Constant _ value) low high = do
  ind <- indicator (IROp OpAnd (IROp OpLessThan low (IRConst value)) (IROp OpGreaterThan high (IRConst value))) --TODO What to do if low and high are equal?
  return (ind, const0, const0)
toIRIntegrate conf (ThetaI _ a i) low high = do
  a' <-  toIRGenerate a
  let val = IRTheta a' i
  ind <- indicator (IROp OpAnd (IROp OpLessThan low val) (IROp OpGreaterThan high val)) --TODO What to do if low and high are equal?
  return (ind, const0, const0)
toIRIntegrate conf (InjF _ name [param]) low high = do  --TODO Multivariable
  prefix <- mkVariable ""
  let letInBlockLow = irMap (uniqueify [v] prefix) (IRLetIn v low invExpr)
  let letInBlockHigh = irMap (uniqueify [v] prefix) (IRLetIn v high invExpr)
  (paramExpr, _, paramBranches) <- toIRIntegrate conf param letInBlockLow letInBlockHigh
  return (paramExpr, const0, paramBranches)
  where Just fPair = lookup name globalFenv   --TODO error handling if nor found
        FPair (_, [inv]) = fPair
        FDecl (_, [v], _, invExpr, [(_, invDerivExpr)]) = inv
toIRIntegrate conf (InjF TypeInfo {rType=TFloat, tags=extras} name [param1, param2]) low high
  | extras `hasAlgorithm` "injF2Left" = do  --FIXME Left
  let Just fPair = lookup name globalFenv   --TODO error handling if not found
  let FPair (fwd, inversions) = fPair
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v3==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, invDerivs) = invDecl
  let Just invDeriv = lookup v1 invDerivs
  leftExpr <- toIRGenerate param1
  let (detVar, sampleVar) = if x2 == v2 then (x2, x3) else (x3, x2)
  let letInBlockLow = IRLetIn detVar leftExpr (IRLetIn sampleVar low invExpr)
  let letInBlockHigh = IRLetIn detVar leftExpr (IRLetIn sampleVar high invExpr)
  (paramExpr, _, paramBranches) <- toIRIntegrate conf param2 letInBlockLow letInBlockHigh
  uniquePrefix <- mkVariable ""
  return (irMap (uniqueify [v1, v2, v3] uniquePrefix) paramExpr, const0, paramBranches)
toIRIntegrate conf (InjF TypeInfo {rType=TFloat, tags=extras} name [param1, param2]) low high
  | extras `hasAlgorithm` "injF2Right" = do  --FIXME Left
  let Just fPair = lookup name globalFenv   --TODO error handling if not found
  let FPair (fwd, inversions) = fPair
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v2==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, invDerivs) = invDecl
  let Just invDeriv = lookup v1 invDerivs
  leftExpr <- toIRGenerate param2
  let (detVar, sampleVar) = if x2 == v3 then (x2, x3) else (x3, x2)
  let letInBlockLow = IRLetIn detVar leftExpr (IRLetIn sampleVar low invExpr)
  let letInBlockHigh = IRLetIn detVar leftExpr (IRLetIn sampleVar high invExpr)
  (paramExpr, _, paramBranches) <- toIRIntegrate conf param1 letInBlockLow letInBlockHigh
  uniquePrefix <- mkVariable ""
  return (irMap (uniqueify [v1, v2, v3] uniquePrefix) paramExpr, const0, paramBranches)
toIRIntegrate conf (Call _ name) low high = do
  var <- mkVariable "call"
  tell [(var, IRCall (name ++ "_integ") [low, high])]
  if countBranches conf then
      return (IRTFst (IRVar var), IRTFst (IRTSnd (IRVar var)), IRTSnd (IRTSnd (IRVar var)))
    else
      return (IRTFst (IRVar var), IRTSnd (IRVar var), const0)
toIRIntegrate conf (Lambda t name subExpr) low high = do
    irTuple <- lift $ return $ generateLetInBlock conf (runWriterT (toIRIntegrate conf subExpr low high))
    return (IRLambda name irTuple, const0, const0)
toIRIntegrate conf (Apply _ l v) low high = do
  vIR <- toIRGenerate v
  (lIR, _, _) <- toIRIntegrate conf l low high -- Dim and BC are irrelevant here. We need to extract these from the return tuple
  if countBranches conf then
    return (IRTFst (IRApply lIR vIR), IRTFst (IRTSnd (IRApply lIR vIR)), IRTSnd (IRTSnd (IRApply lIR vIR)))
  else
    return (IRTFst (IRApply lIR vIR), IRTSnd (IRApply lIR vIR), const0)
toIRIntegrate conf (Var _ n) _ _ = return (IRVar n, const0, const0)
toIRIntegrate _ x _ _ = error ("found no way to convert to IRIntegrate: " ++ show x)

