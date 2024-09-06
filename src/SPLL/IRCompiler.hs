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


-- perhaps as an explicit lambda in the top of the expression, otherwise we'll get trouble generating code.
-- TODO: How do we deal with top-level lambdas in binding here?
--  TL-Lambdas are presumably to be treated differently than non-TL, at least as far as prob is concerned.
--TODO Pull out LetIns
envToIR :: (Ord a, Floating a, Show a, Eq a) => CompilerConfig a -> Program a -> [(String, IRExpr a)]
envToIR conf p = concatMap (\(name, binding) ->
  let pt = pType $ getTypeInfo binding
      rt = rType $ getTypeInfo binding in
    if (pt == Deterministic || pt == Integrate) && (isOnlyNumbers rt) then
      [(name ++ "_integ", (IRLambda "low" (IRLambda "high" (returnize (postProcess $ runSupplyVars (toIRIntegrate conf binding (IRVar "low") (IRVar "high"))))))),
       (name ++ "_prob",(IRLambda "sample" (returnize (postProcess $ runSupplyVars (toIRProbability conf binding (IRVar "sample")))))),
       (name ++ "_gen", (returnize (postProcess $ toIRGenerate binding)))]
    else if pt == Deterministic || pt == Integrate || pt == Prob then
      [(name ++ "_prob", (IRLambda "sample" (returnize (postProcess $ runSupplyVars (toIRProbability conf binding (IRVar "sample")))))),
       (name ++ "_gen", (returnize (postProcess $ toIRGenerate binding)))]
    else
      [(name ++ "_gen", (returnize (postProcess $ toIRGenerate binding)))]) (functions p)
      
isValue :: IRExpr a -> Bool
isValue (IRConst val) = True
isValue _ = False

unval :: IRExpr a -> Value a
unval (IRConst val) = val
unval _ = error "tried to unval a non-val"

--strip all top-level lambdas and collect the bound names.
--unwrapTLLambdas :: Expr t a -> ([Varname], Expr t a)
--unwrapTLLambdas (Lambda _ name subExpr) = (name : innerNames, unwrappedExpr)
--  where (innerNames, unwrappedExpr) = unwrapTLLambdas subExpr
--unwrapTLLambdas expr = ([], expr)

postProcess :: (Show a, Ord a, Fractional a) => IRExpr a -> IRExpr a
postProcess = fixedPointIteration optimize

fixedPointIteration :: (Eq a) => (a -> a) -> a -> a
fixedPointIteration f x = if fx == x then x else fixedPointIteration f fx
  where fx = f x

optimize :: (Show a, Ord a, Fractional a) => IRExpr a -> IRExpr a
optimize = irMap evalAll
--TODO: We can also optimize index magic, potentially here. i.e. a head tail tail x can be simplified.
--TODO: Unary operators
evalAll :: (Show a, Ord a, Fractional a) => IRExpr a -> IRExpr a
evalAll expr@(IROp op leftV rightV)
  | isValue leftV && isValue rightV = IRConst (forceOp op (unval leftV) (unval rightV))
  | isValue leftV || isValue rightV = softForceLogic op leftV rightV
  | otherwise = expr
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
  | scope == IRVar name = val
  | otherwise = ex
evalAll x = x

isSimple :: IRExpr a -> Bool
--isSimple (IRTheta a) = True
isSimple (IRVar a) = True
isSimple (IRConst a) = True
isSimple _ = False

replace :: Eq p => p -> p -> p -> p
replace find replace' expr = if find == expr then replace' else expr

softForceLogic :: Operand -> IRExpr a -> IRExpr a -> IRExpr a
softForceLogic OpOr (IRConst (VBool True)) _ = IRConst (VBool True)
softForceLogic OpOr _ (IRConst (VBool True)) = IRConst (VBool True)
softForceLogic OpOr (IRConst (VBool False)) right = right
softForceLogic OpOr left (IRConst (VBool False)) = left
softForceLogic OpAnd (IRConst (VBool True)) right = right
softForceLogic OpAnd left (IRConst (VBool True)) = left
softForceLogic OpAnd (IRConst (VBool False)) _ = IRConst (VBool False)
softForceLogic OpAnd _ (IRConst (VBool False)) = IRConst (VBool False)
softForceLogic op left right = IROp op left right     -- Nothing can be done

forceOp :: (Ord a, Fractional a) => Operand -> Value a -> Value a -> Value a
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
forceOp OpGreaterThan (VInt x) (VInt y) = VBool (x >= y)
forceOp OpGreaterThan (VFloat x) (VFloat y) = VBool (x >= y)
forceOp OpLessThan (VInt x) (VInt y) = VBool (x <= y)
forceOp OpLessThan (VFloat x) (VFloat y) = VBool (x <= y)

returnize :: IRExpr a -> IRExpr a
returnize (IRIf cond left right) = IRIf cond (returnize left) (returnize right)
returnize (IRReturning expr) = error "called returnize on return statement"
returnize (IRLetIn name binding scope) = IRLetIn name binding (returnize scope)
returnize (IRLambda name expr) = IRLambda name (returnize expr)
returnize other = IRReturning other

pullOutLetIns :: IRExpr a -> IRExpr a
pullOutLetIns (IRLambda n b) = IRLambda n (pullOutLetIns b)
pullOutLetIns (IRLetIn n v b) = IRLetIn n v (pullOutLetIns b)
pullOutLetIns e = runSupplyVars $ do
  case findLetIn e of
    Just (IRLetIn n v b) -> do
      i <- demand
      let newName = n ++ show i
      let newBody = pullOutLetIns (removeAndSubstituteLetIns b n newName)
      return (IRLetIn newName v newBody)
    Nothing -> return e

-- TODO: We currently dont handle inner lambdas here
findLetIn :: IRExpr a -> Maybe (IRExpr a)
findLetIn IRLambda {} = Nothing
findLetIn e@(IRLetIn _ _ _) = Just e
findLetIn e = firstJusts (map findLetIn (getIRSubExprs e))
  where firstJusts l = foldr (\a b -> if isJust a then a else b) Nothing l

removeAndSubstituteLetIns :: IRExpr a -> Varname -> Varname -> IRExpr a
removeAndSubstituteLetIns (IRVar a) old new | old == a = IRVar new
removeAndSubstituteLetIns e old new = irMap (removeSubst old new) e
  where
    removeSubst oldN newN (IRVar n) | n == oldN = IRVar newN
    removeSubst oldN _ (IRLetIn n _ b) | n == oldN = b
    removeSubst _ _ ex = ex


runSupplyVars :: Supply Int a -> a
runSupplyVars codeGen = runSupply codeGen (+1) 1

mkVariable :: String -> Supply Int Varname
mkVariable suffix = do
  varID <- demand
  return ("l_" ++ show varID ++ "_" ++ suffix)

hasAlgorithm :: [Tag a] -> String -> Bool
hasAlgorithm tags alg = alg `elem` ([algName a | Alg a <- tags])
--hasAlgorithm tags alg = not $ null $ filter (== alg) [a | Alg a <- tags]

--in this implementation, I'll forget about the distinction between PDFs and Probabilities. Might need to fix that later.
toIRProbability :: (Floating a, Show a) => CompilerConfig a -> Expr a -> IRExpr a -> Supply Int (IRExpr a)
toIRProbability conf (IfThenElse t cond left right) sample = do
  var_cond_p <- mkVariable "cond"
  condExpr <- toIRProbability conf cond (IRConst (VBool True))
  leftExpr <- toIRProbability conf left sample
  rightExpr <- toIRProbability conf right sample
  -- p(y) = if p_cond < thresh then p_else(y) * (1-p_cond(y)) else if p_cond > 1 - thresh then p_then(y) * p_cond(y) else p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
  let thr = topKThreshold conf
  case thr of
    Just thresh -> do
      if countBranches conf then do
        let unpackedCond = IRTFst condExpr
        leftPropagated <- mkVariable "left"
        rightPropagated <- mkVariable "right"
        let leftE = IRTFst (IRVar leftPropagated)
        let rightE = IRTFst (IRVar rightPropagated)
        let leftCnt = IRTSnd (IRVar leftPropagated)
        let rightCnt = IRTSnd (IRVar rightPropagated)
        let propagateOnlyRight = IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p)) rightE
        let propagateOnlyLeft = IROp OpMult (IRVar var_cond_p) leftE
        let propagateBoth = IROp OpPlus
              (IROp OpMult (IRVar var_cond_p) leftE)
              (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p)) rightE)
        return (IRLetIn leftPropagated leftExpr (IRLetIn rightPropagated rightExpr
          (IRLetIn var_cond_p unpackedCond
            (IRIf (IROp OpLessThan (IRVar var_cond_p) (IRConst (VFloat thresh)))
              (IRTCons propagateOnlyRight rightCnt)
              (IRIf (IROp OpGreaterThan (IRVar var_cond_p) (IRConst (VFloat (1-thresh))))
                (IRTCons propagateOnlyLeft leftCnt)
                (IRTCons propagateBoth (IROp OpPlus (IRConst (VFloat 1)) (IROp OpPlus leftCnt rightCnt))))))))
      else
        return (IRLetIn var_cond_p condExpr
          (IRIf (IROp OpLessThan (IRVar var_cond_p) (IRConst (VFloat thresh)))
            (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr)
            (IRIf (IROp OpGreaterThan (IRVar var_cond_p) (IRConst (VFloat (1-thresh))))
              (IROp OpMult (IRVar var_cond_p) leftExpr)
              (IROp OpPlus
                (IROp OpMult (IRVar var_cond_p) leftExpr)
                (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr)))))
    -- p(y) = p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
    Nothing -> do
      if countBranches conf then do
        let unpackedCond = IRTFst condExpr
        leftPropagated <- mkVariable "left"
        rightPropagated <- mkVariable "right"
        let leftE = IRTFst (IRVar leftPropagated)
        let rightE = IRTFst (IRVar rightPropagated)
        let leftCnt = IRTSnd (IRVar leftPropagated)
        let rightCnt = IRTSnd (IRVar rightPropagated)
        return $ IRLetIn leftPropagated leftExpr (IRLetIn rightPropagated rightExpr
          (IRTCons (IRLetIn var_cond_p unpackedCond
            (IROp OpPlus
              (IROp OpMult (IRVar var_cond_p) leftE)
              (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightE))) (IROp OpPlus (IRConst (VFloat 1)) (IROp OpPlus leftCnt rightCnt))))
      else
        return $ IRLetIn var_cond_p condExpr
          (IROp OpPlus
            (IROp OpMult (IRVar var_cond_p) leftExpr)
            (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr))
toIRProbability conf (GreaterThan (TypeInfo {rType = t, tags = extras}) left right) sample
  --TODO: Find a better lower bound than just putting -9999999
  | extras `hasAlgorithm` "greaterThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    integrate <- toIRIntegrate conf right (IRConst (VFloat (-9999999))) (IRVar var)
    var2 <- mkVariable "rhs_integral"
    propagated <- propagateBranchCount1 conf (\p -> (IRLetIn var2 p
      (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))))) integrate
    return $ IRLetIn var (toIRGenerate left) propagated
  | extras `hasAlgorithm` "greaterThanRight" = do --p(x | var >= const
    var <- mkVariable "fixed_bound"
    integrate <- toIRIntegrate conf left (IRConst (VFloat (-9999999))) (IRVar var)
    var2 <- mkVariable "lhs_integral"
    propagated <- propagateBranchCount1 conf (\p -> (IRLetIn var2 p
      (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)) (IRVar var2) ))) integrate
    return $  IRLetIn var (toIRGenerate right) propagated
toIRProbability conf (LessThan (TypeInfo {rType = t, tags = extras}) left right) sample
  --TODO: Find a better lower bound than just putting -9999999
  | extras `hasAlgorithm` "lessThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    integrate <- toIRIntegrate conf right (IRVar var) (IRConst (VFloat (9999999)))
    var2 <- mkVariable "rhs_integral"
    propagateBranchCount1 conf (\p -> IRLetIn var (toIRGenerate left)
      (IRLetIn var2 p
        (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))))) integrate
  | extras `hasAlgorithm` "lessThanRight" = do --p(x | var >= const
    var <- mkVariable "fixed_bound"
    integrate <- toIRIntegrate conf left (IRVar var) (IRConst (VFloat (9999999)))
    var2 <- mkVariable "lhs_integral"
    propagateBranchCount1 conf (\p -> IRLetIn var (toIRGenerate right)
      (IRLetIn var2 p
        (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))  (IRVar var2)))) integrate
toIRProbability conf (MultF (TypeInfo {rType = TFloat, tags = extras}) left right) sample
  | extras `hasAlgorithm` "multLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRProbability conf right (IROp OpDiv sample (IRVar var))
    propagated <- propagateBranchCount1 conf (\p -> IROp OpDiv p (IRUnaryOp OpAbs (IRVar var))) rightExpr
    return $ IRLetIn var (toIRGenerate left) propagated
  | extras `hasAlgorithm` "multRight" = do
    var <- mkVariable ""
    leftExpr <- toIRProbability conf left (IROp OpDiv sample (IRVar var))
    propagated <- propagateBranchCount1 conf (\p -> IROp OpDiv p (IRUnaryOp OpAbs (IRVar var))) leftExpr
    return $ IRLetIn var (toIRGenerate right) propagated
toIRProbability conf (PlusF (TypeInfo {rType = TFloat, tags = extras}) left right) sample
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRProbability conf right (IROp OpSub sample (IRVar var))
    propagated <- propagateBranchCount1 conf id rightExpr
    return $ IRLetIn var (toIRGenerate left) propagated
  | extras `hasAlgorithm` "plusRight" = do
    var <- mkVariable ""
    leftExpr <- toIRProbability conf left (IROp OpSub sample (IRVar var))
    propagated <- propagateBranchCount1 conf id leftExpr
    return $ IRLetIn var (toIRGenerate right) propagated
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
    --the subexpr in the loop must compute p(enumVar| left) * p(inverse | right)
    pLeft <- toIRProbability conf left (IRVar enumVar)
    pRight <- toIRProbability conf right (IROp OpSub sample (IRVar enumVar))
    propagateBranchCount2 conf (\p1 p2 -> IREnumSum enumVar (VList enumListL) $ IRIf (IRCall "in" [IROp OpSub sample (IRVar enumVar), IRConst (VList enumListR)]) (IROp OpMult p1 p2) (IRConst (VFloat 0))) pLeft pRight
    -- TODO correct branch counting
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRProbability conf right (IROp OpSub sample (IRVar var))
    propagated <- propagateBranchCount1 conf id rightExpr
    return $ IRLetIn var (toIRGenerate left) propagated
toIRProbability conf (ExpF TypeInfo {rType = TFloat} f) sample = do --FIXME correct Inference
  error "deprecated: Use InjF instead"
toIRProbability conf (NegF (TypeInfo {rType = TFloat, tags = extra}) f) sample =
  toIRProbability conf f (IRUnaryOp OpNeg sample)
toIRProbability conf (Not (TypeInfo {rType = TBool}) f) sample =
  toIRProbability conf f (IRUnaryOp OpNot sample)
toIRProbability conf (ReadNN _ name subexpr) sample = do
  let mkInput = toIRGenerate subexpr
  propagateBranchCount0 conf (IRIndex (IREvalNN name mkInput) sample)
  --TODO: Assumption that subexpr is det.
toIRProbability conf (Normal t) sample = propagateBranchCount0 conf (IRDensity IRNormal sample)
toIRProbability conf (Uniform t) sample = propagateBranchCount0 conf (IRDensity IRUniform sample)
--TODO: assumption: These will be top-level lambdas:
toIRProbability conf (Lambda t name subExpr) sample = do
  subExprIR <- toIRProbability conf subExpr sample
  propagateBranchCount1 conf (\p -> IRLambda name p) subExprIR
toIRProbability conf (Apply _ l v) sample = do
  let vIR = toIRGenerate v
  lIR <- toIRProbability conf l sample
  propagateBranchCount1 conf (\p -> IRApply p vIR) lIR
toIRProbability conf (Cons _ hdExpr tlExpr) sample = do
  headP <- toIRProbability conf hdExpr (IRHead sample)
  tailP <- toIRProbability conf tlExpr (IRTail sample)
  propagateBranchCount2 conf (\p1 p2 -> IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (IROp OpMult p1 p2)) headP tailP
toIRProbability conf (TCons _ t1Expr t2Expr) sample = do
  t1P <- toIRProbability conf t1Expr (IRTFst sample)
  t2P <- toIRProbability conf t2Expr (IRTSnd sample)
  propagateBranchCount2 conf (\p1 p2 -> IROp OpMult p1 p2) t1P t2P
toIRProbability conf (InjF _ name [param]) sample = do  --TODO Multivariable
  let letInBlock = IRLetIn v sample invExpr
  paramExpr <- toIRProbability conf param letInBlock
  propagateBranchCount1 conf (\p -> IRLetIn v sample (IROp OpMult p invDerivExpr)) paramExpr
  where Just fPair = lookup name globalFenv   --TODO error handling if nor found
        FPair (_, [inv]) = fPair
        FDecl (_, [v], _, invExpr, [(_, invDerivExpr)]) = inv
toIRProbability conf (InjF TypeInfo {rType=TFloat, tags=extras} name [param1, param2]) sample
  | extras `hasAlgorithm` "injF2Left" = do  --FIXME Left
  let Just fPair = lookup name globalFenv   --TODO error handling if nor found
  let FPair (fwd, inversions) = fPair
  let FDecl (_, [v2, v3], [v1], _, _) = fwd
  let [invDecl] = filter (\(FDecl (_, _, [w1], _, _)) -> v3==w1) inversions   --This should only return one inversion
  let FDecl (_, [x2, x3], _, invExpr, invDerivs) = invDecl
  let Just invDeriv = lookup v1 invDerivs
  let leftExpr = toIRGenerate param1
  let (detVar, sampleVar) = if x2 == v2 then (x2, x3) else (x3, x2)
  let letInBlock = IRLetIn detVar leftExpr (IRLetIn sampleVar sample invExpr)
  paramExpr <- toIRProbability conf param2 letInBlock
  propagateBranchCount1 conf (\p -> IRLetIn detVar leftExpr (IRLetIn sampleVar sample (IROp OpMult p invDeriv))) paramExpr
toIRProbability conf (Null _) sample = do
  expr <- indicator (IROp OpEq sample (IRConst $ VList []))
  propagateBranchCount0 conf expr
toIRProbability conf (Constant _ value) sample = do
  expr <- indicator (IROp OpEq sample (IRConst value))
  propagateBranchCount0 conf expr
toIRProbability conf (Call _ name) sample = return $ IRCall (name ++ "_prob") [sample]
toIRProbability conf (ThetaI _ a i) sample = do
  expr <- indicator (IROp OpEq sample (IRTheta (toIRGenerate a) i))
  propagateBranchCount0 conf expr
toIRProbability conf (Subtree _ a i) sample = error "Cannot infer prob on subtree expression. Please check your syntax"
toIRProbability conf x sample = error ("found no way to convert to IR: " ++ show x)

propagateBranchCount0 :: (Num a) => CompilerConfig a -> IRExpr a -> Supply Int (IRExpr a)
propagateBranchCount0 CompilerConfig {countBranches = False} expr = return expr
propagateBranchCount0 CompilerConfig {countBranches = True} expr = return $ IRTCons expr (IRConst $ VFloat 0)

propagateBranchCount1 :: (Num a) => CompilerConfig a -> (IRExpr a -> IRExpr a) -> IRExpr a -> Supply Int (IRExpr a)
propagateBranchCount1 CompilerConfig {countBranches = False} expr param = return $ expr param
propagateBranchCount1 CompilerConfig {countBranches = True} expr param = do
  pVar <- mkVariable "param"
  let pExpr = IRTFst (IRVar pVar)
  let pCnt = IRTSnd (IRVar pVar)
  return $ IRLetIn pVar param (IRTCons (expr pExpr) pCnt)

propagateBranchCount2 :: (Num a) => CompilerConfig a -> (IRExpr a -> IRExpr a -> IRExpr a) -> IRExpr a ->  IRExpr a -> Supply Int (IRExpr a)
propagateBranchCount2 CompilerConfig {countBranches = False} expr param1 param2 = return $ expr param1 param2
propagateBranchCount2 CompilerConfig {countBranches = True} expr param1 param2 = do
  pVar1 <- mkVariable "param"
  let pExpr1 = IRTFst (IRVar pVar1)
  let pCnt1 = IRTSnd (IRVar pVar1)
  pVar2 <- mkVariable "param"
  let pExpr2 = IRTFst (IRVar pVar2)
  let pCnt2 = IRTSnd (IRVar pVar2)
  return $ IRLetIn pVar1 param1 (IRLetIn pVar2 param2 (IRTCons (expr pExpr1 pExpr2) (IROp OpPlus pCnt1 pCnt2)))

packParamsIntoLetinsProb :: (Show a, Floating a) => [String] -> [Expr a] -> IRExpr a -> IRExpr a -> Supply Int (IRExpr a)
--packParamsIntoLetinsProb [] [] expr _ = do
--  return expr
--packParamsIntoLetinsProb [] _ _ _ = error "More parameters than variables"
--packParamsIntoLetinsProb _ [] _ _ = error "More variables than parameters"
--packParamsIntoLetinsProb (v:vars) (p:params) expr sample = do
--  e <- packParamsIntoLetinsProb vars params expr sample
--  return $ IRLetIn v sample e --TODO sample austauschen durch teil von sample falls multivariable
packParamsIntoLetinsProb [v] [p] expr sample = do
  return $ IRLetIn v sample expr    --FIXME sample to auch toIRProbt werden

indicator :: Num a => IRExpr a -> Supply Int (IRExpr a)
indicator condition = return $ IRIf condition (IRConst $ VFloat 1) (IRConst $ VFloat 0)

--folding detGen and Gen into one, as the distinction is one to make sure things that are det are indeed det.
-- That's what the type system is for though.
toIRGenerate :: (Show a, Floating a) => Expr a -> IRExpr a
toIRGenerate (IfThenElse _ cond left right) = IRIf (toIRGenerate cond) (toIRGenerate left) (toIRGenerate right)
toIRGenerate (LetIn _ n v b) = IRLetIn n (toIRGenerate v) (toIRGenerate b)
toIRGenerate (GreaterThan _ left right) = IROp OpGreaterThan (toIRGenerate left) (toIRGenerate right)
toIRGenerate (LessThan _ left right) = IROp OpLessThan (toIRGenerate left) (toIRGenerate right)
toIRGenerate (PlusF _ left right) = IROp OpPlus (toIRGenerate left) (toIRGenerate right)
toIRGenerate (PlusI _ left right) = IROp OpPlus (toIRGenerate left) (toIRGenerate right)
toIRGenerate (MultF _ left right) = IROp OpMult (toIRGenerate left) (toIRGenerate right)
toIRGenerate (MultI _ left right) = IROp OpMult (toIRGenerate left) (toIRGenerate right)
toIRGenerate (ExpF _ f) = IRUnaryOp OpExp (toIRGenerate f)
toIRGenerate (NegF _ f) = IRUnaryOp OpNeg (toIRGenerate f)
toIRGenerate (Not _ f) = IRUnaryOp OpNot (toIRGenerate f)
toIRGenerate (ThetaI _ a ix) = IRTheta (toIRGenerate a) ix
toIRGenerate (Subtree _ a ix) = IRSubtree (toIRGenerate a) ix
toIRGenerate (Constant _ x) = IRConst x
toIRGenerate (Null _) = IRConst (VList [])
toIRGenerate (Cons _ hd tl) = IRCons (toIRGenerate hd) (toIRGenerate tl)
toIRGenerate (TCons _ t1 t2) = IRTCons (toIRGenerate t1) (toIRGenerate t2)
toIRGenerate (Uniform _) = IRSample IRUniform
toIRGenerate (Normal _) = IRSample IRNormal
--The following assumes that "name" refers to a function defined within the program.
toIRGenerate (Call _ name) = IRCall (name ++ "_gen") []
toIRGenerate (InjF _  name params) = packParamsIntoLetinsGen vars params fwdExpr 
  where Just fPair = lookup name globalFenv
        FPair (fwd, _) = fPair
        FDecl (_, vars, _, fwdExpr, _) = fwd
toIRGenerate (Var _ name) = IRVar name
toIRGenerate (Lambda t name subExpr) = IRLambda name (toIRGenerate subExpr)
toIRGenerate (Apply _ l v) = IRApply (toIRGenerate l) (toIRGenerate v)
toIRGenerate (ReadNN t name subexpr) = IRCall "randomchoice" [IREvalNN name (toIRGenerate subexpr)]
toIRGenerate x = error ("found no way to convert to IRGen: " ++ show x)

packParamsIntoLetinsGen :: (Show a, Floating a) => [String] -> [Expr a] -> IRExpr a -> IRExpr a
packParamsIntoLetinsGen [] [] expr = expr
packParamsIntoLetinsGen [] _ _ = error "More parameters than variables"
packParamsIntoLetinsGen _ [] _ = error "More variables than parameters"
packParamsIntoLetinsGen (v:vars) (p:params) expr = IRLetIn v pExpr e
  where pExpr = toIRGenerate p
        e = packParamsIntoLetinsGen vars params expr

bindLocal :: String -> IRExpr a -> IRExpr a -> Supply Int (IRExpr a)
bindLocal namestring binding inEx = do
  varName <- mkVariable namestring
  return $ IRLetIn varName binding inEx

toIRIntegrate :: (Show a, Floating a) => CompilerConfig a -> Expr a -> IRExpr a -> IRExpr a -> Supply Int (IRExpr a)
toIRIntegrate conf (Uniform _) lower higher = do
  propagateBranchCount0 conf (IROp OpSub (IRCumulative IRUniform higher) (IRCumulative IRUniform lower))
toIRIntegrate conf (Normal TypeInfo {}) lower higher = do
  propagateBranchCount0 conf (IROp OpSub (IRCumulative IRNormal higher) (IRCumulative IRNormal lower))
toIRIntegrate conf (MultF (TypeInfo {tags = extras}) left right) lower higher
  | extras `hasAlgorithm` "multLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRIntegrate conf right (IROp OpDiv lower (IRVar var)) (IRUnaryOp OpAbs (IROp OpDiv higher (IRVar var)))
    propagateBranchCount1 conf (\p -> IRLetIn var (toIRGenerate left) p) rightExpr
  | extras `hasAlgorithm` "multRight" = do
      var <- mkVariable ""
      leftExpr <- toIRIntegrate conf left (IROp OpDiv lower (IRVar var)) (IRUnaryOp OpAbs (IROp OpDiv higher (IRVar var)))
      propagateBranchCount1 conf (\p -> IRLetIn var (toIRGenerate right) p) leftExpr
toIRIntegrate conf (PlusF TypeInfo {tags = extras} left right) lower higher
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRIntegrate conf right (IROp OpSub lower (IRVar var)) (IROp OpSub higher (IRVar var))
    propagateBranchCount1 conf (\p -> IRLetIn var (toIRGenerate left) p) rightExpr
  | extras `hasAlgorithm` "plusRight" = do
      var <- mkVariable ""
      leftExpr <- toIRIntegrate conf left (IROp OpSub lower (IRVar var)) (IROp OpSub higher (IRVar var))
      propagateBranchCount1 conf (\p -> IRLetIn var (toIRGenerate right) p) leftExpr
toIRIntegrate conf (NegF _ a) low high = do
  toIRIntegrate conf a (IRUnaryOp OpNeg high) (IRUnaryOp OpNeg low)
toIRIntegrate conf (ExpF _ a) low high = do
  error "deprecated: Use InjF instead"
toIRIntegrate conf (TCons _ t1Expr t2Expr) low high = do
  t1P <- toIRIntegrate conf t1Expr (IRTFst low) (IRTFst high)
  t2P <- toIRIntegrate conf t2Expr (IRTSnd low) (IRTSnd high)
  propagateBranchCount2 conf (\p1 p2 -> (IROp OpMult p1 p2)) t1P t2P
toIRIntegrate conf (IfThenElse _ cond left right) low high = do
  var_cond_p <- mkVariable "cond"
  condExpr <- toIRProbability conf cond (IRConst (VBool True))
  leftExpr <- toIRIntegrate conf left low high
  rightExpr <- toIRIntegrate conf right low high
  let thr = topKThreshold conf
  case thr of
    Just thresh -> do
      if countBranches conf then do
        let unpackedCond = IRTFst condExpr
        leftPropagated <- mkVariable "left"
        rightPropagated <- mkVariable "right"
        let leftE = IRTFst (IRVar leftPropagated)
        let rightE = IRTFst (IRVar rightPropagated)
        let leftCnt = IRTSnd (IRVar leftPropagated)
        let rightCnt = IRTSnd (IRVar rightPropagated)
        let propagateOnlyRight = IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p)) rightE
        let propagateOnlyLeft = IROp OpMult (IRVar var_cond_p) leftE
        let propagateBoth = IROp OpPlus
              (IROp OpMult (IRVar var_cond_p) leftE)
              (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p)) rightE)
        return (IRLetIn leftPropagated leftExpr (IRLetIn rightPropagated rightExpr
          (IRLetIn var_cond_p unpackedCond
            (IRIf (IROp OpLessThan (IRVar var_cond_p) (IRConst (VFloat thresh)))
              (IRTCons propagateOnlyRight rightCnt)
              (IRIf (IROp OpGreaterThan (IRVar var_cond_p) (IRConst (VFloat (1-thresh))))
                (IRTCons propagateOnlyLeft leftCnt)
                (IRTCons propagateBoth (IROp OpPlus (IRConst (VFloat 1)) (IROp OpPlus leftCnt rightCnt))))))))
      else
        return (IRLetIn var_cond_p condExpr
          (IRIf (IROp OpLessThan (IRVar var_cond_p) (IRConst (VFloat thresh)))
            (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr)
            (IRIf (IROp OpGreaterThan (IRVar var_cond_p) (IRConst (VFloat (1-thresh))))
              (IROp OpMult (IRVar var_cond_p) leftExpr)
              (IROp OpPlus
                (IROp OpMult (IRVar var_cond_p) leftExpr)
                (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr)))))
    -- p(y) = p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
    Nothing -> do
      if countBranches conf then do
        let unpackedCond = IRTFst condExpr
        leftPropagated <- mkVariable "left"
        rightPropagated <- mkVariable "right"
        let leftE = IRTFst (IRVar leftPropagated)
        let rightE = IRTFst (IRVar rightPropagated)
        let leftCnt = IRTSnd (IRVar leftPropagated)
        let rightCnt = IRTSnd (IRVar rightPropagated)
        return $ IRLetIn leftPropagated leftExpr (IRLetIn rightPropagated rightExpr
          (IRTCons (IRLetIn var_cond_p unpackedCond
            (IROp OpPlus
              (IROp OpMult (IRVar var_cond_p) leftE)
              (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightE))) (IROp OpPlus (IRConst (VFloat 1)) (IROp OpPlus leftCnt rightCnt))))
      else
        return $ IRLetIn var_cond_p condExpr
          (IROp OpPlus
            (IROp OpMult (IRVar var_cond_p) leftExpr)
            (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr))
toIRIntegrate conf (Cons _ hdExpr tlExpr) low high = do
  headP <- toIRIntegrate conf hdExpr (IRHead low) (IRHead high)
  tailP <- toIRIntegrate conf tlExpr (IRTail low) (IRTail high)
  propagateBranchCount2 conf (\p1 p2 -> (IRIf (IROp OpOr (IROp OpEq low (IRConst $ VList [])) (IROp OpEq high (IRConst $ VList []))) (IRConst $ VFloat 0) (IROp OpMult p1 p2))) headP tailP
toIRIntegrate conf (Null _) low high = do
  ind <- indicator (IROp OpAnd (IROp OpEq low (IRConst $ VList [])) (IROp OpEq high (IRConst $ VList [])))
  propagateBranchCount0 conf ind
toIRIntegrate conf (Constant _ value) low high = do
  ind <- indicator (IROp OpAnd (IROp OpLessThan low (IRConst value)) (IROp OpGreaterThan high (IRConst value))) --TODO What to do if low and high are equal?
  propagateBranchCount0 conf ind
toIRIntegrate conf (ThetaI _ a i) low high = do
  let val = IRTheta (toIRGenerate a) i
  ind <- indicator (IROp OpAnd (IROp OpLessThan low val) (IROp OpGreaterThan high val)) --TODO What to do if low and high are equal?
  propagateBranchCount0 conf ind
toIRIntegrate conf (InjF _ name params) low high = do  --TODO Multivariable
  let letInBlockLow = IRLetIn v low invExpr
  let letInBlockHigh = IRLetIn v high invExpr
  paramExpr <- toIRIntegrate conf param letInBlockLow letInBlockHigh
  propagateBranchCount1 conf id paramExpr
  where Just fPair = lookup name globalFenv
        FPair (_, [inv]) = fPair
        FDecl (_, [v], _, invExpr, _) = inv
        [param] = params
toIRIntegrate conf (Call _ name) low high = propagateBranchCount0 conf (IRCall (name ++ "_integ") [low, high])
toIRIntegrate conf (Lambda t name subExpr) low high = do
  subExprIR <- toIRIntegrate conf subExpr low high
  propagateBranchCount1 conf (\p -> IRLambda name p) subExprIR
toIRIntegrate conf (Apply _ l v) low high = do
  let vIR = toIRGenerate v
  lIR <- toIRIntegrate conf l low high
  propagateBranchCount1 conf (\p -> IRApply p vIR) lIR
toIRIntegrate conf (Var _ n) _ _ = propagateBranchCount0 conf (IRVar n)
toIRIntegrate _ x _ _ = error ("found no way to convert to IRIntegrate: " ++ show x)

