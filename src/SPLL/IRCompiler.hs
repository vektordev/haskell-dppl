module SPLL.IRCompiler where

import SPLL.IntermediateRepresentation
import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import PredefinedFunctions
import Control.Monad.Supply
import SPLL.Typing.PType 
import SPLL.InferenceRule (algName)


-- perhaps as an explicit lambda in the top of the expression, otherwise we'll get trouble generating code.
-- TODO: How do we deal with top-level lambdas in binding here?
--  TL-Lambdas are presumably to be treated differently than non-TL, at least as far as prob is concerned.
envToIR :: (Ord a, Floating a, Show a, Eq a) => Env (StaticAnnotations a) a -> [(String, IRExpr a)]
envToIR = concatMap (\(name, binding) ->
  let (StaticAnnotations _ pType _) = getTypeInfo binding in
    if pType == Deterministic || pType == Integrate then
      [(name ++ "_integ", IRLambda "low" (IRLambda "high" (postProcess $ runSupplyVars (toIRIntegrate binding (IRVar "low") (IRVar "high"))))),
       (name ++ "_prob", IRLambda "sample" (postProcess $ runSupplyVars (toIRProbability binding (IRVar "sample")))),
       (name ++ "_gen", postProcess $ toIRGenerate binding)]
    else if pType == Prob then
      [(name ++ "_prob", IRLambda "sample" (postProcess $ runSupplyVars (toIRProbability binding (IRVar "sample")))),
       (name ++ "_gen", postProcess $ toIRGenerate binding)]
    else
      [(name ++ "_gen", postProcess $ toIRGenerate binding)])
      
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
isSimple (IRTheta a) = True
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
returnize other = IRReturning other

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
toIRProbability :: (Floating a, Show a) => Expr (StaticAnnotations a) a -> IRExpr a -> Supply Int (IRExpr a)
toIRProbability (IfThenElse t cond left right) sample = do
  var_cond_p <- mkVariable "cond"
  condExpr <- toIRProbability cond (IRConst (VBool True))
  leftExpr <- toIRProbability left sample
  rightExpr <- toIRProbability right sample
  return $ IRLetIn var_cond_p condExpr
    (IROp OpPlus
      (IROp OpMult (IRVar var_cond_p) leftExpr)
      (IROp OpMult (IROp OpSub (IRConst $ VFloat (1.0)) (IRVar var_cond_p) ) rightExpr))
toIRProbability (GreaterThan (StaticAnnotations t _ extras) left right) sample
  --TODO: Find a better lower bound than just putting -9999999
  | extras `hasAlgorithm` "greaterThanLeft" = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    integrate <- toIRIntegrate right (IRConst (VFloat (-9999999))) (IRVar var)
    var2 <- mkVariable "rhs_integral"
    return $ IRLetIn var (toIRGenerate left)
      (IRLetIn var2 integrate
        (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IRVar var2) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2))))
  | extras `hasAlgorithm` "greaterThanRight" = do --p(x | var >= const
    var <- mkVariable "fixed_bound"
    integrate <- toIRIntegrate left (IRConst (VFloat (-9999999))) (IRVar var)
    var2 <- mkVariable "lhs_integral"
    return $ IRLetIn var (toIRGenerate right)
      (IRLetIn var2 integrate
        (IRIf (IROp OpEq (IRConst $ VBool True) sample) (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var2)) (IRVar var2) ))
toIRProbability (MultF (StaticAnnotations TFloat _ extras) left right) sample
  | extras `hasAlgorithm` "multLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRProbability right (IROp OpDiv sample (IRVar var))
    return $ IRLetIn var (toIRGenerate left)
      (IROp OpDiv rightExpr (IRUnaryOp OpAbs (IRVar var)))
  | extras `hasAlgorithm` "multRight" = do
    var <- mkVariable ""
    leftExpr <- toIRProbability left (IROp OpDiv sample (IRVar var))
    return $ IRLetIn var (toIRGenerate right)
      (IROp OpDiv leftExpr (IRUnaryOp OpAbs (IRVar var)))
toIRProbability (PlusF (StaticAnnotations TFloat _ extras) left right) sample
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRProbability right (IROp OpSub sample (IRVar var))
    return $ IRLetIn var (toIRGenerate left) rightExpr
  | extras `hasAlgorithm` "plusRight" = do
    var <- mkVariable ""
    leftExpr <- toIRProbability left (IROp OpSub sample (IRVar var))
    return $ IRLetIn var (toIRGenerate right) leftExpr
toIRProbability (PlusI (StaticAnnotations TInt _ extras) left right) sample
  | extras `hasAlgorithm` "enumeratePlusLeft" = do
    --Solving enumPlusLeft works by enumerating all left hand side choices.
    -- We then invert the addition to infer the right hand side.
    -- TODO: Theoretical assessment whether there's a performance or other difference between enumLeft and enumRight.
    let StaticAnnotations _ _ extrasLeft = getTypeInfo left
    let StaticAnnotations _ _ extrasRight = getTypeInfo right
    let enumListL = head $ [x | EnumList x <- extrasLeft]
    let enumListR = head $ [x | EnumList x <- extrasRight]
    enumVar <- mkVariable "enum"
    --the subexpr in the loop must compute p(enumVar| left) * p(inverse | right)
    pLeft <- toIRProbability left (IRVar enumVar)
    pRight <- toIRProbability right (IROp OpSub sample (IRVar enumVar))
    return $ IREnumSum enumVar (VList enumListL) $ IRIf (IRCall "in" [IROp OpSub sample (IRVar enumVar), IRConst (VList enumListR)]) (IROp OpMult pLeft pRight) (IRConst (VFloat 0))
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRProbability right (IROp OpSub sample (IRVar var))
    return $ IRLetIn var (toIRGenerate left) rightExpr
toIRProbability (ExpF (StaticAnnotations TFloat _ extras) f) sample = do
  logExpr <- toIRProbability f (IRUnaryOp OpLog sample)
  return $ IROp OpDiv logExpr (IRUnaryOp OpAbs sample)
toIRProbability (NegF (StaticAnnotations TFloat _ extras) f) sample =
  toIRProbability f (IRUnaryOp OpNeg sample)
toIRProbability (ReadNN _ name subexpr) sample = do
  let mkInput = toIRGenerate subexpr
  return $ IRIndex (IREvalNN name mkInput) sample
  --TODO: Assumption that subexpr is det.
toIRProbability (Normal t) sample = return $ IRDensity IRNormal sample
toIRProbability (Uniform t) sample = return $ IRDensity IRUniform sample
--TODO: assumption: These will be top-level lambdas:
toIRProbability (Lambda t name subExpr) sample = do
  subExprIR <- toIRProbability subExpr sample
  return $ IRLambda name subExprIR
toIRProbability (Cons _ hdExpr tlExpr) sample = do
  headP <- toIRProbability hdExpr (IRHead sample)
  tailP <- toIRProbability tlExpr (IRTail sample)
  return (IRIf (IROp OpEq sample (IRConst $ VList [])) (IRConst $ VFloat 0) (IROp OpMult headP tailP))
toIRProbability (TCons _ t1Expr t2Expr) sample = do
  t1P <- toIRProbability t1Expr (IRTFst sample)
  t2P <- toIRProbability t2Expr (IRTSnd sample)
  return (IROp OpMult t1P t2P)
toIRProbability (InjF _ name params@[param]) sample = do  --TODO Multivariable
  let letInBlock = IRLetIn v sample invExpr
  paramExpr <- toIRProbability param letInBlock
  return $ IROp OpMult paramExpr invDerivExpr
  where Just fPair = lookup name globalFenv
        FPair (_, [inv]) = fPair
        FDecl (_, [v], _, invExpr, [(_, invDerivExpr)]) = inv
        [param] = params
toIRProbability (Null _) sample = indicator (IROp OpEq sample (IRConst $ VList []))
toIRProbability (Constant _ value) sample = indicator (IROp OpEq sample (IRConst value))
toIRProbability (Call _ name) sample = return $ IRCall (name ++ "_prob") [sample]
toIRProbability (ThetaI _ t) sample = indicator (IROp OpEq sample (IRTheta t))
toIRProbability x sample = error ("found no way to convert to IR: " ++ show x)

packParamsIntoLetinsProb :: (Show a, Floating a) => [String] -> [Expr (StaticAnnotations a) a] -> IRExpr a -> IRExpr a -> Supply Int (IRExpr a)
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
toIRGenerate :: (Show a, Floating a) => Expr (StaticAnnotations a) a -> IRExpr a
toIRGenerate (IfThenElse _ cond left right) = IRIf (toIRGenerate cond) (toIRGenerate left) (toIRGenerate right)
toIRGenerate (GreaterThan _ left right) = IROp OpGreaterThan (toIRGenerate left) (toIRGenerate right)
toIRGenerate (PlusF _ left right) = IROp OpPlus (toIRGenerate left) (toIRGenerate right)
toIRGenerate (PlusI _ left right) = IROp OpPlus (toIRGenerate left) (toIRGenerate right)
toIRGenerate (MultF _ left right) = IROp OpMult (toIRGenerate left) (toIRGenerate right)
toIRGenerate (MultI _ left right) = IROp OpMult (toIRGenerate left) (toIRGenerate right)
toIRGenerate (ExpF _ f) = IRUnaryOp OpExp (toIRGenerate f)
toIRGenerate (NegF _ f) = IRUnaryOp OpNeg (toIRGenerate f)
toIRGenerate (ThetaI _ ix) = IRTheta ix
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
toIRGenerate (ReadNN t name subexpr) = IRCall "randomchoice" [IREvalNN name (toIRGenerate subexpr)]
toIRGenerate x = error ("found no way to convert to IRGen: " ++ show x)

packParamsIntoLetinsGen :: (Show a, Floating a) => [String] -> [Expr (StaticAnnotations a) a] -> IRExpr a -> IRExpr a
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

toIRIntegrate :: (Show a, Floating a) => Expr (StaticAnnotations a) a -> IRExpr a -> IRExpr a -> Supply Int (IRExpr a)
toIRIntegrate (Uniform (StaticAnnotations _ _ tags)) lower higher = do
  return (IROp OpSub (IRCumulative IRUniform higher) (IRCumulative IRUniform lower))
toIRIntegrate (Normal StaticAnnotations {}) lower higher = do
  return (IROp OpSub (IRCumulative IRNormal higher) (IRCumulative IRNormal lower))
toIRIntegrate (MultF (StaticAnnotations _ _ extras) left right) lower higher
  | extras `hasAlgorithm` "multLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRIntegrate right (IROp OpDiv lower (IRVar var)) (IRUnaryOp OpAbs (IROp OpDiv higher (IRVar var)))
    return $ IRLetIn var (toIRGenerate left)
      rightExpr
  | extras `hasAlgorithm` "multRight" = do
      var <- mkVariable ""
      leftExpr <- toIRIntegrate left (IROp OpDiv lower (IRVar var)) (IRUnaryOp OpAbs (IROp OpDiv higher (IRVar var)))
      return $ IRLetIn var (toIRGenerate right)
        leftExpr
toIRIntegrate (PlusF (StaticAnnotations _ _ extras) left right) lower higher
  | extras `hasAlgorithm` "plusLeft" = do
    var <- mkVariable ""
    rightExpr <- toIRIntegrate right (IROp OpSub lower (IRVar var)) (IROp OpSub higher (IRVar var))
    return $ IRLetIn var (toIRGenerate left)
      rightExpr
  | extras `hasAlgorithm` "plusRight" = do
      var <- mkVariable ""
      leftExpr <- toIRIntegrate left (IROp OpSub lower (IRVar var)) (IROp OpSub higher (IRVar var))
      return $ IRLetIn var (toIRGenerate right)
        leftExpr
toIRIntegrate (NegF _ a) low high = do
  toIRIntegrate a (IRUnaryOp OpNeg high) (IRUnaryOp OpNeg low)
toIRIntegrate (ExpF _ a) low high = do
  toIRIntegrate a (IRUnaryOp OpLog high) (IRUnaryOp OpLog low)
toIRIntegrate (TCons _ t1Expr t2Expr) low high = do
  t1P <- toIRIntegrate t1Expr (IRTFst low) (IRTFst high)
  t2P <- toIRIntegrate t2Expr (IRTSnd low) (IRTSnd high)
  return (IROp OpMult t1P t2P)
toIRIntegrate (IfThenElse _ cond left right) low high = do
  var_cond_p <- mkVariable "cond"
  condExpr <- toIRProbability cond (IRConst (VBool True))
  leftExpr <- toIRIntegrate left low high
  rightExpr <- toIRIntegrate right low high
  return $ IRLetIn var_cond_p condExpr
    (IROp OpPlus
      (IROp OpMult (IRVar var_cond_p) leftExpr)
      (IROp OpMult (IROp OpSub (IRConst $ VFloat 1.0) (IRVar var_cond_p) ) rightExpr))
toIRIntegrate (Cons _ hdExpr tlExpr) low high = do
  headP <- toIRIntegrate hdExpr (IRHead low) (IRHead high)
  tailP <- toIRIntegrate tlExpr (IRTail low) (IRTail high)
  return (IRIf (IROp OpOr (IROp OpEq low (IRConst $ VList [])) (IROp OpEq high (IRConst $ VList []))) (IRConst $ VFloat 0) (IROp OpMult headP tailP))
toIRIntegrate (Null _) low high = do
  indicator (IROp OpAnd (IROp OpEq low (IRConst $ VList [])) (IROp OpEq high (IRConst $ VList [])))
toIRIntegrate (Constant _ value) low high = indicator (IROp OpAnd (IROp OpLessThan low (IRConst value)) (IROp OpGreaterThan high (IRConst value))) --TODO What to do if low and high are equal?
toIRIntegrate (InjF _ name params) low high = do  --TODO Multivariable
  let letInBlockLow = IRLetIn v low invExpr
  let letInBlockHigh = IRLetIn v high invExpr
  paramExpr <- toIRIntegrate param letInBlockLow letInBlockHigh
  return $ paramExpr
  where Just fPair = lookup name globalFenv
        FPair (_, [inv]) = fPair
        FDecl (_, [v], _, invExpr, _) = inv
        [param] = params
toIRIntegrate (Call _ name) low high = return $ IRCall (name ++ "_integ") [low, high]
toIRIntegrate (Lambda t name subExpr) low high = do
  subExprIR <- toIRIntegrate subExpr low high
  return $ IRLambda name subExprIR
toIRIntegrate x _ _ = error ("found no way to convert to IRIntegrate: " ++ show x)

