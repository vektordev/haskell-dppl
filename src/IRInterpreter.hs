module IRInterpreter (
generateDet,
generateRand,
) where
  
import Statistics.Distribution (ContGen, genContVar, quantile, density)
import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang (Value(..), Value, ThetaTree(..), Program)

import Control.Monad.Random
import Statistics.Distribution.Normal (normalDistr)
import Data.Foldable
import Data.Number.Erf
import Debug.Trace (trace)
import Data.Data
import Data.Either (fromRight)

newtype VisitationTree = VisitationTree (String, [VisitationTree]) deriving (Show, Eq)

type IREnv a = [(String, IRExpr)]

data RandomFunctions m a = RandomFunctions {uniformGen:: m Value, normalGen:: m Value}

generateRand :: (RandomGen g) => IREnv a -> IREnv a -> [IRExpr]-> IRExpr -> Rand g Value
generateRand = generate f
  where f = RandomFunctions {
    uniformGen = irSample IRUniform, 
    normalGen= irSample IRNormal}
  
generateDet :: IREnv a -> IREnv a -> [IRExpr]-> IRExpr -> Either String Value
generateDet = generate f
  where f = RandomFunctions {
    uniformGen = Left "Uniform Gen is not det", 
    normalGen = Left "Uniform Gen is not det"}

generate :: (Monad m) => RandomFunctions m a -> IREnv a -> IREnv a -> [IRExpr]-> IRExpr -> m Value
--generate f globalEnv env args expr | trace ((show expr) ++ (show args)) False = undefined
generate f globalEnv env args (IRReturning e) = generate f globalEnv env args e
generate f globalEnv env (arg:args) (IRLambda name expr) = generate f globalEnv ((name, arg):env) args expr
generate f globalEnv env [] (IRLambda name expr) = error "No args provided to lambda"
generate f globalEnv env args (IRApply expr val) = generate f globalEnv env (val:args) expr
--generate f globalEnv env (x:args) expr | trace ((show expr) ++ (show x)) False = undefined
generate f globalEnv env (x:args) expr = error ("Arguments provided to non-lamda related expression: " ++ irPrintFlat expr)
generate f globalEnv env args (IRIf cond thenCase elseCase) = do
  condVal <- generate f globalEnv env args cond
  case condVal of
    VBool True -> generate f globalEnv env args thenCase
    VBool False -> generate f globalEnv env args elseCase
    _ -> error "Type error: Condition is not a boolean"
generate f globalEnv env args (IROp OpPlus a b) = do
  aVal <- generate f globalEnv env args a
  bVal <- generate f globalEnv env args b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af + bf)
    (VInt af, VInt bf) -> return $ VInt (af + bf)
    _ -> error "Type error: Plus can only add up numbers (of the same type)"
generate f globalEnv env args (IROp OpMult a b) = do
  aVal <- generate f globalEnv env args a
  bVal <- generate f globalEnv env args b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af * bf)
    (VInt af, VInt bf) -> return $ VInt (af * bf)
    _ -> error "Type error: Mult can only multiply numbers (of the same type)"
generate f globalEnv env args (IROp OpGreaterThan a b) = do
  aVal <- generate f globalEnv env args a
  bVal <- generate f globalEnv env args b
  case (aVal, bVal) of
      (VFloat af, VFloat bf) -> return $ VBool (af > bf)
      (VInt af, VInt bf) -> return $ VBool (af > bf)
      _ -> error "Type error: greater than can only compare two numbers (of the same type)"
generate f globalEnv env args (IROp OpLessThan a b) = do
  aVal <- generate f globalEnv env args a
  bVal <- generate f globalEnv env args b
  case (aVal, bVal) of
      (VFloat af, VFloat bf) -> return $ VBool (af < bf)
      (VInt af, VInt bf) -> return $ VBool (af < bf)
      _ -> error "Type error: greater than can only compare two numbers (of the same type)"
generate f globalEnv env args (IROp OpDiv a b) = do
  aVal <- generate f globalEnv env args a
  bVal <- generate f globalEnv env args b
  case (aVal, bVal) of
      (VFloat af, VFloat bf) -> return $ VFloat (af / bf)
      --(VInt af, VInt bf) -> return $ VFloat (af / bf)
      _ -> error "Type error: Divide can only divide two numbers (of the same type)"
generate f globalEnv env args (IROp OpSub a b) = do
  aVal <- generate f globalEnv env args a
  bVal <- generate f globalEnv env args b
  case (aVal, bVal) of
      (VFloat af, VFloat bf) -> return $ VFloat (af - bf)
      (VInt af, VInt bf) -> return $ VInt (af - bf)
      _ -> error "Type error: Minus can only subtract two numbers (of the same type)"
generate f globalEnv env args (IROp OpOr a b) = do
  aVal <- generate f globalEnv env args a
  bVal <- generate f globalEnv env args b
  case (aVal, bVal) of
        (VBool af, VBool bf) -> return $ VBool (af || bf)
        _ -> error "Type error: Or can only evaluate on two booleans"
generate f globalEnv env args (IROp OpAnd a b) = do
  aVal <- generate f globalEnv env args a
  bVal <- generate f globalEnv env args b
  case (aVal, bVal) of
        (VBool af, VBool bf) -> return $ VBool (af && bf)
        _ -> error "Type error: Or can only evaluate on two booleans"
generate f globalEnv env args (IROp OpEq a b) = do
  aVal <- generate f globalEnv env args a
  bVal <- generate f globalEnv env args b
  case (aVal, bVal) of
    (VBool af, VBool bf) -> return $ VBool (af == bf)
    (VFloat af, VFloat bf) -> return $ VBool (af == bf)
    (VInt af, VInt bf) -> return $ VBool (af == bf)
    (VList af, VList bf) -> return $ VBool (af == bf)
    _ -> error "Type error: Equals can only evaluate on two values"
generate f globalEnv env args (IRUnaryOp OpNot a) = do
  aVal <- generate f globalEnv env args a
  case aVal of
    VBool af -> return $ VBool (not af)
    _ -> error "Type error: Not can only evaluate on a Bool"
generate f globalEnv env args (IRUnaryOp OpExp a) = do
  aVal <- generate f globalEnv env args a
  case aVal of
    VFloat af -> return $ VFloat $ exp af
    _ -> error "Type error: Exp can only evaluate on a floating point numbers"
generate f globalEnv env args (IRUnaryOp OpLog a) = do
  aVal <- generate f globalEnv env args a
  case aVal of
    VFloat af -> return $ VFloat $ log af
    _ -> error "Type error: Exp can only evaluate on a floating point numbers"
generate f globalEnv env args (IRUnaryOp OpNeg a) = do
  aVal <- generate f globalEnv env args a
  case aVal of
    VFloat af -> return $ VFloat (-af)
    VInt af -> return $ VInt (-af)
    _ -> error "Type error: Neg can only evaluate on a number"
generate f globalEnv env args (IRUnaryOp OpAbs a) = do
  aVal <- generate f globalEnv env args a
  case aVal of
    VFloat af -> return $ VFloat (abs af)
    VInt af -> return $ VInt (abs af)
    _ -> error "Type error: Abs can only evaluate on a number"
generate f globalEnv env args (IRTheta a i) = do
  tt <- generate f globalEnv env args a
  let VThetaTree (ThetaTree thetas _) = tt
  return $ VFloat (thetas!!i)
generate f globalEnv env args (IRSubtree a i) = do
  tt <- generate f globalEnv env args a
  let VThetaTree (ThetaTree _ subtrees) = tt
  return $ VThetaTree (subtrees!!i)
generate f globalEnv env args (IRConst val) = return val
generate f globalEnv env args (IRCons hd tl) = do
  ls <- generate f globalEnv env args tl
  case ls of
    VList xs -> do
      x <- generate f globalEnv env args hd
      return $ VList (x : xs)
    _ -> error "Type error: Tail of cons is not a list"
generate f globalEnv env args (IRTCons fst snd) = do
  fstVal <- generate f globalEnv env args fst
  sndVal <- generate f globalEnv env args snd
  return $ VTuple fstVal sndVal
generate f globalEnv env args (IRTFst expr) = do
  val <- generate f globalEnv env args expr
  case val of
    VTuple first _ -> return first
    _ -> error "Type error: Expression of Fst is not a tuple"
generate f globalEnv env args (IRTSnd expr) = do
  val <- generate f globalEnv env args expr
  case val of
    VTuple _ second -> return second
    _ -> error "Type error: Expression of Fst is not a tuple"
generate f globalEnv env args (IRHead listExpr) = do
  listVal <- generate f globalEnv env args listExpr
  case listVal of 
    VList (a:_) -> return a
    _ -> error "Type error: head must be called on a non-empty list"
generate f globalEnv env args (IRTail listExpr) = do
  listVal <- generate f globalEnv env args listExpr
  case listVal of
    VList (_:a) -> return $ VList a
    _ -> error "Type error: tail must be called on a non-empty list"
generate f globalEnv env args (IRDensity IRUniform expr) = do
  x <- generate f globalEnv env args expr
  return $ irPDF IRUniform x
generate f globalEnv env args (IRDensity IRNormal expr) = do
  x <- generate f globalEnv env args expr
  return $ irPDF IRNormal x
generate f globalEnv env args (IRCumulative IRUniform expr) = do
  x <- generate f globalEnv env args expr
  return $ irCDF IRUniform x
generate f globalEnv env args (IRCumulative IRNormal expr) = do
  x <- generate f globalEnv env args expr
  return $ irCDF IRNormal x
generate f globalEnv env args (IRSample IRUniform) =
  uniformGen f
generate f globalEnv env args (IRSample IRNormal) =
  normalGen f
-- Let in evaluates the declaration expression to avoid sampling the same term multiple times
generate f globalEnv env args (IRLetIn name decl body) = do
  declVal <- generate f globalEnv env args decl
  let extendedEnv = (name, IRConst declVal):env
  generate f globalEnv extendedEnv args body
generate f globalEnv env args (IRVar name) = 
  case lookup name env of 
    Just expr -> generate f globalEnv env args expr
    Nothing -> error ("Variable " ++ name ++ " not declared")
generate f globalEnv env args (IRCall name callArgs) = do
  let Just expr = lookup name globalEnv
  -- Evaluate the expressions here if value passed would be a local variable. TODO: This breaks passing of lambda functions as arguments
  evalCa <- mapM (generate f globalEnv env args) (callArgs ++ args)
  let ca = map IRConst evalCa
  generate f globalEnv globalEnv ca expr
generate f globalEnv env args (IREnumSum varname (VInt iVal) expr) = do    --TODO Untested
  foldrM (\i acc -> do
    x <- generate f globalEnv env (IRConst (VInt i):args) (IRLambda varname expr)
    return $ sumValues x acc
    ) (VFloat 0) range
  where range = enumFromTo 0 (iVal-1)
        sumValues = \(VFloat a) (VFloat b) -> VFloat $a+b
generate f globalEnv env args (IREvalNN varname expr) = error "EvalNN cannot be interpreted on the IR. Please use PyTorch or Julia"
generate f globalEnv env args (IRIndex lstExpr idxExpr) = do
  lst <- generate f env globalEnv args lstExpr
  idx <- generate f env globalEnv args idxExpr
  case lst of
    VList l -> case idx of
      VInt i -> return $ l!!i
      _ -> error "Index must be an integer"
    _ -> error "Expression must be a list"
generate f _ _ _ expr = error ("Expression is not yet implemented " ++ show expr)


irSample :: (RandomGen g) => Distribution -> Rand g Value
irSample IRUniform = do
  r <- getRandomR (0.0, 1.0) --uniformR (0.0, 1.0)
  return $ VFloat r
irSample IRNormal = do
  let gauss = normalDistr 0 1
  r <- getRandomR (0.0, 1.0)
  let result = quantile gauss r
  return $ VFloat $ realToFrac result

irPDF :: Distribution -> Value -> Value
irPDF IRUniform (VFloat x) = if x >= 0 && x <= 1 then VFloat 1 else VFloat 0
irPDF IRNormal (VFloat x) = VFloat ((1 / sqrt (2 * pi)) * exp (-0.5 * x * x))
irPDF expr _ = error "Expression must be the density of a valid distribution"

irCDF :: Distribution -> Value -> Value
irCDF IRUniform (VFloat x) = VFloat $ if x < 0 then 0 else if x > 1 then 1 else x
irCDF IRNormal (VFloat x) = VFloat $ (1/2)*(1 + erf(x/sqrt(2)))
  
  