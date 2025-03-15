module IRInterpreter (
generateDet,
generateRand
) where

import Statistics.Distribution (ContGen, genContVar, quantile, density)
import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang (Value(..), ThetaTree(..), Program, elementAt, constructVList)
import StandardLibrary

import Control.Monad.Random
import Statistics.Distribution.Normal (normalDistr)
import Data.Foldable
import Data.Number.Erf
import Debug.Trace (trace)
import Data.Data
import Data.Either (fromRight)
import Data.Bifunctor (second)
import Data.Maybe (fromMaybe)
import SPLL.Lang.Types

newtype VisitationTree = VisitationTree (String, [VisitationTree]) deriving (Show, Eq)

type IREnv a = [(String, IRExpr)]

data RandomFunctions m a = RandomFunctions {uniformGen:: m IRValue, normalGen:: m IRValue}

generateRand :: (RandomGen g) => IREnv a -> [IRExpr]-> IRExpr -> Rand g IRValue
generateRand env = generate f (env ++ standardEnv) (env ++ standardEnv)
  where f = RandomFunctions {
    uniformGen = irSample IRUniform,
    normalGen= irSample IRNormal}

generateDet :: IREnv a -> [IRExpr]-> IRExpr -> Either String IRValue
generateDet env = generate f (env ++ standardEnv) (env ++ standardEnv)
  where f = RandomFunctions {
    uniformGen = Left "Uniform Gen is not det",
    normalGen = Left "Normal Gen is not det"}

generate :: (Monad m) => RandomFunctions m a -> IREnv a -> IREnv a -> [IRExpr]-> IRExpr -> m IRValue
--generate f globalEnv env args expr | trace ((show expr)) False = undefined
generate f globalEnv env args expr | args /= [] = do
  let reverseArgs = reverse args
  let newExpr = foldr (flip IRApply) expr reverseArgs
  generate f globalEnv env [] newExpr
generate f globalEnv env [] (IRInvoke expr) = generate f globalEnv env [] expr
generate f globalEnv env [] (IRLambda name expr) = do
  return $ VClosure env name expr
generate f globalEnv env [] (IRApply expr val) = do
  exprVal <- generate f globalEnv env [] expr
  valVal <- generate f globalEnv env [] val
  case exprVal of
    (VClosure closEnv name lambda) -> do
      let constClosEnv = (name, IRConst valVal):closEnv
      generate f globalEnv constClosEnv [] lambda
    _ -> error ("Type error: Expression is not a closure: " ++ show exprVal)
generate f globalEnv env args (IRIf cond thenCase elseCase) = do
  condVal <- generate f globalEnv env args cond
  case condVal of
    VBool True -> generate f globalEnv env args thenCase
    VBool False -> generate f globalEnv env args elseCase
    _ -> error "Type error: Condition is not a boolean"
generate f globalEnv env [] (IROp OpPlus a b) = do
  aVal <- generate f globalEnv env [] a
  bVal <- generate f globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af + bf)
    (VInt af, VInt bf) -> return $ VInt (af + bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> error ("Type error: Plus can only add up numbers (of the same type): " ++ show (aVal, bVal))
generate f globalEnv env [] (IROp OpMult a b) = do
  aVal <- generate f globalEnv env [] a
  bVal <- generate f globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af * bf)
    (VInt af, VInt bf) -> return $ VInt (af * bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> error ("Type error: Mult can only multiply numbers (of the same type): " ++ show (aVal, bVal))
generate f globalEnv env [] (IROp OpGreaterThan a b) = do
  aVal <- generate f globalEnv env [] a
  bVal <- generate f globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VBool (af > bf)
    (VInt af, VInt bf) -> return $ VBool (af > bf)
    --(VAny, _) -> return $ VBool True
    --(_, VAny) -> return $ VBool True
    _ -> error ("Type error: greater than can only compare two numbers (of the same type): " ++ show (aVal, bVal))
generate f globalEnv env [] (IROp OpLessThan a b) = do
  aVal <- generate f globalEnv env [] a
  bVal <- generate f globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VBool (af < bf)
    (VInt af, VInt bf) -> return $ VBool (af < bf)
    --(VAny, _) -> return $ VBool True
    --(_, VAny) -> return $ VBool True
    _ -> error ("Type error: greater than can only compare two numbers (of the same type): " ++ show (aVal, bVal))
generate f globalEnv env [] (IROp OpDiv a b) = do
  aVal <- generate f globalEnv env [] a
  bVal <- generate f globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af / bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> error ("Type error: Divide can only divide two numbers (of the same type): " ++ show (aVal, bVal))
generate f globalEnv env [] (IROp OpSub a b) = do
  aVal <- generate f globalEnv env [] a
  bVal <- generate f globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af - bf)
    (VInt af, VInt bf) -> return $ VInt (af - bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> error ("Type error: Minus can only subtract two numbers (of the same type): " ++ show (aVal, bVal))
generate f globalEnv env [] (IROp OpOr a b) = do
  aVal <- generate f globalEnv env [] a
  bVal <- generate f globalEnv env [] b
  case (aVal, bVal) of
    (VBool af, VBool bf) -> return $ VBool (af || bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> error ("Type error: Or can only evaluate on two booleans: " ++ show (aVal, bVal))
generate f globalEnv env [] (IROp OpAnd a b) = do
  aVal <- generate f globalEnv env [] a
  bVal <- generate f globalEnv env [] b
  case (aVal, bVal) of
    (VBool af, VBool bf) -> return $ VBool (af && bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> error ("Type error: Or can only evaluate on two booleans: " ++ show (aVal, bVal))
generate f globalEnv env [] (IROp OpEq a b) = do
  aVal <- generate f globalEnv env [] a
  bVal <- generate f globalEnv env [] b
  case (aVal, bVal) of
    (VBool af, VBool bf) -> return $ VBool (af == bf)
    (VFloat af, VFloat bf) -> return $ VBool (af == bf)
    (VInt af, VInt bf) -> return $ VBool (af == bf)
    (VList af, VList bf) -> return $ VBool (af == bf)
    (VTuple af1 af2, VTuple bf1 bf2) -> return $ VBool (af1 == bf1 && af2 == bf2)
    -- Any is not equal to anything
    (VAny, b) -> return $ VBool False
    (a, VAny) -> return $ VBool False
    _ -> error ("Type error: Equals can only evaluate on two values: " ++ show (aVal, bVal))
generate f globalEnv env [] (IRUnaryOp OpNot a) = do
  aVal <- generate f globalEnv env [] a
  case aVal of
    VBool af -> return $ VBool (not af)
    --VAny -> return VAny
    _ -> error "Type error: Not can only evaluate on a Bool"
generate f globalEnv env [] (IRUnaryOp OpExp a) = do
  aVal <- generate f globalEnv env [] a
  case aVal of
    VFloat af -> return $ VFloat $ exp af
    --VAny -> return VAny
    _ -> error "Type error: Exp can only evaluate on a floating point numbers"
generate f globalEnv env [] (IRUnaryOp OpLog a) = do
  aVal <- generate f globalEnv env [] a
  case aVal of
    VFloat af -> return $ VFloat $ log af
    --VAny -> return VAny
    _ -> error "Type error: Exp can only evaluate on a floating point numbers"
generate f globalEnv env [] (IRUnaryOp OpNeg a) = do
  aVal <- generate f globalEnv env [] a
  case aVal of
    VFloat af -> return $ VFloat (-af)
    VInt af -> return $ VInt (-af)
    --VAny -> return VAny
    _ -> error "Type error: Neg can only evaluate on a number"
generate f globalEnv env [] (IRUnaryOp OpSign a) = do
  aVal <- generate f globalEnv env [] a
  case aVal of
    VFloat af | af < 0 -> return $ VFloat (-1)
    VFloat af | af == 0 -> return $ VFloat (0)
    VFloat af | af > 0 -> return $ VFloat (1)
    VInt af | af < 0 -> return $ VInt (-1)
    VInt af | af == 0 -> return $ VInt (0)
    VInt af | af > 0 -> return $ VInt (1)
    --VAny -> return VAny
    _ -> error "Type error: Neg can only evaluate on a number"
generate f globalEnv env [] (IRUnaryOp OpAbs a) = do
  aVal <- generate f globalEnv env [] a
  case aVal of
    VFloat af -> return $ VFloat (abs af)
    VInt af -> return $ VInt (abs af)
    --VAny -> return VAny
    _ -> error "Type error: Abs can only evaluate on a number"
generate f globalEnv env [] (IRUnaryOp OpIsAny a) = do
  aVal <- generate f globalEnv env [] a
  case aVal of
    VAny -> return $ VBool True
    _ -> return $ VBool False
generate f globalEnv env [] (IRTheta a i) = do
  tt <- generate f globalEnv env [] a
  let VThetaTree (ThetaTree thetas _) = tt
  return $ VFloat (thetas!!i)
generate f globalEnv env [] (IRSubtree a i) = do
  tt <- generate f globalEnv env [] a
  let VThetaTree (ThetaTree _ subtrees) = tt
  return $ VThetaTree (subtrees!!i)
generate f globalEnv env [] (IRConst val) = return val
generate f globalEnv env [] (IRCons hd tl) = do
  ls <- generate f globalEnv env [] tl
  case ls of
    VList xs -> do
      x <- generate f globalEnv env [] hd
      return $ VList $ ListCont x xs
    VAny -> do
      x <- generate f globalEnv env [] hd
      return $ VList $ ListCont x AnyList
    _ -> error "Type error: Tail of cons is not a list"
generate f globalEnv env [] (IRTCons fst snd) = do
  fstVal <- generate f globalEnv env [] fst
  sndVal <- generate f globalEnv env [] snd
  return $ VTuple fstVal sndVal
generate f globalEnv env args (IRTFst expr) = do
  val <- generate f globalEnv env args expr
  case val of
    VTuple first _ -> return first
    VClosure cEnv n cExpr -> return $ VClosure cEnv n (IRTFst cExpr)
    _ -> error ("Type error: Expression of Fst is not a tuple: " ++ show val)
generate f globalEnv env args (IRTSnd expr) = do
  val <- generate f globalEnv env args expr
  case val of
    VTuple _ second -> return second
    VClosure cEnv n cExpr -> return $ VClosure cEnv n (IRTSnd cExpr)
    _ -> error ("Type error: Expression of Snd is not a tuple: " ++ show val)
generate f globalEnv env args (IRHead listExpr) = do
  listVal <- generate f globalEnv env args listExpr
  case listVal of
    VList (ListCont a _) -> return a
    _ -> error "Type error: head must be called on a non-empty list"
generate f globalEnv env args (IRTail listExpr) = do
  listVal <- generate f globalEnv env args listExpr
  case listVal of
    VList (ListCont _ AnyList) -> return VAny
    VList (ListCont _ a) -> return $ VList a
    _ -> error "Type error: tail must be called on a non-empty list"
generate f globalEnv env [] (IRElementOf elemExpr listExpr) = do
  elemVal <- generate f globalEnv env [] elemExpr
  listVal <- generate f globalEnv env [] listExpr
  case listVal of
    VList a -> return $ VBool (elemVal `elem` a)
    _ -> error "Type error: ElementOf must be called on a list"
generate f globalEnv env [] (IRLeft expr) = do
  x <- generate f globalEnv env [] expr
  return $ VEither (Left x)
generate f globalEnv env [] (IRRight expr) = do
  x <- generate f globalEnv env [] expr
  return $ VEither (Right x)
generate f globalEnv env [] (IRFromLeft expr) = do
  x <- generate f globalEnv env [] expr
  case x of
    VEither (Left l) -> return l
    _ -> error $ "Type error: fromLeftrequires an either left: " ++ show x
generate f globalEnv env [] (IRFromRight expr) = do
  x <- generate f globalEnv env [] expr
  case x of
    VEither (Right r) -> return r
    _ -> error $ "Type error: fromRight requires an either right: " ++ show x
generate f globalEnv env [] (IRIsLeft expr) = do
  x <- generate f globalEnv env [] expr
  case x of
    VEither (Left r) -> return (VBool True)
    VEither (Right r) -> return (VBool False)
    _ -> error $ "Type error: isLeft requires an either: " ++ show x
generate f globalEnv env [] (IRIsRight expr) = do
  x <- generate f globalEnv env [] expr
  case x of
    VEither (Left r) -> return (VBool False)
    VEither (Right r) -> return (VBool True)
    _ -> error $ "Type error: isLeft requires an either: " ++ show x
generate f globalEnv env [] (IRDensity IRUniform expr) = do
  x <- generate f globalEnv env [] expr
  return $ irPDF IRUniform x
generate f globalEnv env [] (IRDensity IRNormal expr) = do
  x <- generate f globalEnv env [] expr
  return $ irPDF IRNormal x
generate f globalEnv env [] (IRCumulative IRUniform expr) = do
  x <- generate f globalEnv env [] expr
  return $ irCDF IRUniform x
generate f globalEnv env [] (IRCumulative IRNormal expr) = do
  x <- generate f globalEnv env [] expr
  return $ irCDF IRNormal x
generate f globalEnv env [] (IRSample IRUniform) =
  uniformGen f
generate f globalEnv env [] (IRSample IRNormal) =
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
generate f globalEnv env [] (IREnumSum varname (VList values) expr) = do    --TODO Untested
  foldrM (\(VInt i) acc -> do
    x <- generate f globalEnv env [IRConst (VInt i)] (IRLambda varname expr)
    return $ sumValues x acc
    ) (VFloat 0) values
  where sumValues = \(VFloat a) (VFloat b) -> VFloat $a+b
generate f globalEnv env [] (IREvalNN varname expr) = error "EvalNN cannot be interpreted on the IR. Please use PyTorch or Julia"
generate f globalEnv env args (IRIndex lstExpr idxExpr) = do
  lst <- generate f env globalEnv args lstExpr
  idx <- generate f env globalEnv args idxExpr
  case lst of
    VList l -> case idx of
      VInt i -> return $ l `elementAt` i
      _ -> error "Index must be an integer"
    _ -> error "Expression must be a list"
generate _ _ _ _ (IRError s) = error $ "Error during interpretation: " ++ s
generate f _ _ _ expr = error ("Expression is not yet implemented " ++ show expr)

irSample :: (RandomGen g) => Distribution -> Rand g IRValue
irSample IRUniform = do
  r <- getRandomR (0.0, 1.0) --uniformR (0.0, 1.0)
  return $ VFloat r
irSample IRNormal = do
  let gauss = normalDistr 0 1
  r <- getRandomR (0.0, 1.0)
  let result = quantile gauss r
  return $ VFloat $ realToFrac result

irPDF :: Distribution -> IRValue -> IRValue
--irPDF _ VAny = VFloat 1
irPDF IRUniform (VFloat x) = if x >= 0 && x <= 1 then VFloat 1 else VFloat 0
irPDF IRNormal (VFloat x) = VFloat ((1 / sqrt (2 * pi)) * exp (-0.5 * x * x))
irPDF expr _ = error "Expression must be the density of a valid distribution"

irCDF :: Distribution -> IRValue -> IRValue
irCDF IRUniform (VFloat x) = VFloat $ if x < 0 then 0 else if x > 1 then 1 else x
irCDF IRNormal (VFloat x) = VFloat $ (1/2)*(1 + erf(x/sqrt(2)))
