module SPLL.IROptimizer where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Lang
import SPLL.Lang.Types
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

postProcess :: CompilerConfig -> IRExpr -> IRExpr
--postProcess = id
postProcess conf = fixedPointIteration (optimize conf)

isValue :: IRExpr -> Bool
isValue (IRConst _) = True
isValue _ = False

isLambda :: IRExpr -> Bool
isLambda IRLambda {} = True
isLambda _ = False

unval :: IRExpr -> IRValue
unval (IRConst val) = val
unval _ = error "tried to unval a non-val"

--strip all top-level lambdas and collect the bound names.
--unwrapTLLambdas :: Expr t a -> ([Varname], Expr t a)
--unwrapTLLambdas (Lambda _ name subExpr) = (name : innerNames, unwrappedExpr)
--  where (innerNames, unwrappedExpr) = unwrapTLLambdas subExpr
--unwrapTLLambdas expr = ([], expr)


fixedPointIteration :: (Eq a, Show a) => (a -> a) -> a -> a
fixedPointIteration f x = if fx == x then x else fixedPointIteration f fx
  where fx = f x

optimize :: CompilerConfig -> IRExpr -> IRExpr
optimize conf = irMap (commonSubexprStage . applyConstStage . assiciativityStage . letInStage . constantDistrStage . simplifyStage)
  where
    oLvl = optimizerLevel conf
    commonSubexprStage = if False then optimizeCommonSubexpr else id -- Too buggy to use
    applyConstStage = if oLvl >= 2 then applyConstant else id
    assiciativityStage = if oLvl >= 2 then optimizeAssociativity else id
    letInStage = if oLvl >= 2 then optimizeLetIns else id
    constantDistrStage = if oLvl >= 2 then evalConstantDistr else id
    simplifyStage = if oLvl >= 1 then simplify else id

--TODO: We can also optimize index magic, potentially here. i.e. a head tail tail x can be simplified.
--TODO: Unary operators

-- | Simplify terms that apply a constant to a lambda expression
-- if we build a lambda expression and immediately apply a constant, replace mentions of the lambda'd variable with the constant.
applyConstant :: IRExpr -> IRExpr
applyConstant (IRApply (IRLambda varname inExpr) v@(IRConst _)) = replaceAll (IRVar varname) v inExpr
applyConstant x = x

optimizeAssociativity :: IRExpr -> IRExpr
-- Associative Addition
optimizeAssociativity (IROp OpPlus leftV (IROp OpPlus rightV1 rightV2))
  | isValue leftV && isValue rightV1 = IROp OpPlus (IRConst (forceOp OpPlus (unval leftV) (unval rightV1))) rightV2   -- a + (b + c) = (a + b) + c
  | isValue leftV && isValue rightV2 = IROp OpPlus (IRConst (forceOp OpPlus (unval leftV) (unval rightV2))) rightV1   -- a + (b + c) = b + (a + c)
optimizeAssociativity (IROp OpPlus (IROp OpPlus leftV1 leftV2) rightV )
  | isValue leftV1 && isValue rightV = IROp OpPlus (IRConst (forceOp OpPlus (unval leftV1) (unval rightV))) leftV2   -- a + (b + c) = (a + b) + c
  | isValue leftV2 && isValue rightV = IROp OpPlus (IRConst (forceOp OpPlus (unval leftV2) (unval rightV))) leftV1   -- a + (b + c) = b + (a + c)
-- Associative Multiplication
optimizeAssociativity (IROp OpMult leftV (IROp OpMult rightV1 rightV2))
  | isValue leftV && isValue rightV1 = IROp OpMult (IRConst (forceOp OpMult (unval leftV) (unval rightV1))) rightV2   -- a * (b * c) = (a * b) * c
  | isValue leftV && isValue rightV2 = IROp OpMult (IRConst (forceOp OpMult (unval leftV) (unval rightV2))) rightV1   -- a * (b * c) = (a * c) * b
optimizeAssociativity (IROp OpMult (IROp OpMult leftV1 leftV2) rightV )
  | isValue leftV1 && isValue rightV = IROp OpMult (IRConst (forceOp OpMult (unval leftV1) (unval rightV))) leftV2   -- a + (b + c) = (a + b) + c
  | isValue leftV2 && isValue rightV = IROp OpMult (IRConst (forceOp OpMult (unval leftV2) (unval rightV))) leftV1   -- a + (b + c) = b + (a + c)
optimizeAssociativity x = x

optimizeLetIns :: IRExpr -> IRExpr
optimizeLetIns ex@(IRLetIn name val scope)
  | isSimple val = replaceAll (IRVar name) val scope
  | countUses name scope == 1 = replaceAll (IRVar name) val scope
  | countUses name scope == 0 = scope
optimizeLetIns ex = ex

evalConstantDistr :: IRExpr -> IRExpr
evalConstantDistr (IRDensity IRNormal (IRConst (VFloat x))) = IRConst (VFloat ((1 / sqrt (2 * pi)) * exp (-0.5 * x * x)))
evalConstantDistr (IRCumulative IRNormal (IRConst (VFloat x))) = IRConst (VFloat ((1/2) * (1 + erf (x/sqrt (2)))))
evalConstantDistr (IRDensity IRUniform (IRConst (VFloat x))) = IRConst (VFloat (if x >= 0 && x <= 1 then 1 else 0))
evalConstantDistr (IRCumulative IRUniform (IRConst (VFloat x))) = IRConst (VFloat (if x < 0 then 0 else if x > 1 then 1 else x))
evalConstantDistr x = x

simplify :: IRExpr -> IRExpr
simplify (IROp op leftV rightV)
  | isValue leftV && isValue rightV = IRConst (forceOp op (unval leftV) (unval rightV))
  | isValue leftV || isValue rightV = softForceLogic op leftV rightV
simplify (IRUnaryOp OpIsAny x) = forceAnyCheck x
simplify (IRUnaryOp op val) | isValue val = IRConst $ forceUnaryOp op (unval val)
simplify (IRIf _ left right) | left == right = left
simplify x@(IRIf cond left right) =
  if isValue cond
    then if unval cond == VBool True
      then left
      else right
    else x
simplify x@(IRCons left right) =
  if isValue left && isValue right
    then let (VList tl) = unval right in IRConst (VList (ListCont (unval left) tl))
    else x 
simplify (IRHead (IRCons a _)) = a
simplify (IRTail (IRCons _ b)) = b
simplify (IRTFst (IRTCons a _)) = a
simplify (IRTSnd (IRTCons _ b)) = b
simplify (IRTCons (IRLambda n a) (IRLambda m b)) | n == m = IRLambda n (IRTCons a b)
simplify x = x

countUses :: String -> IRExpr -> Int
countUses var (IRVar a) | a == var = 1
countUses var expr = sum (map (countUses var) (getIRSubExprs expr))

isSimple :: IRExpr -> Bool
--isSimple (IRTheta a) = True
isSimple (IRVar a) = True
isSimple (IRConst a) = True
isSimple _ = False

replaceAll :: IRExpr -> IRExpr -> IRExpr -> IRExpr
replaceAll find replaceWith = irMap (replace find replaceWith)

replace :: Eq p => p -> p -> p -> p
replace find replace' expr = if find == expr then replace' else expr

failConversion :: Expr -> IRExpr
failConversion = error "Cannot convert VClosure"

softForceLogic :: Operand -> IRExpr -> IRExpr -> IRExpr
softForceLogic OpOr (IRConst (VBool True)) _ = IRConst (VBool True)
softForceLogic OpOr _ (IRConst (VBool True)) = IRConst (VBool True)
softForceLogic OpOr (IRConst (VBool False)) right = right
softForceLogic OpOr left (IRConst (VBool False)) = left
softForceLogic OpAnd (IRConst (VBool True)) right = right
softForceLogic OpAnd left (IRConst (VBool True)) = left
softForceLogic OpAnd (IRConst (VBool False)) _ = IRConst (VBool False)
softForceLogic OpAnd _ (IRConst (VBool False)) = IRConst (VBool False)
softForceLogic OpEq (IRCons _ _) (IRConst (VList EmptyList)) = IRConst $ VBool False
softForceLogic op left right = IROp op left right     -- Nothing can be done

forceOp :: Operand -> IRValue -> IRValue -> IRValue
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
forceOp _ _ _ = error "Error during forceOp optimizer"

forceUnaryOp :: UnaryOperand -> IRValue -> IRValue
forceUnaryOp OpAbs (VFloat x) = VFloat (abs x)
forceUnaryOp OpAbs (VInt x) = VInt (abs x)
forceUnaryOp OpNeg (VFloat x) = VFloat (-x)
forceUnaryOp OpNeg (VInt x) = VInt (-x)
forceUnaryOp OpSign (VFloat x) = VFloat (signum x)
forceUnaryOp OpSign (VInt x) = VInt (signum x)
forceUnaryOp OpNot (VBool x) = VBool (not x)
forceUnaryOp OpExp (VFloat x) = VFloat (exp x)
forceUnaryOp OpLog (VFloat x) = VFloat (log x)
forceUnaryOp _ _ = error "Error during forceUnaryOp optimizer"


--TODO

forceAnyCheck :: IRExpr -> IRExpr
forceAnyCheck x | isValue x = IRConst $ VBool (unval x == VAny)
forceAnyCheck (IRCons _ _) = IRConst $ VBool False  -- Lists can never be any
forceAnyCheck (IRTCons _ _) = IRConst $ VBool False -- Tuples can never be any
forceAnyCheck (IRLeft _) = IRConst $ VBool False -- Eithers can never be any
forceAnyCheck (IRRight _) = IRConst $ VBool False -- Eithers can never be any
forceAnyCheck x = IRUnaryOp OpIsAny x
-- Maybe more, I am not quite sure

exprSize :: IRExpr -> Int
exprSize expr | null (getIRSubExprs expr) = 1
exprSize expr = sum (map exprSize (getIRSubExprs expr))

numOccurances :: IRExpr -> IRExpr -> Int
numOccurances ref expr | ref == expr = 1
numOccurances ref expr = sum (map (numOccurances ref) (getIRSubExprs expr))

findCommonSubexpr :: IRExpr -> IRExpr -> [IRExpr]
findCommonSubexpr _ ref | exprSize ref < 3 = []
findCommonSubexpr _ (IRLambda _ _) = []
findCommonSubexpr fullScope ref | numOccurances ref fullScope >= 2 = [ref]
findCommonSubexpr fullScope ref = concatMap (findCommonSubexpr fullScope) (getIRSubExprs ref)
-- FIXME random distributions are not equal

optimizeCommonSubexpr :: IRExpr -> IRExpr
optimizeCommonSubexpr (IRLambda n b) = IRLambda n (optimizeCommonSubexpr b)
optimizeCommonSubexpr (IRLetIn n v b) = IRLetIn n v (optimizeCommonSubexpr b)
optimizeCommonSubexpr expr = letInBlock
  where
    commonSubs = findCommonSubexpr expr expr
    optimNames = map (\i -> "opt" ++ show i) [0..(length commonSubs - 1)]
    namedCommonSubs = zip commonSubs optimNames
    replacedBody = foldr (\(sub, name) body -> replaceAll sub (IRVar name) body) expr namedCommonSubs
    letInBlock = foldr (\(sub, name) block -> IRLetIn name sub block) replacedBody namedCommonSubs