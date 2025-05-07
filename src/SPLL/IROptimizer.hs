module SPLL.IROptimizer (
  optimizeEnv
, failConversion
) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types ( Expr )
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
import Data.Functor ( (<&>) )
import Data.Number.Erf (erf)
import Data.List (nub)
import Control.Monad.Supply
import Data.Foldable (toList)
import PrettyPrint


optimizeEnv :: CompilerConfig -> IREnv -> IREnv
optimizeEnv conf = map (\(IRFunGroup name gen prob integ doc) -> IRFunGroup name (pp gen) (prob <&> pp) (integ <&> pp) doc)
  where pp (expr, doc) = (postProcess conf expr, doc)

postProcess :: CompilerConfig -> IRExpr -> IRExpr
--postProcess = id
postProcess conf = fixedPointIteration (optimize conf)

isValue :: IRExpr -> Bool
isValue (IRConst _) = True
isValue _ = False

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
optimize conf = irMap (commonSubexprStage . applyConstStage . assiciativityStage . letInStage . constantDistrStage . simplifyStage . indexStage . distributeConditionals)
  where
    oLvl = optimizerLevel conf
    commonSubexprStage = if False then optimizeCommonSubexpr else id -- Too buggy to use
    applyConstStage = if oLvl >= 2 then applyConstant else id
    assiciativityStage = if oLvl >= 2 then optimizeAssociativity else id
    letInStage = if oLvl >= 2 then optimizeLetIns else id
    constantDistrStage = if oLvl >= 2 then evalConstantDistr else id
    simplifyStage = if oLvl >= 1 then simplify else id
    indexStage = if oLvl >= 1 then indexmagic else id
    distributeConditionals = if oLvl >= 2 then distributeIf else id

indexmagic :: IRExpr -> IRExpr
-- if calling Apply ("indexOf") elem [0..], replace with elem
indexmagic (IRInvoke (IRApply (IRApply (IRVar "indexOf") elem) (IRConst (VList list)))) | isNaturals (toList list) = elem
  where
    isNaturals lst = and (zipWith (==) [0..] (map toNatural lst))
    toNatural (VInt x) = x
    toNatural _ = -1 -- not a natural number, should fail the above.
indexmagic x = x

-- (if cond then x else y, if cond then z else w) can be simplified to if cond then (x, z) else (y, w).
-- basically, law of distribution.
distributeIf :: IRExpr -> IRExpr
distributeIf (IRTCons (IRIf cond1 x1 x2) (IRIf cond2 y1 y2)) | cond1 == cond2 = IRIf cond1 (IRTCons x1 y1) (IRTCons x2 y2)
-- now for ((x, y), z):
distributeIf (IRTCons (IRTCons (IRIf cond1 x1 x2) (IRIf cond2 y1 y2)) (IRIf cond3 z1 z2)) | cond1 == cond2 && cond1 == cond3 =
  IRIf cond1 (IRTCons (IRTCons x1 y1) z1) (IRTCons (IRTCons x2 y2) z2)
-- now for (x, (y, z)):
distributeIf (IRTCons (IRIf cond1 x1 x2) (IRTCons (IRIf cond2 y1 y2) (IRIf cond3 z1 z2))) | cond1 == cond2 && cond1 == cond3 =
  IRIf cond1 (IRTCons x1 (IRTCons y1 z1)) (IRTCons x2 (IRTCons y2 z2))
distributeIf x = x

--TODO: We can also optimize index magic, potentially here. i.e. a head tail tail x can be simplified.
--TODO: Unary operators

-- | Simplify terms that apply a constant to a lambda expression
-- if we build a lambda expression and immediately apply a constant, replace mentions of the lambda'd variable with the constant.
applyConstant :: IRExpr -> IRExpr
applyConstant (IRInvoke (IRApply (IRLambda varname inExpr) v@(IRConst _))) = replaceAll (IRVar varname) v inExpr
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
--logic operands: or and and
softForceLogic OpOr (IRConst (VBool True)) _ = IRConst (VBool True)
softForceLogic OpOr _ (IRConst (VBool True)) = IRConst (VBool True)
softForceLogic OpOr (IRConst (VBool False)) right = right
softForceLogic OpOr left (IRConst (VBool False)) = left
softForceLogic OpAnd (IRConst (VBool True)) right = right
softForceLogic OpAnd left (IRConst (VBool True)) = left
softForceLogic OpAnd (IRConst (VBool False)) _ = IRConst (VBool False)
softForceLogic OpAnd _ (IRConst (VBool False)) = IRConst (VBool False)
softForceLogic OpEq (IRCons _ _) (IRConst (VList EmptyList)) = IRConst $ VBool False
-- integer arithmetic:
softForceLogic OpPlus (IRConst (VInt 0)) right = right
softForceLogic OpPlus left (IRConst (VInt 0)) = left
softForceLogic OpMult (IRConst (VInt 0)) _ = IRConst (VInt 0)
softForceLogic OpMult _ (IRConst (VInt 0)) = IRConst (VInt 0)
softForceLogic OpMult (IRConst (VInt 1)) right = right
softForceLogic OpMult left (IRConst (VInt 1)) = left
softForceLogic OpDiv left (IRConst (VInt 1)) = left
softForceLogic OpDiv left (IRConst (VInt 0)) = error "tried to divide by zero in softForceArithmetic"
softForceLogic OpDiv (IRConst (VInt 0)) _ = IRConst (VInt 0)
softForceLogic OpSub left (IRConst (VInt 0)) = left
softForceLogic OpSub left right | left == right = IRConst (VInt 0)
--float arithmetic:
softForceLogic OpPlus (IRConst (VFloat 0)) right = right
softForceLogic OpPlus left (IRConst (VFloat 0)) = left
softForceLogic OpMult (IRConst (VFloat 0)) _ = IRConst (VFloat 0)
softForceLogic OpMult _ (IRConst (VFloat 0)) = IRConst (VFloat 0)
softForceLogic OpMult (IRConst (VFloat 1)) right = right
softForceLogic OpMult left (IRConst (VFloat 1)) = left
softForceLogic OpDiv left (IRConst (VFloat 1)) = left
softForceLogic OpDiv left (IRConst (VFloat 0)) = error "tried to divide by zero in softForceArithmetic"
softForceLogic OpDiv (IRConst (VFloat 0)) _ = IRConst (VFloat 0)
softForceLogic OpSub left (IRConst (VFloat 0)) = left
softForceLogic OpSub left right | left == right = IRConst (VFloat 0)
softForceLogic op left right = IROp op left right
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
-- Operations on ANYs should not happen. This is simplifying unreachable code paths, that should be optimized away later
forceOp _ VAny _ = VAny
forceOp _ _ VAny = VAny
forceOp a b c = error $ "Error during forceOp optimizer: " ++ show a ++ " " ++ show b ++ " " ++ show c

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

--slightly strict matching: Do not match if random sampling is contained.
-- otherwise, defer to (==)
matchExprs :: IRExpr -> IRExpr -> Bool
matchExprs a b = if samples a then False else a == b

--FIXME: a function call to a sampling function does itself also sample.
samples :: IRExpr -> Bool
samples (IRSample _) = True
samples x = any samples (getIRSubExprs x)

numOccurrences :: IRExpr -> IRExpr -> Int
numOccurrences ref expr | ref `matchExprs` expr = 1
numOccurrences ref expr = sum (map (numOccurrences ref) (getIRSubExprs expr))

findExprs :: IRExpr -> [IRExpr]
findExprs (IRLambda _ _) = []
findExprs expr = expr : (concatMap findExprs (getIRSubExprs expr))

findCommonSubexpr :: IRExpr -> IRExpr -> [IRExpr]
--findCommonSubexpr _ ref | exprSize ref < 3 = []
findCommonSubexpr scope _ = filter (\x -> numOccurrences x scope >= 2 && exprSize x > 1) (nub (findExprs scope))
--findCommonSubexpr _ (IRLambda _ _) = []
--findCommonSubexpr fullScope ref | numOccurrences ref fullScope >= 2 = [ref]
--findCommonSubexpr fullScope ref = concatMap (findCommonSubexpr fullScope) (getIRSubExprs ref)

optimizeCommonSubexpr :: IRExpr -> IRExpr
optimizeCommonSubexpr (IRLambda n b) = IRLambda n (optimizeCommonSubexpr b)
optimizeCommonSubexpr (IRLetIn n v b) = IRLetIn n v (optimizeCommonSubexpr b)
optimizeCommonSubexpr expr = letInBlock
  where
    commonSubs = findCommonSubexpr expr expr
    optimNames = map (\i -> "opt_" ++ show i ++ "_common") [1..]
    namedCommonSubs = zip commonSubs optimNames
    letInBlock = foldl extractSubexpr expr namedCommonSubs

extractSubexpr :: IRExpr -> (IRExpr, Varname) -> IRExpr
extractSubexpr body (sub, name) = trace report $ IRLetIn name sub newBody
  where
    newBody = replaceAll sub (IRVar name) body
    report = "Extracted subexpression: \n" ++ pPrintIRExpr sub 2 ++ "\n ##### as " ++ name ++ ", now: \n" ++ pPrintIRExpr newBody 2
