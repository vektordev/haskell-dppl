module SPLL.IntermediateRepresentation (
  IRExpr(..)
, StaticAnnotations(..)
, Tag(..)
, Operand(..)
, UnaryOperand(..)
, Distribution(..)
, toIRProbability
, toIRGenerate
, envToIR
, Varname
, irMap
) where

import SPLL.Lang
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Transpiler
import SPLL.Analysis
import SPLL.Typing.Typing
import Control.Monad.Supply
import Debug.Trace
import SPLL.InferenceRule
{-
{-# OPTIONS -Wall #-}
import Control.Monad.Cont
import Control.Monad.State.Strict


data IRExpr = IRLetIn Varname IRExpr IRExpr
            | IRLit Int
            | IRAdd IRExpr IRExpr
            | IRVar Varname
  deriving (Show)

newtype Varname = Varname String
  deriving (Show)

type M = StateT Int (Cont IRExpr)

runM :: M IRExpr -> IRExpr
runM m = runCont (runStateT m 0) fst

genName :: String -> M Varname
genName base = do
  i <- get
  let name = "$" ++ show i ++ "_" ++ base
  put (i + 1)
  return (Varname name)

letin :: String -> IRExpr -> M Varname
letin base rhs = do
  name <- genName base
  lift $ cont (\f -> IRLetIn name rhs (f name))

-- literal :: Int -> M ()
-- literal n = lift $ cont (\f -> _ f)

generateCode :: M IRExpr
generateCode = do
  varName <- letin "some_string" (IRLit 10)
  subex <- subCode varName
  return (IRAdd (IRVar varName) subex)

-- returs var + 3, using a let binding
subCode :: Varname -> M IRExpr
subCode v = do
  a <- letin "a" (IRLit 3)
  return (IRAdd (IRVar a) (IRVar v))
-}



{-
import Control.Monad.Cont
import Control.Monad.State.Strict

type Varname = String

type M a = ContT Int (State (IRExpr a))

--runM :: M a (IRExpr a) -> IRExpr a
runM m = evalState (runContT m return) 0

genName :: String -> M a Varname
genName base = do
  i <- get
  let name = "$" ++ show i ++ "_" ++ base
  put (i + 1)
  return name

letin :: String -> IRExpr a -> M a Varname
letin base rhs = do
  name <- genName base
  ContT (\f -> IRLetIn name rhs <$> f name)
-}
--generateCode :: M a (IRExpr a)
--generateCode = do
--  varName <- letin "some_string" (IRLit 10)
--  subex <- subCode varName
--  return (IRAdd (IRVar varName) subex)

-- returs var + 3, using a let binding
--subCode :: Varname -> M a (IRExpr a)
--subCode v = do
--  a <- letin "a" (IRLit 3)
--  return (IRAdd (IRVar a) (IRVar v))

type Varname = String

data Operand = OpPlus
             | OpMult
             | OpGreaterThan
             | OpDiv
             | OpSub
             | OpOr
             | OpEq
             deriving (Show, Eq)

data UnaryOperand = OpNeg
                  | OpAbs
                  | OpNot
                  deriving (Show, Eq)

data Distribution = IRNormal | IRUniform deriving (Show, Eq)

data IRExpr a = IRIf (IRExpr a) (IRExpr a) (IRExpr a)
              | IROp Operand (IRExpr a) (IRExpr a)
              | IRUnaryOp UnaryOperand (IRExpr a)
              | IRTheta Int
              | IRConst (Value a)
              | IRCons (IRExpr a) (IRExpr a)
              | IRTCons (IRExpr a) (IRExpr a)
              | IRHead (IRExpr a)
              | IRTail (IRExpr a)
              | IRTFst (IRExpr a)
              | IRTSnd (IRExpr a)
              | IRDensity Distribution (IRExpr a)
              | IRSample Distribution
              | IRLetIn Varname (IRExpr a) (IRExpr a)
              | IRVar Varname
              | IRCall String [IRExpr a]
              | IRLambda String (IRExpr a)
              -- auxiliary construct to aid enumeration: bind each enumerated Value to the Varname and evaluate the subexpr. Sum results.
              -- maybe we can instead move this into some kind of standard library.
              | IREnumSum Varname (Value a) (IRExpr a)
              | IREvalNN Varname (IRExpr a)
              | IRIndex (IRExpr a) (IRExpr a)
              | IRReturning (IRExpr a) -- only used to wrap statements that act as exit point of the expression.
              deriving (Show, Eq)
--3: convert algortihm-and-type-annotated Exprs into abstract representation of explicit computation:
--    Fold enum ranges, algorithms, etc. into a representation of computation that can be directly converted into code.


-- perhaps as an explicit lambda in the top of the expression, otherwise we'll get trouble generating code.
-- TODO: How do we deal with top-level lambdas in binding here?
--  TL-Lambdas are presumably to be treated differently than non-TL, at least as far as prob is concerned.
envToIR :: (Ord a, Fractional a, Show a, Eq a) => Env (StaticAnnotations a) a -> [(String, IRExpr a)]
envToIR = concatMap (\(name, binding) -> [
  (name ++ "_prob", IRLambda "sample" (postProcess $ runSupplyVars (toIRProbability binding (IRVar "sample")))),
  (name ++ "_gen", postProcess $ toIRGenerate binding)])

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

isValue :: IRExpr a -> Bool
isValue (IRConst val) = True
isValue _ = False

unval :: IRExpr a -> Value a
unval (IRConst val) = val
unval _ = error "tried to unval a non-val"

irMap :: (IRExpr a -> IRExpr a) -> IRExpr a -> IRExpr a
irMap f x = case x of
  (IRIf cond left right) -> f (IRIf (irMap f cond) (irMap f left) (irMap f right))
  (IROp op left right) -> f (IROp op (irMap f left) (irMap f right))
  (IRUnaryOp op expr) -> f (IRUnaryOp op (irMap f expr))
  (IRCons left right) -> f (IRCons (irMap f left) (irMap f right))
  (IRTCons left right) -> f (IRTCons (irMap f left) (irMap f right))
  (IRHead expr) -> f (IRHead (irMap f expr))
  (IRTail expr) -> f (IRTail (irMap f expr))
  (IRTFst expr) -> f (IRTFst (irMap f expr))
  (IRTSnd expr) -> f (IRTSnd (irMap f expr))
  (IRDensity a expr) -> f (IRDensity a (irMap f expr))
  (IRLetIn name left right) -> f (IRLetIn name (irMap f left) (irMap f right))
  (IRCall name args) -> f (IRCall name (map (irMap f) args))
  (IRLambda name scope) -> f (IRLambda name (irMap f scope))
  (IREnumSum name val scope) -> f (IREnumSum name val (irMap f scope))
  (IREvalNN name arg) -> f (IREvalNN name (irMap f arg))
  (IRIndex left right) -> f (IRIndex (irMap f left) (irMap f right))
  (IRReturning expr) -> f (IRReturning (irMap f expr))
  (IRTheta _) -> f x
  (IRConst _) -> f x
  (IRSample _) -> f x
  (IRVar _) -> f x

--TODO: We can also optimize index magic, potentially here. i.e. a head tail tail x can be simplified.
--TODO: Unary operators
evalAll :: (Show a, Ord a, Fractional a) => IRExpr a -> IRExpr a
evalAll expr@(IROp op leftV rightV)
  | isValue leftV && isValue rightV = IRConst (forceOp op (unval leftV) (unval rightV))
  | (isValue leftV || isValue rightV) && (op == OpOr) = softForceLogic op leftV rightV
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
  | isSimple val = trace "tracing" $ traceShow ex $ irMap (replace (IRVar name) val) scope
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
softForceLogic op left right = error "tried to force logic op that can't be forced."

forceOp :: (Ord a, Fractional a) => Operand -> Value a -> Value a -> Value a
forceOp OpEq x y = VBool (x == y)
forceOp OpMult (VInt x) (VInt y) = VInt (x*y)
forceOp OpMult (VFloat x) (VFloat y) = VFloat (x*y)
forceOp OpPlus (VInt x) (VInt y) = VInt (x+y)
forceOp OpPlus (VFloat x) (VFloat y) = VFloat (x+y)
forceOp OpDiv (VInt x) (VInt y) = VInt (x-y)
forceOp OpDiv (VFloat x) (VFloat y) = VFloat (x-y)
forceOp OpSub (VInt _) (VInt _) = error "tried to do integer division in forceOp"
forceOp OpSub (VFloat x) (VFloat y) = VFloat (x/y)
forceOp OpOr (VBool x) (VBool y) = VBool (x || y)
forceOp OpGreaterThan (VInt x) (VInt y) = VBool (x >= y)
forceOp OpGreaterThan (VFloat x) (VFloat y) = VBool (x >= y)

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
toIRProbability :: (Fractional a, Show a) => Expr (StaticAnnotations a) a -> IRExpr a -> Supply Int (IRExpr a)
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
toIRProbability (Null _) sample = indicator (IROp OpEq sample (IRConst $ VList []))
toIRProbability (Constant _ value) sample = indicator (IROp OpEq sample (IRConst value))
toIRProbability (Call _ name) sample = return $ IRCall (name ++ "_prob") [sample]
toIRProbability x sample = error ("found no way to convert to IR: " ++ show x)

indicator :: Num a => IRExpr a -> Supply Int (IRExpr a)
indicator condition = return $ IRIf condition (IRConst $ VFloat 1) (IRConst $ VFloat 0)

--folding detGen and Gen into one, as the distinction is one to make sure things that are det are indeed det.
-- That's what the type system is for though.
toIRGenerate :: Show a => Expr (StaticAnnotations a) a -> IRExpr a
toIRGenerate (IfThenElse _ cond left right) = IRIf (toIRGenerate cond) (toIRGenerate left) (toIRGenerate right)
toIRGenerate (GreaterThan _ left right) = IROp OpGreaterThan (toIRGenerate left) (toIRGenerate right)
toIRGenerate (PlusF _ left right) = IROp OpPlus (toIRGenerate left) (toIRGenerate right)
toIRGenerate (PlusI _ left right) = IROp OpPlus (toIRGenerate left) (toIRGenerate right)
toIRGenerate (MultF _ left right) = IROp OpMult (toIRGenerate left) (toIRGenerate right)
toIRGenerate (MultI _ left right) = IROp OpMult (toIRGenerate left) (toIRGenerate right)
toIRGenerate (ThetaI _ ix) = IRTheta ix
toIRGenerate (Constant _ x) = IRConst x
toIRGenerate (Null _) = IRConst (VList [])
toIRGenerate (Cons _ hd tl) = IRCons (toIRGenerate hd) (toIRGenerate tl)
toIRGenerate (TCons _ t1 t2) = IRTCons (toIRGenerate t1) (toIRGenerate t2)
toIRGenerate (Uniform _) = IRSample IRUniform
toIRGenerate (Normal _) = IRSample IRNormal
--The following assumes that "name" refers to a function defined within the program. 
toIRGenerate (Call _ name) = IRCall (name ++ "_gen") []
toIRGenerate (Var _ name) = IRVar name
toIRGenerate (Lambda t name subExpr) = IRLambda name (toIRGenerate subExpr)
toIRGenerate (ReadNN t name subexpr) = IRCall "randomchoice" [IREvalNN name (toIRGenerate subexpr)]
toIRGenerate x = error ("found no way to convert to IRGen: " ++ show x)

bindLocal :: String -> IRExpr a -> IRExpr a -> Supply Int (IRExpr a)
bindLocal namestring binding inEx = do
  varName <- mkVariable namestring
  return $ IRLetIn varName binding inEx

toIRIntegrate :: (Show a, Num a) => Expr (StaticAnnotations a) a -> IRExpr a -> IRExpr a -> Supply Int (IRExpr a)
toIRIntegrate (Uniform (StaticAnnotations _ _ tags)) lower higher = do
  varlow <- mkVariable "low"
  varhigh <- mkVariable "high"
  let x = IRIf
            (IROp OpOr (IROp OpGreaterThan (IRVar varlow) (IRConst $ VFloat 1)) (IROp OpGreaterThan (IRConst $ VFloat 0) (IRVar varhigh)))
            (IRConst $ VFloat 0)
            (IROp OpSub (IRVar varhigh) (IRVar varlow))
  return
    (IRLetIn varlow
      (IRIf (IROp OpGreaterThan (IRConst $ VFloat 0) lower) (IRConst $ VFloat 0) lower)
      (IRLetIn varhigh
        (IRIf (IROp OpGreaterThan (IRConst $ VFloat 1) higher) higher (IRConst $ VFloat 1))
        x))
toIRIntegrate x low high = error ("found no way to convert to IRIntegrate: " ++ show x)
