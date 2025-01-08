module SPLL.IntermediateRepresentation (
  IRExpr(..)
, Tag(..)
, Operand(..)
, UnaryOperand(..)
, Distribution(..)
, Varname
, IRValue
, CompilerConfig(..)
, irMap
, getIRSubExprs
, irPrintFlat
, valueToIR
) where

import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Typing.Typing
import Data.Data

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

type M a = ContT Int (State IRExpr)

--runM :: M a IRExpr -> IRExpr
runM m = evalState (runContT m return) 0

genName :: String -> M a Varname
genName base = do
  i <- get
  let name = "$" ++ show i ++ "_" ++ base
  put (i + 1)
  return name

letin :: String -> IRExpr -> M a Varname
letin base rhs = do
  name <- genName base
  ContT (\f -> IRLetIn name rhs <$> f name)
-}
--generateCode :: M a IRExpr
--generateCode = do
--  varName <- letin "some_string" (IRLit 10)
--  subex <- subCode varName
--  return (IRAdd (IRVar varName) subex)

-- returs var + 3, using a let binding
--subCode :: Varname -> M a IRExpr
--subCode v = do
--  a <- letin "a" (IRLit 3)
--  return (IRAdd (IRVar a) (IRVar v))

type Varname = String

data Operand = OpPlus
             | OpMult
             | OpGreaterThan
             | OpLessThan
             | OpDiv
             | OpSub
             | OpOr
             | OpAnd
             | OpEq
             deriving (Show, Eq)

data UnaryOperand = OpNeg
                  | OpAbs
                  | OpNot
                  | OpExp
                  | OpLog   --Natural Logarithm
                  deriving (Show, Eq)

data Distribution = IRNormal | IRUniform deriving (Show, Eq)

data IRExpr = IRIf IRExpr IRExpr IRExpr
              | IROp Operand IRExpr IRExpr
              | IRUnaryOp UnaryOperand IRExpr
              | IRTheta IRExpr Int
              | IRSubtree IRExpr Int
              | IRConst IRValue
              | IRCons IRExpr IRExpr
              | IRElementOf IRExpr IRExpr
              | IRTCons IRExpr IRExpr
              | IRHead IRExpr
              | IRTail IRExpr
              | IRTFst IRExpr
              | IRTSnd IRExpr
              | IRDensity Distribution IRExpr
              | IRCumulative Distribution IRExpr
              | IRSample Distribution
              | IRLetIn Varname IRExpr IRExpr
              | IRVar Varname
              | IRLambda String IRExpr
              | IRApply IRExpr IRExpr
              | IRInvoke IRExpr -- Only relevant for CodeGen. States that the last argument has been applied to a function
              -- auxiliary construct to aid enumeration: bind each enumerated Value to the Varname and evaluate the subexpr. Sum results.
              -- maybe we can instead move this into some kind of standard library.
              | IREnumSum Varname IRValue IRExpr
              | IREvalNN Varname IRExpr
              | IRIndex IRExpr IRExpr
              deriving (Show, Eq)
              
type IRValue = GenericValue IRExpr


data CompilerConfig = CompilerConfig {
  -- If set to Just x: All branches with likelihood less than x are discarded.
  --  Uses local probability of the branch,given that the execution arrives at that branching point
  topKThreshold :: Maybe Double,
  countBranches :: Bool,
  verbose :: Int
} deriving (Show)
--3: convert algortihm-and-type-annotated Exprs into abstract representation of explicit computation:
--    Fold enum ranges, algorithms, etc. into a representation of computation that can be directly converted into code.

valueToIR :: GenericValue a -> GenericValue b
valueToIR (VBool b) = VBool b
valueToIR (VInt i) = VInt i
valueToIR (VSymbol s) = VSymbol s
valueToIR (VFloat d) = VFloat d
valueToIR (VList xs) = VList (map valueToIR xs)
valueToIR (VTuple x y) = VTuple (valueToIR x) (valueToIR y)
valueToIR (VBranch x y s) = VBranch (valueToIR x) (valueToIR y) s
valueToIR (VThetaTree t) = VThetaTree t
valueToIR VAnyList = VAnyList
valueToIR VClosure{} = error "Cannot convert VClosure to IR"

getIRSubExprs :: IRExpr -> [IRExpr]
getIRSubExprs (IRIf a b c) = [a, b, c]
getIRSubExprs (IROp _ a b) = [a, b]
getIRSubExprs (IRUnaryOp _ a) = [a]
getIRSubExprs (IRTheta a _) = [a]
getIRSubExprs (IRSubtree a _) = [a]
getIRSubExprs (IRConst _) = []
getIRSubExprs (IRCons a b) = [a, b]
getIRSubExprs (IRTCons a b) = [a, b]
getIRSubExprs (IRHead a) = [a]
getIRSubExprs (IRTail a) = [a]
getIRSubExprs (IRElementOf a b) = [a, b]
getIRSubExprs (IRTFst a) = [a]
getIRSubExprs (IRTSnd a) = [a]
getIRSubExprs (IRDensity _ a) = [a]
getIRSubExprs (IRCumulative _ a) = [a]
getIRSubExprs (IRSample _) = []
getIRSubExprs (IRLetIn _ a b) = [a, b]
getIRSubExprs (IRVar _) = []
getIRSubExprs (IRInvoke a) = [a]
getIRSubExprs (IRLambda _ a) = [a]
getIRSubExprs (IRApply a b) = [a, b]
getIRSubExprs (IREnumSum _ _ a) = [a]
getIRSubExprs (IREvalNN _ a) = [a]
getIRSubExprs (IRIndex a b) = [a, b]

irMap :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
irMap f x = case x of
  (IRIf cond left right) -> f (IRIf (irMap f cond) (irMap f left) (irMap f right))
  (IROp op left right) -> f (IROp op (irMap f left) (irMap f right))
  (IRUnaryOp op expr) -> f (IRUnaryOp op (irMap f expr))
  (IRCons left right) -> f (IRCons (irMap f left) (irMap f right))
  (IRTCons left right) -> f (IRTCons (irMap f left) (irMap f right))
  (IRHead expr) -> f (IRHead (irMap f expr))
  (IRTail expr) -> f (IRTail (irMap f expr))
  (IRElementOf ele lst) -> f (IRElementOf (irMap f ele) (irMap f lst))
  (IRTFst expr) -> f (IRTFst (irMap f expr))
  (IRTSnd expr) -> f (IRTSnd (irMap f expr))
  (IRDensity a expr) -> f (IRDensity a (irMap f expr))
  (IRCumulative a expr) -> f (IRCumulative a (irMap f expr))
  (IRLetIn name left right) -> f (IRLetIn name (irMap f left) (irMap f right))
  (IRLambda name scope) -> f (IRLambda name (irMap f scope))
  (IRApply a b) -> f (IRApply (irMap f a) (irMap f b))
  (IRInvoke expr) -> f (IRInvoke (irMap f expr))
  (IREnumSum name val scope) -> f (IREnumSum name val (irMap f scope))
  (IREvalNN name arg) -> f (IREvalNN name (irMap f arg))
  (IRIndex left right) -> f (IRIndex (irMap f left) (irMap f right))
  (IRTheta a i) -> f (IRTheta (irMap f a) i)
  (IRSubtree a i) -> f (IRSubtree (irMap f a) i)
  (IRConst _) -> f x
  (IRSample _) -> f x
  (IRVar _) -> f x

irPrintFlat :: IRExpr -> String
irPrintFlat (IRIf _ _ _) = "IRIf"
irPrintFlat (IROp _ _ _) = "IROp"
irPrintFlat (IRUnaryOp _ _) = "IRUnaryOp"
irPrintFlat (IRTheta _ _) = "IRTheta"
irPrintFlat (IRSubtree _ _) = "IRSubtree"
irPrintFlat (IRConst _) = "IRConst"
irPrintFlat (IRCons _ _) = "IRCons"
irPrintFlat (IRTCons _ _) = "IRTCons"
irPrintFlat (IRHead _) = "IRHead"
irPrintFlat (IRTail _) = "IRTail"
irPrintFlat (IRElementOf _ _) = "IRElementOf"
irPrintFlat (IRTFst _) = "IRTFst"
irPrintFlat (IRTSnd _) = "IRTSnd"
irPrintFlat (IRDensity _ _) = "IRDensity"
irPrintFlat (IRCumulative _ _) = "IRCumulative"
irPrintFlat (IRSample _) = "IRSample"
irPrintFlat (IRLetIn _ _ _) = "IRLetIn"
irPrintFlat (IRVar _) = "IRVar"
irPrintFlat (IRLambda _ _) = "IRLambda"
irPrintFlat (IRApply _ _) = "IRApply"
irPrintFlat (IRInvoke _) = "IRInvoke"
irPrintFlat (IREnumSum _ _ _) = "IREnumSum"
irPrintFlat (IREvalNN name _) = "IREvalNN " ++ name
irPrintFlat (IRIndex _ _) = "IRIndex"

