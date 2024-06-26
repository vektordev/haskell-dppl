module SPLL.IntermediateRepresentation (
  IRExpr(..)
, StaticAnnotations(..)
, Tag(..)
, Operand(..)
, UnaryOperand(..)
, Distribution(..)
, Varname
, irMap
) where

import SPLL.Lang
import SPLL.Typing.RType
import SPLL.Typing.PType
import SPLL.Analysis
import SPLL.Typing.Typing

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
              | IRCumulative Distribution (IRExpr a)
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
  (IRCumulative a expr) -> f (IRCumulative a (irMap f expr))
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

