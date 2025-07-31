module SPLL.IntermediateRepresentation (
  IRExpr(..)
, IREnv(..)
, IRFunDecl
, IRFunGroup (..)
, Tag(..)
, Operand(..)
, UnaryOperand(..)
, Distribution(..)
, Varname
, IRValue
, CompilerConfig(..)
, irMap
, getIRSubExprs
, lookupIREnv
, irPrintFlat
, valueToIR
, isLambda
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
             | OpApprox
             deriving (Show, Eq)

data UnaryOperand = OpNeg
                  | OpSign
                  | OpAbs
                  | OpNot
                  | OpExp
                  | OpLog   --Natural Logarithm
                  | OpIsAny
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
              | IRMap IRExpr IRExpr
              | IRTFst IRExpr
              | IRTSnd IRExpr
              | IRLeft IRExpr
              | IRRight IRExpr
              | IRFromLeft IRExpr
              | IRFromRight IRExpr
              | IRIsLeft IRExpr
              | IRIsRight IRExpr
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
              | IRError String
              deriving (Show, Eq)
              
type IRValue = GenericValue IRExpr

data IREnv = IREnv [IRFunGroup] [ADTDecl] deriving (Show)


data IRFunGroup = IRFunGroup {groupName::String, genFun::IRFunDecl, probFun::Maybe IRFunDecl, integFun::Maybe IRFunDecl, groupDoc::String} deriving (Show)

-- Name, Documentation, Body
type IRFunDecl = (IRExpr, String)

data CompilerConfig = CompilerConfig {
  -- If set to Just x: All branches with likelihood less than x are discarded.
  --  Uses local probability of the branch,given that the execution arrives at that branching point
  topKThreshold :: Maybe Double,
  countBranches :: Bool,
  verbose :: Int,
  optimizerLevel :: Int
} deriving (Show)
--3: convert algortihm-and-type-annotated Exprs into abstract representation of explicit computation:
--    Fold enum ranges, algorithms, etc. into a representation of computation that can be directly converted into code.

valueToIR :: GenericValue a -> GenericValue b
valueToIR = fmap (error "Cannot convert VClosure to IR")

lookupIREnv :: String -> IREnv -> IRFunGroup
lookupIREnv name (IREnv env _) = 
  case filter (\IRFunGroup{groupName=a} -> a == name) env of
    [] -> error ("function " ++ show name ++ "not found in environment")
    [a] -> a
    lst -> head lst

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
getIRSubExprs (IRMap f a) = [f, a]
getIRSubExprs (IRElementOf a b) = [a, b]
getIRSubExprs (IRTFst a) = [a]
getIRSubExprs (IRTSnd a) = [a]
getIRSubExprs (IRLeft a) = [a]
getIRSubExprs (IRRight a) = [a]
getIRSubExprs (IRFromLeft a) = [a]
getIRSubExprs (IRFromRight a) = [a]
getIRSubExprs (IRIsLeft a) = [a]
getIRSubExprs (IRIsRight a) = [a]
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
getIRSubExprs (IRError _) = []

irMap :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
irMap f x = case x of
  (IRIf cond left right) -> f (IRIf (irMap f cond) (irMap f left) (irMap f right))
  (IROp op left right) -> f (IROp op (irMap f left) (irMap f right))
  (IRUnaryOp op expr) -> f (IRUnaryOp op (irMap f expr))
  (IRCons left right) -> f (IRCons (irMap f left) (irMap f right))
  (IRTCons left right) -> f (IRTCons (irMap f left) (irMap f right))
  (IRHead expr) -> f (IRHead (irMap f expr))
  (IRTail expr) -> f (IRTail (irMap f expr))
  (IRMap fe expr) -> f (IRMap (irMap f fe) (irMap f expr))
  (IRElementOf ele lst) -> f (IRElementOf (irMap f ele) (irMap f lst))
  (IRTFst expr) -> f (IRTFst (irMap f expr))
  (IRTSnd expr) -> f (IRTSnd (irMap f expr))
  (IRLeft expr) -> f (IRLeft (irMap f expr))
  (IRRight expr) -> f (IRRight (irMap f expr))
  (IRFromLeft expr) -> f (IRFromLeft (irMap f expr))
  (IRFromRight expr) -> f (IRFromRight (irMap f expr))
  (IRIsLeft expr) -> f (IRIsLeft (irMap f expr))
  (IRIsRight expr) -> f (IRIsRight (irMap f expr))
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
  (IRError _) -> f x

isLambda :: IRExpr -> Bool
isLambda IRLambda {} = True
isLambda _ = False

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
irPrintFlat (IRMap _ _) = "IRMap"
irPrintFlat (IRElementOf _ _) = "IRElementOf"
irPrintFlat (IRTFst _) = "IRTFst"
irPrintFlat (IRTSnd _) = "IRTSnd"
irPrintFlat (IRLeft _) = "IRLeft"
irPrintFlat (IRRight _) = "IRRight"
irPrintFlat (IRFromLeft _) = "IRFromLeft"
irPrintFlat (IRFromRight _) = "IRFromRight"
irPrintFlat (IRIsLeft _) = "IRIsLeft"
irPrintFlat (IRIsRight _) = "IRIsRight"
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
irPrintFlat (IRError _) = "IRError"

