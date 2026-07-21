{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
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
, defaultCompilerConfig
, irMap
, irDescend
, getIRSubExprs
, isPure
, isEffectfulVar
, lookupIREnv
, irPrintFlat
, valueToIR
, isLambda
, IfMode(..)
, pattern IRIf
, pattern IRSelect
, pattern VProbDim
, pattern VProbDimBC
, resultImpossible
) where

import SPLL.Lang.Types
import SPLL.Typing.RType (RType(..))
import SPLL.Typing.PType()
import SPLL.Typing.Typing()
import Data.Data()
import Data.List (isSuffixOf)

-- | The probability-mode result layout, as produced by 'SPLL.IRCompiler.packResult':
--
-- >  (prob, (dim, (branchCount, impossible)))    -- countBranches on
-- >  (prob, (dim, impossible))                   -- countBranches off
--
-- The impossibility flag is an internal side-channel (design
-- inference-result-side-channels): it tells a mixture which alternatives are
-- structurally inapplicable, instead of that being re-derived by comparing a
-- probability to zero. It is not stripped from the emitted result yet, so
-- consumers match through these patterns rather than on the tuple shape, which
-- is the layout's only definition outside the compiler.
pattern VProbDim :: Double -> Double -> IRValue
pattern VProbDim p d <- (probDimOf -> Just (p, d))

pattern VProbDimBC :: Double -> Double -> Double -> IRValue
pattern VProbDimBC p d bc <- (probDimBCOf -> Just (p, d, bc))

probDimOf :: IRValue -> Maybe (Double, Double)
probDimOf (VTuple (VFloat p) (VTuple (VFloat d) _)) = Just (p, d)
probDimOf _                                         = Nothing

probDimBCOf :: IRValue -> Maybe (Double, Double, Double)
probDimBCOf (VTuple (VFloat p) (VTuple (VFloat d) (VTuple (VFloat bc) _))) = Just (p, d, bc)
probDimBCOf _                                                             = Nothing

-- | The impossibility flag of a result, when the layout carries one.
resultImpossible :: IRValue -> Maybe Bool
resultImpossible (VTuple _ (VTuple _ (VBool imp)))            = Just imp
resultImpossible (VTuple _ (VTuple _ (VTuple _ (VBool imp)))) = Just imp
resultImpossible _                                            = Nothing

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

-- | Strictness of an 'IRIfMode' node (design pytorch-tensorizer, M1).
--
-- A 'LazyIf' is the ordinary conditional: exactly one arm is evaluated. A
-- 'SelectIf' is a /select/: both arms are computed and combined by a mask.
-- Every if leaves 'IRCompiler' as 'LazyIf'; the batched-mode select pass
-- (see 'SPLL.IRSelectPass') retags the data-dependent, elementwise-eligible
-- ones to 'SelectIf'. Scalar backends lower both identically (a lazy ternary),
-- so retagging is a behavioural no-op today; a future batched backend lowers
-- 'SelectIf' to @torch.where@. The flag lives on the if rather than in a
-- separate node so the ~130 existing if sites -- which neither know nor care
-- about select semantics -- keep matching/constructing through the 'IRIf'
-- pattern synonym unchanged.
data IfMode = LazyIf | SelectIf deriving (Show, Eq)

data IRExpr = IRIfMode IfMode IRExpr IRExpr IRExpr
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
              -- auxiliary construct to aid enumeration: bind each enumerated Value to the Varname and evaluate the subexpr. Sum results.
              -- maybe we can instead move this into some kind of standard library.
              | IREnumSum Varname MultiValue IRExpr
              | IRIsPossible MultiValue IRExpr
              | IRIndex IRExpr IRExpr
              | IRError String
              -- Runtime type-tag check: True iff the value of the sub-expression
              -- structurally conforms to the given RType. Emitted only as the
              -- query-type guard at a prob/integ function root (see IRCompiler),
              -- so a wrong-typed query value fails with a clear diagnostic instead
              -- of a silent bogus number or a deep "not a boolean" panic.
              | IRConformsTo RType IRExpr
              deriving (Show, Eq)

-- | A conditional of unspecified strictness. As a /pattern/ it matches an if
-- of either mode (callers that don't distinguish select from lazy see a plain
-- three-field if); as a /constructor/ it builds a 'LazyIf'. This is what keeps
-- the existing if sites source-compatible after the 'IfMode' field was added.
pattern IRIf :: IRExpr -> IRExpr -> IRExpr -> IRExpr
pattern IRIf c t e <- IRIfMode _ c t e where
        IRIf c t e = IRIfMode LazyIf c t e

-- | A select: both arms are evaluated and combined by a mask on @cond@.
pattern IRSelect :: IRExpr -> IRExpr -> IRExpr -> IRExpr
pattern IRSelect c t e = IRIfMode SelectIf c t e

{-# COMPLETE IRIf, IROp, IRUnaryOp, IRTheta, IRSubtree, IRConst, IRCons
  , IRElementOf, IRTCons, IRHead, IRTail, IRMap, IRTFst, IRTSnd, IRLeft
  , IRRight, IRFromLeft, IRFromRight, IRIsLeft, IRIsRight, IRDensity
  , IRCumulative, IRSample, IRLetIn, IRVar, IRLambda, IRApply, IREnumSum
  , IRIsPossible, IRIndex, IRError, IRConformsTo #-}

type IRValue = GenericValue IRExpr

data IREnv = IREnv [IRFunGroup] [ADTDecl] [(String, IRValue)] deriving (Show)


data IRFunGroup = IRFunGroup {groupName::String, genFun::Maybe IRFunDecl, probFun::Maybe IRFunDecl, integFun::Maybe IRFunDecl, encodeFun::Maybe IRFunDecl, normalFun::Maybe IRFunDecl, groupDoc::String} deriving (Show)

-- Name, Documentation, Body
type IRFunDecl = (IRExpr, String)

data CompilerConfig = CompilerConfig {
  -- If set to Just x: All branches with likelihood less than x are discarded.
  --  Uses local probability of the branch,given that the execution arrives at that branching point
  topKThreshold :: Maybe Double,
  countBranches :: Bool,
  verbose :: Int,
  optimizerLevel :: Int,
  pruneAnyChecks :: Bool,
  noIntegrate :: Bool,
  noProbability :: Bool,
  noGenerate :: Bool,
  -- When True, print every intermediate AST state during compilation (with full TypeInfo/tags)
  showIntermediates :: Bool,
  -- When True (default), the prob/integ function root is wrapped in a guard that
  -- checks the query value structurally conforms to the program's return type,
  -- failing with a clear diagnostic on a mismatch. Independent of optimizerLevel.
  -- Disable (CLI --noTypeCheck) to shave the entry check off hot compiled code.
  checkQueryType :: Bool,
  -- When True (CLI --batched), opt into batched inference mode (design
  -- pytorch-tensorizer). M1 wires only the backend-agnostic select pass, which
  -- retags data-dependent elementwise ifs to SelectIf; scalar lowering is
  -- unchanged, so today this is a behavioural no-op over the tensor fragment.
  batched :: Bool
} deriving (Show)

defaultCompilerConfig :: CompilerConfig
defaultCompilerConfig = CompilerConfig {countBranches = False, topKThreshold = Nothing, optimizerLevel = 2, verbose = 0, pruneAnyChecks = False, noIntegrate=False, noProbability=False, noGenerate=False, showIntermediates=False, checkQueryType=True, batched=False}
--3: convert algortihm-and-type-annotated Exprs into abstract representation of explicit computation:
--    Fold enum ranges, algorithms, etc. into a representation of computation that can be directly converted into code.

valueToIR :: GenericValue a -> GenericValue b
valueToIR = fmap (error "Cannot convert VClosure to IR")

lookupIREnv :: String -> IREnv -> IRFunGroup
lookupIREnv name (IREnv env _ _) =
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
getIRSubExprs (IRIsPossible _ a) = [a]
getIRSubExprs (IRDensity _ a) = [a]
getIRSubExprs (IRCumulative _ a) = [a]
getIRSubExprs (IRSample _) = []
getIRSubExprs (IRLetIn _ a b) = [a, b]
getIRSubExprs (IRVar _) = []
getIRSubExprs (IRLambda _ a) = [a]
getIRSubExprs (IRApply a b) = [a, b]
getIRSubExprs (IREnumSum _ _ a) = [a]
getIRSubExprs (IRIndex a b) = [a, b]
getIRSubExprs (IRError _) = []
getIRSubExprs (IRConformsTo _ a) = [a]

-- | True if an @IRVar name@ reference is *effectful* -- i.e. a reference to a
-- top-level generator function, whose evaluation draws randomness. The IR uses
-- @IRVar@ for two semantically different things: a pure value reference (a
-- lambda parameter, let binding, or enumSum loop variable, free to duplicate)
-- and a nullary generator call such as @coin_gen@. \"Referencing\" the latter
-- actually /runs the sampler/: the interpreter re-evaluates the bound expression
-- on every lookup and code generation renders it as a call, so duplicating the
-- reference duplicates the random draw (task ir-effectful-var-purity).
--
-- Generator references are recognised by the @_gen@ name suffix that
-- 'SPLL.IRCompiler' appends to every inference-carrying top-level declaration
-- (this also covers neural @_auto_gen@). A @_gen@ reference that names a
-- /function/ rather than a nullary sampler is itself a pure closure value, but
-- treating it conservatively as effectful only ever forgoes an optimization --
-- it never changes semantics -- so this predicate does not try to tell them
-- apart.
isEffectfulVar :: String -> Bool
isEffectfulVar name = "_gen" `isSuffixOf` name

-- | True if evaluating the expression has no observable side effect, so it is
-- safe both to duplicate (inline into several uses) and to collapse repeated
-- occurrences into one shared binding. The two effects are drawing a random
-- sample ('IRSample') and referencing a generator function ('isEffectfulVar').
--
-- This is the single mechanism every duplicating or sharing optimizer rewrite
-- consults, replacing the ad-hoc per-pass assumptions this class of bug used to
-- rely on: @optimizeLetIns@' \"never duplicate a non-'IRConst' binding\" and
-- CSE's \"a subexpression is pure iff it contains no 'IRSample'\" -- the latter
-- silently misclassified an expression built from a generator reference as
-- pure and could collapse two independent draws into one (task
-- ir-effectful-var-purity).
isPure :: IRExpr -> Bool
isPure (IRSample _) = False
isPure (IRVar name) = not (isEffectfulVar name)
isPure e            = all isPure (getIRSubExprs e)

irMap :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
irMap f x = f (irDescend (irMap f) x)

-- | Apply @f@ to the immediate children of a node, rebuilding it. One level
-- only -- unlike 'irMap' it does not recurse, so the caller controls the
-- traversal. This is what a scope-aware rewrite needs: it can handle the
-- binding forms itself (threading an environment through 'IRLetIn'/'IRLambda'/
-- 'IREnumSum' scopes) and delegate every other constructor here, instead of
-- re-listing the whole 35-constructor AST.
irDescend :: (IRExpr -> IRExpr) -> IRExpr -> IRExpr
irDescend f x = case x of
  -- Match the real constructor so a SelectIf tag survives the rebuild; the
  -- bare 'IRIf' synonym would reconstruct it as LazyIf and drop the flag.
  (IRIfMode m cond left right) -> IRIfMode m (f cond) (f left) (f right)
  (IROp op left right) -> IROp op (f left) (f right)
  (IRUnaryOp op expr) -> IRUnaryOp op (f expr)
  (IRCons left right) -> IRCons (f left) (f right)
  (IRTCons left right) -> IRTCons (f left) (f right)
  (IRHead expr) -> IRHead (f expr)
  (IRTail expr) -> IRTail (f expr)
  (IRMap fe expr) -> IRMap (f fe) (f expr)
  (IRElementOf ele lst) -> IRElementOf (f ele) (f lst)
  (IRTFst expr) -> IRTFst (f expr)
  (IRTSnd expr) -> IRTSnd (f expr)
  (IRLeft expr) -> IRLeft (f expr)
  (IRRight expr) -> IRRight (f expr)
  (IRFromLeft expr) -> IRFromLeft (f expr)
  (IRFromRight expr) -> IRFromRight (f expr)
  (IRIsLeft expr) -> IRIsLeft (f expr)
  (IRIsRight expr) -> IRIsRight (f expr)
  (IRIsPossible val expr) -> IRIsPossible val (f expr)
  (IRDensity a expr) -> IRDensity a (f expr)
  (IRCumulative a expr) -> IRCumulative a (f expr)
  (IRLetIn name left right) -> IRLetIn name (f left) (f right)
  (IRLambda name scope) -> IRLambda name (f scope)
  (IRApply a b) -> IRApply (f a) (f b)
  (IREnumSum name val scope) -> IREnumSum name val (f scope)
  (IRIndex left right) -> IRIndex (f left) (f right)
  (IRTheta a i) -> IRTheta (f a) i
  (IRSubtree a i) -> IRSubtree (f a) i
  (IRConst _) -> x
  (IRSample _) -> x
  (IRVar _) -> x
  (IRError _) -> x
  (IRConformsTo t a) -> IRConformsTo t (f a)

isLambda :: IRExpr -> Bool
isLambda IRLambda {} = True
isLambda _ = False

irPrintFlat :: IRExpr -> String
irPrintFlat (IRIfMode LazyIf _ _ _) = "IRIf"
irPrintFlat (IRIfMode SelectIf _ _ _) = "IRSelect"
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
irPrintFlat (IRIsPossible _ _) = "IRIsPossible"
irPrintFlat (IRDensity _ _) = "IRDensity"
irPrintFlat (IRCumulative _ _) = "IRCumulative"
irPrintFlat (IRSample _) = "IRSample"
irPrintFlat (IRLetIn _ _ _) = "IRLetIn"
irPrintFlat (IRVar _) = "IRVar"
irPrintFlat (IRLambda _ _) = "IRLambda"
irPrintFlat (IRApply _ _) = "IRApply"
irPrintFlat (IREnumSum _ _ _) = "IREnumSum"
irPrintFlat (IRIndex _ _) = "IRIndex"
irPrintFlat (IRError _) = "IRError"
irPrintFlat (IRConformsTo _ _) = "IRConformsTo"

