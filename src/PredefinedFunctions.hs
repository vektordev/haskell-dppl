module PredefinedFunctions (
globalFEnv,
lookupFPair,
soleOutputVar,
inversionFor,
FPair(..),
FDecl(..),
FEnv,
instantiate,
propagateValues,
parameterCount,
hasAnyExcept,
isHigherOrder,
isFieldConstructor,
getFunctionParamIdx,
renameDecl
) where

import SPLL.Typing.RType (RType(..), Scheme(..), TVarR(..), ClassConstraint(..))
import SPLL.IntermediateRepresentation (IRExpr, IRExpr(..), Operand(..), UnaryOperand(..), Builtin(..), ConTag(..), Accessor(..), irMap, IREnv (IREnv), getIRSubExprs) --FIXME
import SPLL.Lang.Lang
import Data.Maybe (fromJust, fromMaybe)
import SPLL.Lang.Types
import IRInterpreter
import qualified Data.Bifunctor
import StandardLibrary (invokeStandardFunction, stdListProd)
import SPLL.Typing.AlgebraicDataTypes (implicitFunctionApplicable)

-- | The placeholder value standing for "anything at all" in the slot typed
-- @rt@ of a container an inverse reconstructs.
--
-- Several inverses rebuild a container purely so the caller can immediately
-- tear it apart again: @head L == s@ inverts to @L = Cons(s, <hole>)@, whose
-- head and tail the construction branch then reads back out. The hole is never
-- meant to exist as a value, but it *is* emitted, and at @-O0@ nothing folds
-- the round trip away -- so the emitted Julia and Python evaluate it for real.
--
-- Both backends model a list as a distinct runtime type (@InferenceList@),
-- so a scalar hole in a *list* slot is not merely useless but ill-typed:
-- @prepend(x, "ANY")@ is a Julia @MethodError@. The list-shaped hole
-- (@AnyInferenceList@ / 'AnyList') is a legal member of that type, and
-- @isAny@ recognises it in all three backends, so it behaves identically
-- wherever the scalar one would have worked.
--
-- Every other slot takes the scalar 'VAny': the container types are
-- structurally typed at runtime and @isAny@ only recognises these two forms,
-- so a "recursive" hole such as @VTuple VAny VAny@ would read as an ordinary
-- tuple and be compared component-wise instead of matching anything.
anyOfType :: RType -> GenericValue a
anyOfType (ListOf _) = VList AnyList
anyOfType _          = VAny

-- InputVars, OutputVars, fwd, grad
data FDecl = FDecl {contract :: Scheme, inputVars :: [String], outputVars :: [String], body :: IRExpr, applicability :: IRExpr, deconstructing :: Bool, derivatives :: [(String, IRExpr)]} deriving (Show, Eq)
-- Forward, inverse
data FPair = FPair {forwardDecl :: FDecl, inverseDecl :: [FDecl]} deriving (Show, Eq)
type FEnv = [(String, FPair)]

-- | The forward/inverse declaration pair of a known InjF. Every InjF name in an
-- annotated AST was resolved against this same environment by the parser, which
-- rejects the unknown ones, so a miss downstream is an internal inconsistency
-- rather than anything an SPLL program can express.
lookupFPair :: [ADTDecl] -> String -> FPair
lookupFPair adtsDecl name = fromMaybe (error ("Unknown InjF: " ++ name)) (lookup name (globalFEnv adtsDecl))

-- | The single output variable of an InjF declaration. Every FDecl in
-- 'globalFEnv' has exactly one; the field is a list only to mirror 'inputVars'.
soleOutputVar :: FDecl -> String
soleOutputVar FDecl{outputVars=[v]} = v
soleOutputVar d = error ("InjF declaration has output variables " ++ show (outputVars d)
                         ++ "; exactly one is required")

-- | The one inverse declaration that solves for @v@. An InjF declares at most
-- one inversion per input variable, so both "none" and "several" mean the
-- declaration table disagrees with the caller about which variable is invertible.
inversionFor :: String -> String -> [FDecl] -> FDecl
inversionFor name v inversions = case [d | d <- inversions, outputVars d == [v]] of
  [d] -> d
  ds  -> error ("InjF '" ++ name ++ "' has " ++ show (length ds)
                ++ " inversions solving for '" ++ v ++ "'; exactly one is required")

-- ============================ UNARY ARITHMETIC ============================

doubleFwd :: FDecl
doubleFwd = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["a"] ["b"] (IROp OpMult (IRVar "a") (IRConst $ VFloat 2)) (IRConst (VBool True)) False [("a", IRConst $ VFloat 2)]
doubleInv :: FDecl
doubleInv = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["b"] ["a"] (IROp OpDiv (IRVar "b") (IRConst $ VFloat 2)) (IRConst (VBool True)) False [("b", IRConst $ VFloat 0.5)]

expFwd :: FDecl
expFwd = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["a"] ["b"] (IRUnaryOp OpExp (IRVar "a")) (IRConst (VBool True)) False [("a", IRUnaryOp OpExp (IRVar "a"))]
expInv :: FDecl
expInv = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["b"] ["a"] (IRUnaryOp OpLog (IRVar "b")) (IROp OpGreaterThan (IRVar "b") (IRConst $ VFloat 0)) False [("b", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))]

negFwd :: FDecl
negFwd = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["a"] ["b"] (IRUnaryOp OpNeg (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat (-1)))]
negInv :: FDecl
negInv = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["b"] ["a"] (IRUnaryOp OpNeg (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat (-1)))]
negIFwd :: FDecl
negIFwd = FDecl (Forall [] [] (TArrow TInt TInt)) ["a"] ["b"] (IRUnaryOp OpNeg (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat (-1)))]
negIInv :: FDecl
negIInv = FDecl (Forall [] [] (TArrow TInt TInt)) ["b"] ["a"] (IRUnaryOp OpNeg (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat (-1)))]

recipFwd :: FDecl
recipFwd = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["a"] ["b"] (IROp OpDiv (IRConst (VFloat 1)) (IRVar "a")) (IRConst (VBool True)) False [("a", IRUnaryOp OpNeg (IROp OpDiv (IRConst (VFloat 1)) (IROp OpMult (IRVar "a") (IRVar "a"))))]
recipInv :: FDecl
-- 1/a is never 0, so a zero observation is impossible rather than a division
-- by zero producing NaN/Inf in the reported density.
recipInv = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["b"] ["a"] (IROp OpDiv (IRConst (VFloat 1)) (IRVar "b")) (IRUnaryOp OpNot (IROp OpEq (IRVar "b") (IRConst $ VFloat 0))) False [("b", IRUnaryOp OpNeg (IROp OpDiv (IRConst (VFloat 1)) (IROp OpMult (IRVar "b") (IRVar "b"))))]

-- sqrt via exp(0.5*log x) (no dedicated OpSqrt); defined on the positive reals.
-- Forward derivative d/da sqrt(a) = 0.5 / sqrt(a). Inverse is squaring.
sqrtFwd :: FDecl
sqrtFwd = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["a"] ["b"] (IRUnaryOp OpExp (IROp OpMult (IRConst (VFloat 0.5)) (IRUnaryOp OpLog (IRVar "a")))) (IROp OpGreaterThan (IRVar "a") (IRConst (VFloat 0))) False [("a", IROp OpDiv (IRConst (VFloat 0.5)) (IRUnaryOp OpExp (IROp OpMult (IRConst (VFloat 0.5)) (IRUnaryOp OpLog (IRVar "a")))))]
-- Applicable only on the image of sqrt, [0, inf): squaring happily maps a
-- negative observation back into the argument's support (p(sqrt(X) = -0.5)
-- would otherwise report X's density at 0.25), so the observation itself has
-- to be tested. Spelled as not(b < 0) for want of an OpGeq, and inclusive of 0.
sqrtInv :: FDecl
sqrtInv = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["b"] ["a"] (IROp OpMult (IRVar "b") (IRVar "b")) (IRUnaryOp OpNot (IROp OpLessThan (IRVar "b") (IRConst $ VFloat 0))) False [("b", IROp OpMult (IRConst (VFloat 2)) (IRVar "b"))]

-- sq (squaring); inverse is sqrt, so it is only invertible on the positive reals.
-- Forward derivative d/da a^2 = 2a.
sqFwd :: FDecl
sqFwd = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["a"] ["b"] (IROp OpMult (IRVar "a") (IRVar "a")) (IRConst (VBool True)) False [("a", IROp OpMult (IRConst (VFloat 2)) (IRVar "a"))]
sqInv :: FDecl
sqInv = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["b"] ["a"] (IRUnaryOp OpExp (IROp OpMult (IRConst (VFloat 0.5)) (IRUnaryOp OpLog (IRVar "b")))) (IROp OpGreaterThan (IRVar "b") (IRConst (VFloat 0))) False [("b", IROp OpDiv (IRConst (VFloat 0.5)) (IRUnaryOp OpExp (IROp OpMult (IRConst (VFloat 0.5)) (IRUnaryOp OpLog (IRVar "b")))))]

leftFwd :: FDecl
leftFwd = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "a") `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["a"] ["b"] (IRConstruct TgLeft [IRVar "a"]) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
-- Partial extractor, kept only to serve as `left`'s inverse (guarded by
-- applicability = isLeft, as before). Not exposed under the "fromLeft" name
-- any more -- see fromLeftMaybeFwd/fromLeftMaybeInv below for that.
fromLeftFwd :: FDecl
fromLeftFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "a"))) ["b"] ["a"] (IRDestruct AcFromLeft (IRVar "b")) (IRDestruct AcIsLeft (IRVar "b")) True [("b", IRConst (VFloat 1))]

rightFwd :: FDecl
rightFwd = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "b") `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["a"] ["b"] (IRConstruct TgRight [IRVar "a"]) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
-- Partial extractor, kept only to serve as `right`'s inverse. See fromRightFwd's
-- comment above.
fromRightFwd :: FDecl
fromRightFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "b"))) ["b"] ["a"] (IRDestruct AcFromRight (IRVar "b")) (IRDestruct AcIsRight (IRVar "b")) True [("b", IRConst (VFloat 1))]

-- Total, Maybe-returning fromLeft/fromRight (the surfaced "fromLeft"/"fromRight"
-- InjF names). Maybe a is represented as Either () a (Haskell convention:
-- Nothing = Left (), Just x = Right x -- see maybe-partial-functions task doc).
-- fromLeft (Left x) = Just x = Right x; fromLeft (Right _) = Nothing = Left ().
-- Always applicable (total), so no zero-guard is needed at the call site.
fromLeftMaybeFwd :: FDecl
fromLeftMaybeFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TEither TUnit (TVarR (TV "a"))))
  ["b"] ["m"]
  (IRIf (IRDestruct AcIsLeft (IRVar "b")) (IRConstruct TgRight [IRDestruct AcFromLeft (IRVar "b")]) (IRConstruct TgLeft [IRConst VUnit]))
  (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]
fromLeftMaybeInv :: FDecl
fromLeftMaybeInv = FDecl (Forall [TV "a", TV "b"] [] (TEither TUnit (TVarR (TV "a")) `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b"))))
  ["m"] ["b"]
  (IRIf (IRDestruct AcIsRight (IRVar "m")) (IRConstruct TgLeft [IRDestruct AcFromRight (IRVar "m")]) (IRConstruct TgRight [IRConst VAny]))
  (IRConst (VBool True)) True [("m", IRConst (VFloat 1))]

fromRightMaybeFwd :: FDecl
fromRightMaybeFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TEither TUnit (TVarR (TV "b"))))
  ["b"] ["m"]
  (IRIf (IRDestruct AcIsRight (IRVar "b")) (IRConstruct TgRight [IRDestruct AcFromRight (IRVar "b")]) (IRConstruct TgLeft [IRConst VUnit]))
  (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]
fromRightMaybeInv :: FDecl
fromRightMaybeInv = FDecl (Forall [TV "a", TV "b"] [] (TEither TUnit (TVarR (TV "b")) `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b"))))
  ["m"] ["b"]
  (IRIf (IRDestruct AcIsRight (IRVar "m")) (IRConstruct TgRight [IRDestruct AcFromRight (IRVar "m")]) (IRConstruct TgLeft [IRConst VAny]))
  (IRConst (VBool True)) True [("m", IRConst (VFloat 1))]

isLeftFwd :: FDecl
isLeftFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TBool)) ["a"] ["b"] (IRDestruct AcIsLeft (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
isLeftInv :: FDecl
isLeftInv = FDecl (Forall [TV "a", TV "b"] [] (TBool `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRIf (IRVar "b") (IRConst $ VEither (Left VAny)) (IRConst $ VEither (Right VAny))) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

isRightFwd :: FDecl
isRightFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TBool)) ["a"] ["b"] (IRDestruct AcIsRight (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
isRightInv :: FDecl
isRightInv = FDecl (Forall [TV "a", TV "b"] [] (TBool `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRIf (IRVar "b") (IRConst $ VEither (Right VAny)) (IRConst $ VEither (Left VAny))) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

plusFwd :: FDecl
plusFwd = FDecl (Forall [TV "a"] [CNum (TV "a")] (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "a")))) ["a", "b"] ["c"] (IROp OpPlus (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]
plusInv1 :: FDecl
plusInv1 = FDecl (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["a", "c"] ["b"] (IROp OpSub (IRVar "c") (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))]
plusInv2 :: FDecl
plusInv2 = FDecl (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["b", "c"] ["a"] (IROp OpSub (IRVar "c") (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))]

multFwd :: FDecl
multFwd = FDecl (Forall [TV "a"] [CNum (TV "a")] (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "a")))) ["a", "b"] ["c"] (IROp OpMult (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRVar "b"), ("b", IRVar "a")]
multInv1 :: FDecl
multInv1 = FDecl (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["a", "c"] ["b"] (IROp OpDiv (IRVar "c") (IRVar "a")) (IRConst (VBool True)) False [("a", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "a") (IRVar "a")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "a"))]
multInv2 :: FDecl
multInv2 = FDecl (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["b", "c"] ["a"] (IROp OpDiv (IRVar "c") (IRVar "b")) (IRConst (VBool True)) False [("b", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "b") (IRVar "b")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))]

plusIFwd :: FDecl
plusIFwd = FDecl (Forall [] [] (TInt `TArrow` (TInt `TArrow` TInt))) ["a", "b"] ["c"] (IROp OpPlus (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]
plusIInv1 :: FDecl
plusIInv1 = FDecl (Forall [] [] (TInt `TArrow` (TInt `TArrow` TInt))) ["a", "c"] ["b"] (IROp OpSub (IRVar "c") (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))]
plusIInv2 :: FDecl
plusIInv2 = FDecl (Forall [] [] (TInt `TArrow` (TInt `TArrow` TInt))) ["b", "c"] ["a"] (IROp OpSub (IRVar "c") (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))]

multIFwd :: FDecl
multIFwd = FDecl (Forall [] [] (TInt `TArrow` (TInt `TArrow` TInt))) ["a", "b"] ["c"] (IROp OpMult (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRVar "b"), ("b", IRVar "a")]
multIInv1 :: FDecl
multIInv1 = FDecl (Forall [] [] (TInt `TArrow` (TInt `TArrow` TInt))) ["a", "c"] ["b"] (IROp OpDiv (IRVar "c") (IRVar "a")) (IRConst (VBool True)) False [("a", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "a") (IRVar "a")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "a"))]
multIInv2 :: FDecl
multIInv2 = FDecl (Forall [] [] (TInt `TArrow` (TInt `TArrow` TInt))) ["b", "c"] ["a"] (IROp OpDiv (IRVar "c") (IRVar "b")) (IRConst (VBool True)) False [("b", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "b") (IRVar "b")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))]

notFwd :: FDecl
notFwd = FDecl (Forall [] [] (TBool `TArrow` TBool)) ["a"] ["b"] (IRUnaryOp OpNot (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
notInv :: FDecl
notInv = FDecl (Forall [] [] (TBool `TArrow` TBool)) ["b"] ["a"] (IRUnaryOp OpNot (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

-- Boolean conjunction/disjunction: forward-only (no point inverse — given a&&b=False
-- and a=False, b is free). They carry an empty inverse list, which routes them to the
-- enumerate-both discrete inference path in IRCompiler rather than the invert-one path.
-- Derivatives are placeholders (booleans are not differentiated).
andFwd :: FDecl
andFwd = FDecl (Forall [] [] (TBool `TArrow` (TBool `TArrow` TBool))) ["a", "b"] ["c"] (IROp OpAnd (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]
orFwd :: FDecl
orFwd = FDecl (Forall [] [] (TBool `TArrow` (TBool `TArrow` TBool))) ["a", "b"] ["c"] (IROp OpOr (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]

-- Comparisons: also forward-only -- given a>b=False there is no point inverse
-- recovering a single operand (a<=b is a half-line, not a point). Continuous
-- comparisons are handled by IRCompiler's own bespoke deterministic-bound /
-- both-PNormal cases (which key off resolved InjF name "gt"/"lt" directly,
-- same as the old bespoke GreaterThan/LessThan constructors did); the empty
-- inverse list here only routes the both-enumerable-discrete case to the
-- generic enumerate-both path (task gt-lt-range-propagation).
gtFwd :: FDecl
gtFwd = FDecl (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TBool))) ["a", "b"] ["c"] (IROp OpGreaterThan (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]
ltFwd :: FDecl
ltFwd = FDecl (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TBool))) ["a", "b"] ["c"] (IROp OpLessThan (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]

-- max: also forward-only, like gt/lt -- given max(a,b)=c there is no single
-- functional inverse recovering one operand from the other. If a is known
-- and a<c then b=c is forced, but if a==c then b can be *any* value <= c: the
-- fiber is set-valued, not a point, exactly the shape task
-- fiber-enumerator-probe-max exists to test. Declaring an empty inverse list
-- (like and/or/gt/lt) routes both-enumerable-discrete and
-- one-side-deterministic cases through IRCompiler's existing isForwardOnly
-- enumerate-both/enumerate-single machinery with NO new IRCompiler code --
-- see the task writeup for what that does and does not prove. Derivatives
-- are placeholders (unused: max never reaches a continuous change-of-variables
-- case, since no inversion is ever looked up for a forward-only InjF).
maxFwd :: FDecl
maxFwd = FDecl (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["a", "b"] ["c"] (IROp OpMax (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]

eqFwd :: FDecl
eqFwd = FDecl (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TBool))) ["a", "b"] ["c"] (IROp OpEq (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]
eqInv1 :: FDecl
eqInv1 = FDecl (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` (TBool `TArrow` TVarR (TV "a")))) ["a", "c"] ["b"] (IRIf (IRVar "c") (IRVar "a") (IRConst (VAnyExcept [IRVar "a"]))) (IRConst (VBool True)) True [("a", IRConst (VFloat 1)), ("c", IRConst (VFloat 1))]
eqInv2 :: FDecl
eqInv2 = FDecl (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` (TBool `TArrow` TVarR (TV "a")))) ["b", "c"] ["a"] (IRIf (IRVar "c") (IRVar "b") (IRConst (VAnyExcept [IRVar "b"]))) (IRConst (VBool True)) True [("b", IRConst (VFloat 1)), ("c", IRConst (VFloat 1))]
-- ============================ FIELD CONSTRUCTORS ============================
-- Cons/TCons are field constructors: each field is independently recoverable
-- from the constructed value via a deconstructing inverse (head/tail, fst/snd).
-- This mirrors the FPair shape produced for user-ADT constructors by
-- fPairsFromADT, so list/tuple construction folds into the generic InjF
-- machinery instead of needing bespoke Expr constructors.

-- Applicability guard shared by the Cons inverses: head/tail are undefined on
-- the empty list, so the inversion (and hence the whole Cons inference) is only
-- valid on a non-empty list. Mirrors the empty-list guard the old bespoke Cons
-- inference applied by hand.
listNonEmpty :: IRExpr
listNonEmpty = IRUnaryOp OpNot (IROp OpEq (IRVar "b") (IRConst (VList EmptyList)))

consFwd :: FDecl
consFwd = FDecl (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a"))))) ["h", "t"] ["b"] (IRConstruct TgCons [IRVar "h", IRVar "t"]) (IRConst (VBool True)) False [("h", IRConst (VFloat 1)), ("t", IRConst (VFloat 1))]
consInvHead :: FDecl
consInvHead = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` TVarR (TV "a"))) ["b"] ["h"] (IRDestruct AcHead (IRVar "b")) listNonEmpty True [("b", IRConst (VFloat 1))]
consInvTail :: FDecl
consInvTail = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a")))) ["b"] ["t"] (IRDestruct AcTail (IRVar "b")) listNonEmpty True [("b", IRConst (VFloat 1))]

tConsFwd :: FDecl
tConsFwd = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "a") `TArrow` (TVarR (TV "b") `TArrow` Tuple (TVarR (TV "a")) (TVarR (TV "b"))))) ["x", "y"] ["b"] (IRConstruct TgTuple [IRVar "x", IRVar "y"]) (IRConst (VBool True)) False [("x", IRConst (VFloat 1)), ("y", IRConst (VFloat 1))]
tConsInvFst :: FDecl
tConsInvFst = FDecl (Forall [TV "a", TV "b"] [] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "a"))) ["b"] ["x"] (IRDestruct AcFst (IRVar "b")) (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]
tConsInvSnd :: FDecl
tConsInvSnd = FDecl (Forall [TV "a", TV "b"] [] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "b"))) ["b"] ["y"] (IRDestruct AcSnd (IRVar "b")) (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]

fstFwd :: FDecl
fstFwd = FDecl (Forall [TV "a", TV "b"] [] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "a"))) ["a"] ["b"] (IRDestruct AcFst (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
fstInv :: FDecl
fstInv = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "a") `TArrow` Tuple (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRConstruct TgTuple [IRVar "b", IRConst VAny]) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]
sndFwd :: FDecl
sndFwd = FDecl (Forall [TV "a", TV "b"] [] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "b"))) ["a"] ["b"] (IRDestruct AcSnd (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
sndInv :: FDecl
sndInv = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "b") `TArrow` Tuple (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRConstruct TgTuple [IRConst VAny, IRVar "b"]) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

headFwd :: FDecl
headFwd = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` TVarR (TV "a"))) ["a"] ["b"] (IRDestruct AcHead (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
headInv :: FDecl
-- The reconstructed tail is a list slot, so its hole must be the list-shaped
-- any-value; a scalar one is ill-typed on both text backends. See 'anyOfType'.
headInv = FDecl (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` ListOf (TVarR (TV "a")))) ["b"] ["a"] (IRConstruct TgCons [IRVar "b", IRConst (anyOfType (ListOf (TVarR (TV "a"))))]) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

tailFwd :: FDecl
tailFwd = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a")))) ["a"] ["b"] (IRDestruct AcTail (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
tailInv :: FDecl
tailInv = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a")))) ["b"] ["a"] (IRConstruct TgCons [IRConst VAny, IRVar "b"]) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

isNullFwd :: FDecl
isNullFwd = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` TBool)) ["a"] ["b"] (IROp OpEq (IRVar "a") (IRConst (VList EmptyList))) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
-- Inverse of isNull is either an empty list if true or a list with at least one element
isNullInv :: FDecl 
isNullInv = FDecl (Forall [TV "a"] [] (TBool `TArrow` ListOf (TVarR (TV "a")))) ["b"] ["a"] (IRIf (IRVar "b") (IRConst $ VList EmptyList ) (IRConst $ VList (ListCont VAny AnyList))) (IRConst (VBool True)) True [("b", IRConst (VFloat 1))] 

-- ============================ Higher Order Functions ============================

-- Apply is only a test function for higher order injF
applyFwd :: FDecl
applyFwd = FDecl (Forall [TV "a", TV "b"] [] ((TVarR (TV "a") `TArrow` TVarR (TV "b")) `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "b")))) ["f", "a"] ["b"] (IRApply (IRVar "f") (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
applyInv :: FDecl
applyInv = FDecl (Forall [TV "b", TV "a"] [] ((TVarR (TV "a") `TArrow` TVarR (TV "b")) `TArrow` (TVarR (TV "b") `TArrow` TVarR (TV "a")))) ["f", "b"] ["a"] (IRApply (IRVar "f^-1") (IRVar "b")) (IRConst (VBool True)) True [("b", IRApply (IRVar "f^-1'") (IRVar "b"))]

mapFwd :: FDecl
mapFwd = FDecl (Forall [TV "a", TV "b"] [] ((TVarR (TV "a") `TArrow` TVarR (TV "b")) `TArrow` (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "b"))))) ["f", "a"] ["b"] (IRBuiltin BMapList [IRVar "f", IRVar "a"]) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
--FIXME: The derivative here is probably wron in general, if the list represents a degenerate distribution. This should probably be something like the determinant of the jacobian
mapInv :: FDecl
mapInv = FDecl (Forall [TV "a", TV "b"] [] ((TVarR (TV "b") `TArrow` TVarR (TV "a")) `TArrow` (ListOf (TVarR (TV "b")) `TArrow` ListOf (TVarR (TV "a"))))) ["f", "b"] ["a"] (IRBuiltin BMapList [IRVar "f^-1", IRVar "b"]) (IRConst (VBool True)) True [("b", invokeStandardFunction stdListProd [IRBuiltin BMapList [IRVar "f^-1'", IRVar "b"]])]

mapLeftFwd :: FDecl
mapLeftFwd = FDecl (Forall [TV "a", TV "b", TV "c"] [] ((TVarR (TV "a") `TArrow` TVarR (TV "c")) `TArrow` (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TEither (TVarR (TV "c")) (TVarR (TV "b"))))) ["f", "a"] ["b"]
              (IRIf (IRDestruct AcIsLeft (IRVar "a")) (IRConstruct TgLeft [IRApply (IRVar "f") (IRDestruct AcFromLeft (IRVar "a"))]) (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
mapLeftInv :: FDecl
mapLeftInv = FDecl (Forall [TV "a", TV "b", TV "c"] [] ((TVarR (TV "c") `TArrow` TVarR (TV "a")) `TArrow` (TEither (TVarR (TV "c")) (TVarR (TV "b")) `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b"))))) ["f", "b"] ["a"]
              (IRIf (IRDestruct AcIsLeft (IRVar "b")) (IRConstruct TgLeft [IRApply (IRVar "f^-1") (IRDestruct AcFromLeft (IRVar "b"))]) (IRVar "b")) (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]

mapEitherFwd :: FDecl
mapEitherFwd = FDecl (Forall [TV "a", TV "b", TV "c", TV "d"] [] ((TVarR (TV "a") `TArrow` TVarR (TV "c")) `TArrow` ((TVarR (TV "b") `TArrow` TVarR (TV "d")) `TArrow` (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TEither (TVarR (TV "c")) (TVarR (TV "d")))))) ["f", "g", "a"] ["b"]
              (IRIf (IRDestruct AcIsLeft (IRVar "a")) (IRConstruct TgLeft [IRApply (IRVar "f") (IRDestruct AcFromLeft (IRVar "a"))]) (IRConstruct TgRight [IRApply (IRVar "g") (IRDestruct AcFromRight (IRVar "a"))])) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
mapEitherInv :: FDecl
mapEitherInv = FDecl (Forall [TV "a", TV "b", TV "c", TV "d"] [] ((TVarR (TV "c") `TArrow` TVarR (TV "a")) `TArrow` ((TVarR (TV "d") `TArrow` TVarR (TV "b")) `TArrow` (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TEither (TVarR (TV "c")) (TVarR (TV "d")))))) ["f", "g", "b"] ["a"]
              (IRIf (IRDestruct AcIsLeft (IRVar "b")) (IRConstruct TgLeft [IRApply (IRVar "f^-1") (IRDestruct AcFromLeft (IRVar "b"))]) (IRConstruct TgRight [IRApply (IRVar "g^-1") (IRDestruct AcFromRight (IRVar "b"))])) (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]



globalFenv' :: FEnv
globalFenv' = [("double", FPair doubleFwd [doubleInv]),
              ("exp", FPair expFwd [expInv]),
              ("log", FPair expInv [expFwd]),
              ("neg", FPair negFwd [negInv]),
              ("negI", FPair negIFwd [negIInv]),
              ("recip", FPair recipFwd [recipInv]),
              ("sqrt", FPair sqrtFwd [sqrtInv]),
              ("sq", FPair sqFwd [sqInv]),
              ("left", FPair leftFwd [fromLeftFwd]),
              ("right", FPair rightFwd [fromRightFwd]),
              ("fromLeft", FPair fromLeftMaybeFwd [fromLeftMaybeInv]),
              ("fromRight", FPair fromRightMaybeFwd [fromRightMaybeInv]),
              -- Partial extractors backing the `let left a = ...`/`let right b = ...`
              -- letIn-destructuring sugar only -- see sfromLeftPartial/sfromRightPartial.
              ("fromLeftPartial", FPair fromLeftFwd [leftFwd]),
              ("fromRightPartial", FPair fromRightFwd [rightFwd]),
              ("isLeft", FPair isLeftFwd [isLeftInv]),
              ("isRight", FPair isRightFwd [isRightInv]),
              ("plus", FPair plusFwd [plusInv1, plusInv2]),
              ("plusI", FPair plusIFwd [plusIInv1, plusIInv2]),
              ("mult", FPair multFwd [multInv1, multInv2]),
              ("multI", FPair multIFwd [multIInv1, multIInv2]),
              ("not", FPair notFwd [notInv]),
              ("and", FPair andFwd []),
              ("or", FPair orFwd []),
              ("gt", FPair gtFwd []),
              ("lt", FPair ltFwd []),
              ("max", FPair maxFwd []),
              ("eq", FPair eqFwd [eqInv1, eqInv2]),
              ("Cons", FPair consFwd [consInvHead, consInvTail]),
              ("TCons", FPair tConsFwd [tConsInvFst, tConsInvSnd]),
              ("fst", FPair fstFwd [fstInv]),
              ("snd", FPair sndFwd [sndInv]),
              ("head", FPair headFwd [headInv]),
              ("tail", FPair tailFwd [tailInv]),
              ("apply", FPair applyFwd [applyInv]),
              ("map", FPair mapFwd [mapInv]),
              ("mapLeft", FPair mapLeftFwd [mapLeftInv]),
              ("mapEither", FPair mapEitherFwd [mapEitherInv]),
              ("isNull", FPair isNullFwd [isNullInv])]

globalFEnv :: [ADTDecl] -> FEnv
globalFEnv adtsDecl = globalFenv' ++ concatMap fPairsFromADT adtsDecl

-- Creates a instance of a FPair, that has identifier names given by a monadic function. m should be a supply monad
-- Works by having each identifier renamed using this function
instantiate :: (Monad m) => (String -> m String) -> [ADTDecl] -> String -> m FPair
instantiate gen adtsDecl n = do
  let (FPair fwd inv) = case lookup n (globalFEnv adtsDecl) of
                             Just f -> f
                             Nothing -> error ("InjF " ++ n ++ " not found!")
  let FDecl {inputVars=v1, outputVars=v2} = fwd
  let allVarNames = v1 ++ v2  -- All indentifier names in the InjF
  newVarNames <- mapM gen allVarNames -- These are the new names given by the gen function
  let instantiateDecl d = foldr (\(old, new) decl -> renameDecl old new decl) d (zip allVarNames newVarNames) -- Rename all identifiers with the new names
  return (FPair (instantiateDecl fwd) (map instantiateDecl inv))

rename :: String -> String -> IRExpr -> IRExpr
rename old new (IRVar n) | n == old = IRVar new
rename old new (IRVar n) | n == old ++ "^-1" = IRVar (new ++ "^-1")
rename old new (IRVar n) | n == old ++ "^-1'" = IRVar (new ++ "^-1'")
rename old new (IRConst (VAnyExcept e)) = IRConst (VAnyExcept (map (rename old new) e))
rename _ _ expr = expr

renameAll :: String -> String -> IRExpr -> IRExpr
renameAll old new = irMap (rename old new)

renameDecl :: String -> String -> FDecl -> FDecl
renameDecl old new FDecl {contract=sig, inputVars=inVars, outputVars=outVars, body=expr, applicability=app, deconstructing=decons, derivatives=derivs} =
  FDecl {contract=sig, inputVars=map renS inVars, outputVars=map renS outVars, body=ren expr, applicability=ren app, deconstructing=decons, derivatives=map (Data.Bifunctor.bimap renS ren) derivs}
  where
    ren = renameAll old new-- A function that renames old to new
    renS s = if s == old then new else s  -- A function that replaces old string with new strings


-- | True if a named InjF is a multi-field "field constructor": every input is
-- independently recoverable from the single output via a deconstructing inverse
-- (Cons, TCons, and user-ADT constructors with >= 2 fields). These need product
-- inference (each field inferred against its recovered sub-sample, results
-- multiplied) rather than the additive PlusConstraint semantics of ordinary
-- multi-argument InjFs. Single-field constructors are excluded; they are already
-- handled correctly by the single-probabilistic-parameter InjF path.
isFieldConstructor :: [ADTDecl] -> String -> Bool
isFieldConstructor adtsDecl name =
  case lookup name (globalFEnv adtsDecl) of
    Just (FPair FDecl{inputVars=ins, outputVars=[_]} invs) ->
         length ins >= 2
      && length invs == length ins
      && all (\FDecl{inputVars=iv, deconstructing=d} -> length iv == 1 && d) invs
    _ -> False

isHigherOrder :: [ADTDecl] -> String -> Bool
isHigherOrder adtsDecl name =
  case lookup name (globalFEnv adtsDecl) of
    Nothing -> False
    Just (FPair FDecl {contract=Forall _ _ c} _) -> hasArrowParameter c
  where
    hasArrowParameter rt =
      case rt of
        TArrow (TArrow _ _) _ -> True
        TArrow _ a -> hasArrowParameter a
        _ -> False

getFunctionParamIdx :: [ADTDecl] -> String -> [Int]
getFunctionParamIdx adtsDecl name =
  case lookup name (globalFEnv adtsDecl) of
    Nothing -> []
    Just (FPair FDecl {contract=Forall _ _ c} _) -> findArrowParameter c
  where
    findArrowParameter rt =
      case rt of
        TArrow (TArrow _ _) a -> 0: map (+1) (findArrowParameter a)
        TArrow _ a -> map (+1) (findArrowParameter a)
        _ -> []

propagateValues :: [ADTDecl] -> String -> [[Value]] -> [Value]
propagateValues adtsDecl name values = case results of
  Left _ -> []
  Right l -> map (fmap failConversionRev) l
  where
    results = mapM (generateDet [] [] (IREnv [] adtsDecl []) []) letInBlocks
    letInBlocks = map (foldr (\(n, p) e -> IRLetIn n (IRConst (fmap failConversionFwd p)) e) fwdExpr) namedParams
    namedParams = map (zip paramNames) applicableProd
    -- An ADT field accessor / constructor test is partial: it is undefined on a
    -- value of a sibling constructor, and 'implicitFunctionImpl' says so with an
    -- 'error', not a 'Left' this could catch. Enumerating a multi-constructor
    -- domain therefore has to drop those tuples before evaluating, leaving the
    -- accessor's domain as its own constructor's values.
    applicableProd = filter (implicitFunctionApplicable adtsDecl name) valueProd
    valueProd = sequence values
    FPair FDecl {inputVars = paramNames, body = fwdExpr} _ = lookupFPair adtsDecl name

parameterCount :: [ADTDecl] -> String -> Int
parameterCount adtsDecl name = do
  case lookup name (globalFEnv adtsDecl) of
    Just (FPair FDecl {inputVars=params} _) -> length params
    _ -> error $ "Unknown InjF: " ++ name

hasAnyExcept :: [ADTDecl] -> String -> Bool
hasAnyExcept adtsDecl name =
  case lookup name (globalFEnv adtsDecl) of
    Just (FPair _ invs) -> any (hasAnyExceptExpr . body) invs
    _ -> error $ "Unknown InjF: " ++ name


hasAnyExceptExpr :: IRExpr -> Bool
hasAnyExceptExpr (IRConst (VAnyExcept _)) = True 
hasAnyExceptExpr e = any hasAnyExceptExpr (getIRSubExprs e)

failConversionFwd :: Expr -> IRExpr
failConversionFwd = error "Error during value conversion. This should not happen"

failConversionRev :: IRExpr -> Expr
failConversionRev = error "Error during value conversion. This should not happen"

fPairsFromADT :: ADTDecl -> [(String, FPair)]
fPairsFromADT ADTDecl{dataName=name, constructors=constrs} = concatMap (fPairsFromADTConstructor name) constrs

fPairsFromADTConstructor :: String -> ADTConstructorDecl  -> [(String, FPair)]
fPairsFromADTConstructor adtName constr@(constrName, fields) = constrFPair:isFunctionFPair:fieldFPairs
  where
    constrFPair = (constrName, FPair fwdConstr (map invConstr fieldNames))
    isFunctionFPair = fPaisOfADTIsFunction adtName constr
    fieldFPairs = map (fPairFromADTField adtRT constr) fields
    adtRT = TADT adtName
    fieldNames = map fst fields
    -- Rename fields so that they don' clash with the accessor functions
    fieldNames' = map ("f_" ++) fieldNames
    fieldRTs = map snd fields
    constrRT = foldr TArrow (TADT adtName) fieldRTs
    applicationExpr = foldl (\e n -> IRApply e (IRVar n)) (IRVar constrName) fieldNames'
    derivs = map (\n -> (n, IRConst $ VFloat 1)) fieldNames'
    fwdConstr = FDecl (Forall [] [] constrRT) fieldNames' ["b"] applicationExpr (IRConst $ VBool True) False derivs
    rtOfField f = fromJust $ lookup f fields
    -- The inverse deconstructs the sample with a field accessor, which is only
    -- defined when the sample actually carries this constructor. Without the
    -- guard, inference for a multi-constructor ADT evaluates every
    -- constructor's contribution unconditionally and the accessor throws on a
    -- sample built by a sibling constructor. Any-tolerant, since a marginal
    -- wildcard stands for a value of every constructor.
    invConstr f = FDecl (Forall [] [] (adtRT `TArrow` rtOfField f)) ["b"] ["f_" ++ f] (IRApply (IRVar f) (IRVar "b")) (isConstrGuard constrName (IRVar "b")) True [("b", IRConst $ VFloat 1)]

fPaisOfADTIsFunction :: String -> ADTConstructorDecl -> (String, FPair)
fPaisOfADTIsFunction adtName (constrName, rTypes) = (isFName, fPair)
  where
    isFName = "is" ++ constrName 
    fPair = FPair fwdIs [invIs]
    fwdIs = FDecl (Forall [] [] (TADT adtName `TArrow` TBool)) ["a"] ["b"] (IRApply (IRVar isFName) (IRVar "a")) (IRConst $ VBool True) False [("a", IRConst $ VFloat 1)]
    constrWithAnys = foldl (\e (_, fieldRT) -> IRApply e (IRConst (anyOfType fieldRT))) (IRVar constrName) rTypes  -- One position-correct Any for each parameter
    invIs = FDecl (Forall [] [] (TBool `TArrow` TADT adtName)) ["b"] ["a"] (IRIf (IRVar "b") constrWithAnys (IRConst $ VAnyExcept [constrWithAnys])) (IRConst $ VBool True) False [("b", IRConst $ VFloat 1)]

fPairFromADTField :: RType -> ADTConstructorDecl -> (String, RType) -> (String, FPair)
fPairFromADTField adtRT constr@(ownerName, _) (fieldName, fieldRT) = (fieldName, FPair fwd [inv])
  where
    -- Reading a field is only applicable to a sample carrying the constructor
    -- that declares it; see 'invConstr'.
    fwd = FDecl (Forall [] [] (adtRT `TArrow` fieldRT)) ["a"] ["b"] (IRApply (IRVar fieldName) (IRVar "a")) (isConstrGuard ownerName (IRVar "a")) True [("a", IRConst $ VFloat 1)]
    inv = FDecl (Forall [] [] (fieldRT `TArrow` adtRT)) ["b"] ["a"] (allAnyFieldsExcept constr fieldName (IRVar "b")) (IRConst $ VBool True) False [("b", IRConst $ VFloat 1)]

-- | Runtime test that @v@ carries constructor @cName@, used as the
-- applicability guard of every inverse that deconstructs an ADT sample. A
-- marginal wildcard passes: @ANY@ stands for a value of any constructor, and
-- the enclosing inference handles it through its own Any-safe path.
isConstrGuard :: String -> IRExpr -> IRExpr
isConstrGuard cName v =
  IRIf (IRUnaryOp OpIsAny v) (IRConst $ VBool True) (IRApply (IRVar ("is" ++ cName)) v)

allAnyFieldsExcept :: ADTConstructorDecl -> String -> IRExpr -> IRExpr
allAnyFieldsExcept (constrName, fields) toFill fillExpr = foldl IRApply (IRVar constrName) fieldValues
  where
    fieldValues = map (\(fieldName, fieldRT) -> if fieldName == toFill then fillExpr else IRConst (anyOfType fieldRT)) fields