module PredefinedFunctions (
globalFEnv,
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
import SPLL.IntermediateRepresentation (IRExpr, IRExpr(..), Operand(..), UnaryOperand(..), irMap, IREnv (IREnv), getIRSubExprs) --FIXME
import SPLL.Lang.Lang
import Data.Maybe (fromJust)
import SPLL.Lang.Types
import IRInterpreter
import qualified Data.Bifunctor
import StandardLibrary (invokeStandardFunction, stdListProd)

-- InputVars, OutputVars, fwd, grad
data FDecl = FDecl {contract :: Scheme, inputVars :: [String], outputVars :: [String], body :: IRExpr, applicability :: IRExpr, deconstructing :: Bool, derivatives :: [(String, IRExpr)]} deriving (Show, Eq)
-- Forward, inverse
data FPair = FPair {forwardDecl :: FDecl, inverseDecl :: [FDecl]} deriving (Show, Eq)
type FEnv = [(String, FPair)]

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
recipInv = FDecl (Forall [] [] (TArrow TFloat TFloat)) ["b"] ["a"] (IROp OpDiv (IRConst (VFloat 1)) (IRVar "b")) (IRConst (VBool True)) False [("b", IRUnaryOp OpNeg (IROp OpDiv (IRConst (VFloat 1)) (IROp OpMult (IRVar "b") (IRVar "b"))))]

leftFwd :: FDecl
leftFwd = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "a") `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["a"] ["b"] (IRLeft (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
fromLeftFwd :: FDecl
fromLeftFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "a"))) ["b"] ["a"] (IRFromLeft (IRVar "b")) (IRIsLeft (IRVar "b")) True [("b", IRConst (VFloat 1))]

rightFwd :: FDecl
rightFwd = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "b") `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["a"] ["b"] (IRRight (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
fromRightFwd :: FDecl
fromRightFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "b"))) ["b"] ["a"] (IRFromRight (IRVar "b")) (IRIsRight (IRVar "b")) True [("b", IRConst (VFloat 1))]

isLeftFwd :: FDecl
isLeftFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TBool)) ["a"] ["b"] (IRIsLeft (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
isLeftInv :: FDecl
isLeftInv = FDecl (Forall [TV "a", TV "b"] [] (TBool `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRIf (IRVar "b") (IRConst $ VEither (Left VAny)) (IRConst $ VEither (Right VAny))) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

isRightFwd :: FDecl
isRightFwd = FDecl (Forall [TV "a", TV "b"] [] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TBool)) ["a"] ["b"] (IRIsRight (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
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
consFwd = FDecl (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a"))))) ["h", "t"] ["b"] (IRCons (IRVar "h") (IRVar "t")) (IRConst (VBool True)) False [("h", IRConst (VFloat 1)), ("t", IRConst (VFloat 1))]
consInvHead :: FDecl
consInvHead = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` TVarR (TV "a"))) ["b"] ["h"] (IRHead (IRVar "b")) listNonEmpty True [("b", IRConst (VFloat 1))]
consInvTail :: FDecl
consInvTail = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a")))) ["b"] ["t"] (IRTail (IRVar "b")) listNonEmpty True [("b", IRConst (VFloat 1))]

tConsFwd :: FDecl
tConsFwd = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "a") `TArrow` (TVarR (TV "b") `TArrow` Tuple (TVarR (TV "a")) (TVarR (TV "b"))))) ["x", "y"] ["b"] (IRTCons (IRVar "x") (IRVar "y")) (IRConst (VBool True)) False [("x", IRConst (VFloat 1)), ("y", IRConst (VFloat 1))]
tConsInvFst :: FDecl
tConsInvFst = FDecl (Forall [TV "a", TV "b"] [] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "a"))) ["b"] ["x"] (IRTFst (IRVar "b")) (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]
tConsInvSnd :: FDecl
tConsInvSnd = FDecl (Forall [TV "a", TV "b"] [] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "b"))) ["b"] ["y"] (IRTSnd (IRVar "b")) (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]

fstFwd :: FDecl
fstFwd = FDecl (Forall [TV "a", TV "b"] [] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "a"))) ["a"] ["b"] (IRTFst (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
fstInv :: FDecl
fstInv = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "a") `TArrow` Tuple (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRTCons (IRVar "b") (IRConst VAny)) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]
sndFwd :: FDecl
sndFwd = FDecl (Forall [TV "a", TV "b"] [] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "b"))) ["a"] ["b"] (IRTSnd (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
sndInv :: FDecl
sndInv = FDecl (Forall [TV "a", TV "b"] [] (TVarR (TV "b") `TArrow` Tuple (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRTCons (IRConst VAny) (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

headFwd :: FDecl
headFwd = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` TVarR (TV "a"))) ["a"] ["b"] (IRHead (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
headInv :: FDecl
headInv = FDecl (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` ListOf (TVarR (TV "a")))) ["b"] ["a"] (IRCons (IRVar "b") (IRConst VAny)) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

tailFwd :: FDecl
tailFwd = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a")))) ["a"] ["b"] (IRTail (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
tailInv :: FDecl
tailInv = FDecl (Forall [TV "a"] [] (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a")))) ["b"] ["a"] (IRCons (IRConst VAny) (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

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
mapFwd = FDecl (Forall [TV "a", TV "b"] [] ((TVarR (TV "a") `TArrow` TVarR (TV "b")) `TArrow` (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "b"))))) ["f", "a"] ["b"] (IRMap (IRVar "f") (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
--FIXME: The derivative here is probably wron in general, if the list represents a degenerate distribution. This should probably be something like the determinant of the jacobian
mapInv :: FDecl
mapInv = FDecl (Forall [TV "a", TV "b"] [] ((TVarR (TV "b") `TArrow` TVarR (TV "a")) `TArrow` (ListOf (TVarR (TV "b")) `TArrow` ListOf (TVarR (TV "a"))))) ["f", "b"] ["a"] (IRMap (IRVar "f^-1") (IRVar "b")) (IRConst (VBool True)) True [("b", invokeStandardFunction stdListProd [IRMap (IRVar "f^-1'") (IRVar "b")])]

mapLeftFwd :: FDecl
mapLeftFwd = FDecl (Forall [TV "a", TV "b", TV "c"] [] ((TVarR (TV "a") `TArrow` TVarR (TV "c")) `TArrow` (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TEither (TVarR (TV "c")) (TVarR (TV "b"))))) ["f", "a"] ["b"]
              (IRIf (IRIsLeft (IRVar "a")) (IRLeft (IRApply (IRVar "f") (IRFromLeft (IRVar "a")))) (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
mapLeftInv :: FDecl
mapLeftInv = FDecl (Forall [TV "a", TV "b", TV "c"] [] ((TVarR (TV "c") `TArrow` TVarR (TV "a")) `TArrow` (TEither (TVarR (TV "c")) (TVarR (TV "b")) `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b"))))) ["f", "b"] ["a"]
              (IRIf (IRIsLeft (IRVar "b")) (IRLeft (IRApply (IRVar "f^-1") (IRFromLeft (IRVar "b")))) (IRVar "b")) (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]

mapEitherFwd :: FDecl
mapEitherFwd = FDecl (Forall [TV "a", TV "b", TV "c", TV "d"] [] ((TVarR (TV "a") `TArrow` TVarR (TV "c")) `TArrow` ((TVarR (TV "b") `TArrow` TVarR (TV "d")) `TArrow` (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TEither (TVarR (TV "c")) (TVarR (TV "d")))))) ["f", "g", "a"] ["b"]
              (IRIf (IRIsLeft (IRVar "a")) (IRLeft (IRApply (IRVar "f") (IRFromLeft (IRVar "a")))) (IRRight (IRApply (IRVar "g") (IRFromRight (IRVar "a"))))) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
mapEitherInv :: FDecl
mapEitherInv = FDecl (Forall [TV "a", TV "b", TV "c", TV "d"] [] ((TVarR (TV "c") `TArrow` TVarR (TV "a")) `TArrow` ((TVarR (TV "d") `TArrow` TVarR (TV "b")) `TArrow` (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TEither (TVarR (TV "c")) (TVarR (TV "d")))))) ["f", "g", "b"] ["a"]
              (IRIf (IRIsLeft (IRVar "b")) (IRLeft (IRApply (IRVar "f^-1") (IRFromLeft (IRVar "b")))) (IRRight (IRApply (IRVar "g^-1") (IRFromRight (IRVar "b"))))) (IRConst (VBool True)) True [("b", IRConst (VFloat 1))]



globalFenv' :: FEnv
globalFenv' = [("double", FPair doubleFwd [doubleInv]),
              ("exp", FPair expFwd [expInv]),
              ("log", FPair expInv [expFwd]),
              ("neg", FPair negFwd [negInv]),
              ("negI", FPair negIFwd [negIInv]),
              ("recip", FPair recipFwd [recipInv]),
              ("left", FPair leftFwd [fromLeftFwd]),
              ("right", FPair rightFwd [fromRightFwd]),
              ("fromLeft", FPair fromLeftFwd [leftFwd]),
              ("fromRight", FPair fromRightFwd [rightFwd]),
              ("isLeft", FPair isLeftFwd [isLeftInv]),
              ("isRight", FPair isRightFwd [isRightInv]),
              ("plus", FPair plusFwd [plusInv1, plusInv2]),
              ("plusI", FPair plusIFwd [plusIInv1, plusIInv2]),
              ("mult", FPair multFwd [multInv1, multInv2]),
              ("multI", FPair multIFwd [multIInv1, multIInv2]),
              ("not", FPair notFwd [notInv]),
              ("and", FPair andFwd []),
              ("or", FPair orFwd []),
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
globalFEnv adts = globalFenv' ++ concatMap fPairsFromADT adts

-- Creates a instance of a FPair, that has identifier names given by a monadic function. m should be a supply monad
-- Works by having each identifier renamed using this function
instantiate :: (Monad m) => (String -> m String) -> [ADTDecl] -> String -> m FPair
instantiate gen adts n = do
  let (FPair fwd inv) = case lookup n (globalFEnv adts) of
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
isFieldConstructor adts name =
  case lookup name (globalFEnv adts) of
    Just (FPair FDecl{inputVars=ins, outputVars=[_]} invs) ->
         length ins >= 2
      && length invs == length ins
      && all (\FDecl{inputVars=iv, deconstructing=d} -> length iv == 1 && d) invs
    _ -> False

isHigherOrder :: [ADTDecl] -> String -> Bool
isHigherOrder adts name =
  case lookup name (globalFEnv adts) of
    Nothing -> False
    Just (FPair FDecl {contract=Forall _ _ c} _) -> hasArrowParameter c
  where
    hasArrowParameter rt =
      case rt of
        TArrow (TArrow _ _) _ -> True
        TArrow _ a -> hasArrowParameter a
        _ -> False

getFunctionParamIdx :: [ADTDecl] -> String -> [Int]
getFunctionParamIdx adts name =
  case lookup name (globalFEnv adts) of
    Nothing -> []
    Just (FPair FDecl {contract=Forall _ _ c} _) -> findArrowParameter c
  where
    findArrowParameter rt =
      case rt of
        TArrow (TArrow _ _) a -> 0: map (+1) (findArrowParameter a)
        TArrow _ a -> map (+1) (findArrowParameter a)
        _ -> []

propagateValues :: [ADTDecl] -> String -> [[Value]] -> [Value]
propagateValues adts name values = case results of
  Left _ -> []
  Right l -> map (fmap failConversionRev) l
  where
    results = mapM (generateDet [] (IREnv [] adts []) []) letInBlocks
    letInBlocks = map (foldr (\(n, p) e -> IRLetIn n (IRConst (fmap failConversionFwd p)) e) fwdExpr) namedParams
    namedParams = map (zip paramNames) valueProd
    valueProd = sequence values
    Just (FPair FDecl {inputVars = paramNames, body = fwdExpr} _) = lookup name (globalFEnv adts)

parameterCount :: [ADTDecl] -> String -> Int
parameterCount adts name = do
  case lookup name (globalFEnv adts) of
    Just (FPair FDecl {inputVars=params} _) -> length params
    _ -> error $ "Unknown InjF: " ++ name

hasAnyExcept :: [ADTDecl] -> String -> Bool
hasAnyExcept adts name = 
  case lookup name (globalFEnv adts) of
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
    -- FIXME Probably chekc whether parameter is indeed of this constructor in applicability test
    invConstr f = FDecl (Forall [] [] (adtRT `TArrow` rtOfField f)) ["b"] ["f_" ++ f] (IRApply (IRVar f) (IRVar "b")) (IRConst $ VBool True) True [("b", IRConst $ VFloat 1)]

fPaisOfADTIsFunction :: String -> ADTConstructorDecl -> (String, FPair)
fPaisOfADTIsFunction adtName (constrName, rTypes) = (isFName, fPair)
  where
    isFName = "is" ++ constrName 
    fPair = FPair fwdIs [invIs]
    fwdIs = FDecl (Forall [] [] (TADT adtName `TArrow` TBool)) ["a"] ["b"] (IRApply (IRVar isFName) (IRVar "a")) (IRConst $ VBool True) False [("a", IRConst $ VFloat 1)]
    constrWithAnys = foldl (\e _ -> IRApply e (IRConst VAny)) (IRVar constrName) rTypes  -- One Any for each parameter
    invIs = FDecl (Forall [] [] (TBool `TArrow` TADT adtName)) ["b"] ["a"] (IRIf (IRVar "b") constrWithAnys (IRConst $ VAnyExcept [constrWithAnys])) (IRConst $ VBool True) False [("b", IRConst $ VFloat 1)]

fPairFromADTField :: RType -> ADTConstructorDecl -> (String, RType) -> (String, FPair)
fPairFromADTField adtRT constr (fieldName, fieldRT) = (fieldName, FPair fwd [inv])
  where
    -- FIXME Probably chekc whether parameter is indeed of this constructor in applicability test
    fwd = FDecl (Forall [] [] (adtRT `TArrow` fieldRT)) ["a"] ["b"] (IRApply (IRVar fieldName) (IRVar "a")) (IRConst $ VBool True) True [("a", IRConst $ VFloat 1)]
    inv = FDecl (Forall [] [] (fieldRT `TArrow` adtRT)) ["b"] ["a"] (allAnyFieldsExcept constr fieldName (IRVar "b")) (IRConst $ VBool True) False [("b", IRConst $ VFloat 1)]

allAnyFieldsExcept :: ADTConstructorDecl -> String -> IRExpr -> IRExpr
allAnyFieldsExcept (constrName, fields) toFill fillExpr = foldl IRApply (IRVar constrName) fieldValues
  where
    fieldValues = map (\(fieldName, _) -> if fieldName == toFill then fillExpr else IRConst VAny) fields