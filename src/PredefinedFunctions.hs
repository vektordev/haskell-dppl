module PredefinedFunctions (
globalFenv,
getHornClause,
FPair(..),
FDecl(..),
FEnv,
instantiate,
propagateValues,
parameterCount
) where

import SPLL.Typing.RType (RType(..), Scheme(..), TVarR(..))
import SPLL.IntermediateRepresentation (IRExpr, IRExpr(..), Operand(..), UnaryOperand(..), irMap) --FIXME
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import Data.Set (fromList)
import Data.Maybe (fromJust)
import SPLL.Lang.Types
import IRInterpreter
import Control.Monad
import Control.Monad.Supply (MonadSupply)
import qualified Data.Bifunctor

-- InputVars, OutputVars, fwd, grad
data FDecl = FDecl {contract :: Scheme, inputVars :: [String], outputVars :: [String], body :: IRExpr, applicability :: IRExpr, deconstructing :: Bool, derivatives :: [(String, IRExpr)]} deriving (Show, Eq)
-- Forward, inverse
data FPair = FPair {forwardDecl :: FDecl, inverseDecl :: [FDecl]} deriving (Show, Eq)
type FEnv = [(String, FPair)]

-- ============================ UNARY ARITHMETIC ============================

doubleFwd :: FDecl
doubleFwd = FDecl (Forall [] (TArrow TFloat TFloat)) ["a"] ["b"] (IROp OpMult (IRVar "a") (IRConst $ VFloat 2)) (IRConst (VBool True)) False [("a", IRConst $ VFloat 2)]
doubleInv :: FDecl
doubleInv = FDecl (Forall [] (TArrow TFloat TFloat)) ["b"] ["a"] (IROp OpDiv (IRVar "b") (IRConst $ VFloat 2)) (IRConst (VBool True)) False [("b", IRConst $ VFloat 0.5)]

expFwd :: FDecl
expFwd = FDecl (Forall [] (TArrow TFloat TFloat)) ["a"] ["b"] (IRUnaryOp OpExp (IRVar "a")) (IRConst (VBool True)) False [("a", IRUnaryOp OpExp (IRVar "a"))]
expInv :: FDecl
expInv = FDecl (Forall [] (TArrow TFloat TFloat)) ["b"] ["a"] (IRUnaryOp OpLog (IRVar "b")) (IROp OpGreaterThan (IRVar "b") (IRConst $ VFloat 0)) False [("b", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))]

negFwd :: FDecl
negFwd = FDecl (Forall [] (TArrow TFloat TFloat)) ["a"] ["b"] (IRUnaryOp OpNeg (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat (-1)))]
negInv :: FDecl
negInv = FDecl (Forall [] (TArrow TFloat TFloat)) ["b"] ["a"] (IRUnaryOp OpNeg (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat (-1)))]

leftFwd :: FDecl
leftFwd = FDecl (Forall [TV "a", TV "b"] (TVarR (TV "a") `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["a"] ["b"] (IRLeft (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
fromLeftFwd :: FDecl
fromLeftFwd = FDecl (Forall [TV "a", TV "b"] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "a"))) ["b"] ["a"] (IRFromLeft (IRVar "b")) (IRIsLeft (IRVar "b")) True [("a", IRConst (VFloat 1))]

rightFwd :: FDecl
rightFwd = FDecl (Forall [TV "a", TV "b"] (TVarR (TV "b") `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["a"] ["b"] (IRRight (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
fromRightFwd :: FDecl
fromRightFwd = FDecl (Forall [TV "a", TV "b"] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "b"))) ["b"] ["a"] (IRFromRight (IRVar "b")) (IRIsRight (IRVar "b")) True [("a", IRConst (VFloat 1))]

isLeftFwd :: FDecl
isLeftFwd = FDecl (Forall [TV "a", TV "b"] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TBool)) ["a"] ["b"] (IRIsLeft (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
isLeftInv :: FDecl
isLeftInv = FDecl (Forall [TV "a", TV "b"] (TBool `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRIf (IRVar "b") (IRConst $ VEither (Left VAny)) (IRConst $ VEither (Right VAny))) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

isRightFwd :: FDecl
isRightFwd = FDecl (Forall [TV "a", TV "b"] (TEither (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TBool)) ["a"] ["b"] (IRIsRight (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1))]
isRightInv :: FDecl
isRightInv = FDecl (Forall [TV "a", TV "b"] (TBool `TArrow` TEither (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRIf (IRVar "b") (IRConst $ VEither (Right VAny)) (IRConst $ VEither (Left VAny))) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

plusFwd :: FDecl
plusFwd = FDecl (Forall [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["a", "b"] ["c"] (IROp OpPlus (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]
plusInv1 :: FDecl
plusInv1 = FDecl (Forall [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["a", "c"] ["b"] (IROp OpSub (IRVar "c") (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))]
plusInv2 :: FDecl
plusInv2 = FDecl (Forall [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["b", "c"] ["a"] (IROp OpSub (IRVar "c") (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))]

multFwd :: FDecl
multFwd = FDecl (Forall [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["a", "b"] ["c"] (IROp OpMult (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRVar "b"), ("b", IRVar "a")]
multInv1 :: FDecl
multInv1 = FDecl (Forall [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["a", "c"] ["b"] (IROp OpDiv (IRVar "c") (IRVar "a")) (IRConst (VBool True)) False [("a", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "a") (IRVar "a")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "a"))]
multInv2 :: FDecl
multInv2 = FDecl (Forall [] (TFloat `TArrow` (TFloat `TArrow` TFloat))) ["b", "c"] ["a"] (IROp OpDiv (IRVar "c") (IRVar "b")) (IRConst (VBool True)) False [("b", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "b") (IRVar "b")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))]

plusIFwd :: FDecl
plusIFwd = FDecl (Forall [] (TInt `TArrow` (TInt `TArrow` TInt))) ["a", "b"] ["c"] (IROp OpPlus (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))]
plusIInv1 :: FDecl
plusIInv1 = FDecl (Forall [] (TInt `TArrow` (TInt `TArrow` TInt))) ["a", "c"] ["b"] (IROp OpSub (IRVar "c") (IRVar "a")) (IRConst (VBool True)) False [("a", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))]
plusIInv2 :: FDecl
plusIInv2 = FDecl (Forall [] (TInt `TArrow` (TInt `TArrow` TInt))) ["b", "c"] ["a"] (IROp OpSub (IRVar "c") (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))]

multIFwd :: FDecl
multIFwd = FDecl (Forall [] (TInt `TArrow` (TInt `TArrow` TInt))) ["a", "b"] ["c"] (IROp OpMult (IRVar "a") (IRVar "b")) (IRConst (VBool True)) False [("a", IRVar "b"), ("b", IRVar "a")]
multIInv1 :: FDecl
multIInv1 = FDecl (Forall [] (TInt `TArrow` (TInt `TArrow` TInt))) ["a", "c"] ["b"] (IROp OpDiv (IRVar "c") (IRVar "a")) (IRConst (VBool True)) False [("a", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "a") (IRVar "a")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "a"))]
multIInv2 :: FDecl
multIInv2 = FDecl (Forall [] (TInt `TArrow` (TInt `TArrow` TInt))) ["b", "c"] ["a"] (IROp OpDiv (IRVar "c") (IRVar "b")) (IRConst (VBool True)) False [("b", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "b") (IRVar "b")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))]

--tConsFwd :: FDecl
--tConsFwd = FDecl (Forall [] (TFloat `TArrow` (TFloat `TArrow` Tuple TFloat TFloat))) ["a", "b"] ["c", "d"] (IRTCons (IRVar "a") (IRVar "b")) (IRConst (VBool True)) [("a", IRTCons (IRConst (VFloat 1)) (IRVar "b")), ("b", IRTCons (IRVar "a") (IRConst (VFloat 1)))]-- Cannot declare a backward pass here

fstFwd :: FDecl
fstFwd = FDecl (Forall [TV "a", TV "b"] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "a"))) ["a"] ["b"] (IRTFst (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
fstInv :: FDecl
fstInv = FDecl (Forall [TV "a", TV "b"] (TVarR (TV "a") `TArrow` Tuple (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRTCons (IRVar "b") (IRConst VAny)) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]
sndFwd :: FDecl
sndFwd = FDecl (Forall [TV "a", TV "b"] (Tuple (TVarR (TV "a")) (TVarR (TV "b")) `TArrow` TVarR (TV "b"))) ["a"] ["b"] (IRTSnd (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
sndInv :: FDecl
sndInv = FDecl (Forall [TV "a", TV "b"] (TVarR (TV "b") `TArrow` Tuple (TVarR (TV "a")) (TVarR (TV "b")))) ["b"] ["a"] (IRTCons (IRConst VAny) (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

headFwd :: FDecl
headFwd = FDecl (Forall [TV "a"] (ListOf (TVarR (TV "a")) `TArrow` TVarR (TV "a"))) ["a"] ["b"] (IRHead (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
headInv :: FDecl
headInv = FDecl (Forall [TV "a"] (TVarR (TV "a") `TArrow` ListOf (TVarR (TV "a")))) ["b"] ["a"] (IRCons (IRVar "b") (IRConst VAny)) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]

tailFwd :: FDecl
tailFwd = FDecl (Forall [TV "a"] (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a")))) ["a"] ["b"] (IRTail (IRVar "a")) (IRConst (VBool True)) True [("a", IRConst (VFloat 1))]
tailInv :: FDecl
tailInv = FDecl (Forall [TV "a"] (ListOf (TVarR (TV "a")) `TArrow` ListOf (TVarR (TV "a")))) ["b"] ["a"] (IRCons (IRConst VAny) (IRVar "b")) (IRConst (VBool True)) False [("b", IRConst (VFloat 1))]



globalFenv :: FEnv
globalFenv = [("double", FPair doubleFwd [doubleInv]),
              ("exp", FPair expFwd [expInv]),
              ("neg", FPair negFwd [negInv]),
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
              ("fst", FPair fstFwd [fstInv]),
              ("snd", FPair sndFwd [sndInv]),
              ("head", FPair headFwd [headInv]),
              ("tail", FPair tailFwd [tailInv])]

-- Creates a instance of a FPair, that has identifier names given by a monadic function. m should be a supply monad
-- Works by having each identifier renamed using this function
instantiate :: (Monad m) => (String -> m String) -> String -> m FPair
instantiate gen n = do
  let (FPair fwd inv) = case lookup n globalFenv of
                             Just f -> f
                             Nothing -> error ("InjF " ++ n ++ " not found!")
  let FDecl {inputVars=v1, outputVars=v2} = fwd
  let allVarNames = v1 ++ v2  -- All indentifier names in the InjF
  newVarNames <- mapM gen allVarNames -- These are the new names given by the gen function
  let instantiateDecl d = foldr (\(old, new) decl -> renameDecl old new decl) d (zip allVarNames newVarNames) -- Rename all identifiers with the new names
  return (FPair (instantiateDecl fwd) (map instantiateDecl inv))

rename :: String -> String -> IRExpr -> IRExpr
rename old new (IRVar n) | n == old = IRVar new
rename old new expr = expr

renameAll :: String -> String -> IRExpr -> IRExpr
renameAll old new = irMap (rename old new)

renameDecl :: String -> String -> FDecl -> FDecl
renameDecl old new FDecl {contract=sig, inputVars=inVars, outputVars=outVars, body=expr, applicability=app, deconstructing=decons, derivatives=derivs} =
  FDecl {contract=sig, inputVars=map renS inVars, outputVars=map renS outVars, body=ren expr, applicability=ren app, deconstructing=decons, derivatives=map (Data.Bifunctor.bimap renS ren) derivs}
  where
    ren = renameAll old new -- A function that renames old to new
    renS s = if s == old then new else s  -- A function that replaces old string with new strings

getHornClause :: Expr -> [HornClause]
getHornClause e = case e of
  InjF t name params -> (constructHornClause subst eFwd): map (constructHornClause subst) eInv
    where
      subst = (outV, eCN):zip inV (getInputChainNames e)
      eCN = chainName $ getTypeInfo e
      FDecl {inputVars = inV, outputVars = [outV]} = eFwd
      Just (FPair eFwd eInv) = lookup name globalFenv
  _ -> error "Cannot get horn clause of non-predefined function"

constructHornClause :: [(String, ChainName)] -> FDecl -> HornClause
constructHornClause subst decl = (map lookUpSubstAddDet inV, map lookUpSubstAddDet outV, (StubInjF, 0)) --FIXME correct inversion parameters 
  where
    FDecl {inputVars = inV, outputVars = outV} = decl
    lookupSubst v = fromJust (lookup v subst)
    lookUpSubstAddDet v = (lookupSubst v, CInferDeterministic)


getInputChainNames :: Expr -> [ChainName]
getInputChainNames e = map (chainName . getTypeInfo) (getSubExprs e)

propagateValues :: String -> [[Value]] -> [Value]
propagateValues name values = case results of
  Left s -> []
  Right l -> map (fmap failConversionRev) l
  where
    results = sequence (map (generateDet [] [] []) letInBlocks)
    letInBlocks = map (foldr (\(n, p) e -> IRLetIn n (IRConst (fmap failConversionFwd p)) e) fwdExpr) namedParams
    namedParams = map (zip paramNames) valueProd
    valueProd = sequence values
    Just (FPair FDecl {inputVars = paramNames, body = fwdExpr} _) = lookup name globalFenv

parameterCount :: String -> Int
parameterCount name = do
  case lookup name globalFenv of
    Just (FPair FDecl {inputVars=params} _) -> length params
    _ -> error $ "Unknown InjF: " ++ name

failConversionFwd :: Expr -> IRExpr
failConversionFwd = error "Error during value conversion. This should not happen"

failConversionRev :: IRExpr -> Expr
failConversionRev = error "Error during value conversion. This should not happen"
