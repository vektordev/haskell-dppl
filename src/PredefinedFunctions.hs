module PredefinedFunctions (
globalFenv,
getHornClause,
FPair(..),
FDecl(..),
FEnv,
propagateValues
) where

import SPLL.Typing.RType (RType(..))
import SPLL.IntermediateRepresentation (IRExpr, IRExpr(..), Operand(..), UnaryOperand(..)) --FIXME
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import Data.Set (fromList)
import Data.Maybe (fromJust)
import SPLL.Lang.Types
import IRInterpreter
import Control.Monad

-- InputVars, OutputVars, fwd, grad
newtype FDecl = FDecl (RType, [String], [String], IRExpr, [(String, IRExpr)]) deriving (Show, Eq)
-- Forward, inverse
newtype FPair = FPair (FDecl, [FDecl]) deriving (Show, Eq)
type FEnv = [(String, FPair)]

doubleFwd :: FDecl
doubleFwd = FDecl (TArrow TFloat TFloat, ["a"], ["b"], IROp OpMult (IRVar "a") (IRConst $ VFloat 2) , [("a", IRConst $ VFloat 2)])
doubleInv :: FDecl
doubleInv = FDecl (TArrow TFloat TFloat, ["b"], ["a"], IROp OpDiv (IRVar "b") (IRConst $ VFloat 2) , [("b", IRConst $ VFloat 0.5)])

expFwd :: FDecl
expFwd = FDecl (TArrow TFloat TFloat, ["a"], ["b"], IRUnaryOp OpExp (IRVar "a") , [("a", IRUnaryOp OpExp (IRVar "a"))])
expInv :: FDecl
expInv = FDecl (TArrow TFloat TFloat, ["b"], ["a"], IRUnaryOp OpLog (IRVar "b") , [("b", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))])

negFwd :: FDecl
negFwd = FDecl (TArrow TFloat TFloat, ["a"], ["b"], IRUnaryOp OpNeg (IRVar "a") , [("a", IRConst (VFloat (-1)))])
negInv :: FDecl
negInv = FDecl (TArrow TFloat TFloat, ["b"], ["a"], IRUnaryOp OpNeg (IRVar "b") , [("b", IRConst (VFloat (-1)))])

plusFwd :: FDecl
plusFwd = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["a", "b"], ["c"], IROp OpPlus (IRVar "a") (IRVar "b"), [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))])
plusInv1 :: FDecl
plusInv1 = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["a", "c"], ["b"], IROp OpSub (IRVar "c") (IRVar "a"), [("a", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))])
plusInv2 :: FDecl
plusInv2 = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["b", "c"], ["a"], IROp OpSub (IRVar "c") (IRVar "b"), [("b", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))])

multFwd :: FDecl
multFwd = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["a", "b"], ["c"], IROp OpMult (IRVar "a") (IRVar "b"), [("a", IRVar "b"), ("b", IRVar "a")])
multInv1 :: FDecl
multInv1 = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["a", "c"], ["b"], IROp OpDiv (IRVar "c") (IRVar "a"), [("a", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "a") (IRVar "a")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "a"))])
multInv2 :: FDecl
multInv2 = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["b", "c"], ["a"], IROp OpDiv (IRVar "c") (IRVar "b"), [("b", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "b") (IRVar "b")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))])

plusIFwd :: FDecl
plusIFwd = FDecl (TInt `TArrow` (TInt `TArrow` TInt), ["a", "b"], ["c"], IROp OpPlus (IRVar "a") (IRVar "b"), [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))])
plusIInv1 :: FDecl
plusIInv1 = FDecl (TInt `TArrow` (TInt `TArrow` TInt), ["a", "c"], ["b"], IROp OpSub (IRVar "c") (IRVar "a"), [("a", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))])
plusIInv2 :: FDecl
plusIInv2 = FDecl (TInt `TArrow` (TInt `TArrow` TInt), ["b", "c"], ["a"], IROp OpSub (IRVar "c") (IRVar "b"), [("b", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))])

multIFwd :: FDecl
multIFwd = FDecl (TInt `TArrow` (TInt `TArrow` TInt), ["a", "b"], ["c"], IROp OpMult (IRVar "a") (IRVar "b"), [("a", IRVar "b"), ("b", IRVar "a")])
multIInv1 :: FDecl
multIInv1 = FDecl (TInt `TArrow` (TInt `TArrow` TInt), ["a", "c"], ["b"], IROp OpDiv (IRVar "c") (IRVar "a"), [("a", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "a") (IRVar "a")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "a"))])
multIInv2 :: FDecl
multIInv2 = FDecl (TInt `TArrow` (TInt `TArrow` TInt), ["b", "c"], ["a"], IROp OpDiv (IRVar "c") (IRVar "b"), [("b", IRUnaryOp OpNeg (IROp OpDiv (IRVar "c") (IROp OpMult (IRVar "b") (IRVar "b")))), ("c", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))])


tConsFwd :: FDecl
tConsFwd = FDecl (TFloat `TArrow` (TFloat `TArrow` Tuple TFloat TFloat), ["a", "b"], ["c", "d"], IRTCons (IRVar "a") (IRVar "b"), [("a", IRTCons (IRConst (VFloat 1)) (IRVar "b")), ("b", IRTCons (IRVar "a") (IRConst (VFloat 1)))])
-- Cannot declare a backward pass here

globalFenv :: FEnv
globalFenv = [("double", FPair (doubleFwd, [doubleInv])),
              ("exp", FPair (expFwd, [expInv])),
              ("neg", FPair (negFwd, [negInv])),
              ("plus", FPair (plusFwd, [plusInv1, plusInv2])),
              ("plusI", FPair (plusIFwd, [plusIInv1, plusIInv2])),
              ("mult", FPair (multFwd, [multInv1, multInv2])),
              ("multI", FPair (multIFwd, [multIInv1, multIInv2]))]

getHornClause :: Expr -> [HornClause]
getHornClause e = case e of
  InjF t name params -> (constructHornClause subst eFwd): map (constructHornClause subst) eInv
    where
      subst = (outV, eCN):zip inV (getInputChainNames e)
      eCN = chainName $ getTypeInfo e
      FDecl (_, inV, [outV], _, _) = eFwd
      Just (FPair (eFwd, eInv)) = lookup name globalFenv
  _ -> error "Cannot get horn clause of non-predefined function"

constructHornClause :: [(String, ChainName)] -> FDecl -> HornClause
constructHornClause subst decl = (map lookUpSubstAddDet inV, map lookUpSubstAddDet outV, (StubInjF, 0)) --FIXME correct inversion parameters 
  where
    FDecl (_, inV, outV, _, _) = decl
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
    Just (FPair (FDecl (_, paramNames, _, fwdExpr, _), _)) = lookup name globalFenv


failConversionFwd :: Expr -> IRExpr
failConversionFwd = error "Error during value conversion. This should not happen"

failConversionRev :: IRExpr -> Expr
failConversionRev = error "Error during value conversion. This should not happen"
