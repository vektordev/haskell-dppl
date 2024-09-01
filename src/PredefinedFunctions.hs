module PredefinedFunctions (
globalFenv,
getHornClause,
FPair(..),
FDecl(..),
FEnv
) where

import SPLL.Typing.RType (RType(..))
import SPLL.IntermediateRepresentation (IRExpr, IRExpr(..), Operand(..), UnaryOperand(..)) --FIXME
import SPLL.Lang.Lang
import SPLL.Typing.Typing
import Data.Set (fromList)
import Data.Maybe (fromJust)

-- InputVars, OutputVars, fwd, grad
newtype FDecl a = FDecl (RType, [String], [String], IRExpr a, [(String, IRExpr a)]) deriving (Show, Eq)
-- Forward, inverse
newtype FPair a = FPair (FDecl a, [FDecl a]) deriving (Show, Eq)
type FEnv a = [(String, FPair a)]

doubleFwd :: (Floating a) => FDecl a
doubleFwd = FDecl (TArrow TFloat TFloat, ["a"], ["b"], IROp OpMult (IRVar "a") (IRConst $ VFloat 2) , [("a", IRConst $ VFloat 2)])
doubleInv :: (Floating a) => FDecl a
doubleInv = FDecl (TArrow TFloat TFloat, ["b"], ["a"], IROp OpDiv (IRVar "b") (IRConst $ VFloat 2) , [("b", IRConst $ VFloat 0.5)])

expFwd :: (Floating a) => FDecl a
expFwd = FDecl (TArrow TFloat TFloat, ["a"], ["b"], IRUnaryOp OpExp (IRVar "a") , [("a", IRUnaryOp OpExp (IRVar "a"))])
expInv :: (Floating a) => FDecl a
expInv = FDecl (TArrow TFloat TFloat, ["b"], ["a"], IRUnaryOp OpLog (IRVar "b") , [("b", IROp OpDiv (IRConst (VFloat 1)) (IRVar "b"))])

plusFwd :: (Floating a) => FDecl a
plusFwd = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["a", "b"], ["c"], IROp OpPlus (IRVar "a") (IRVar "b"), [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))])
plusInv1 :: (Floating a) => FDecl a
plusInv1 = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["a", "c"], ["b"], IROp OpSub (IRVar "c") (IRVar "a"), [("a", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))])
plusInv2 :: (Floating a) => FDecl a
plusInv2 = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["b", "c"], ["a"], IROp OpSub (IRVar "c") (IRVar "b"), [("b", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))])

globalFenv :: (Floating a) => FEnv a
globalFenv = [("double", FPair (doubleFwd, [doubleInv])),
              ("exp", FPair (expFwd, [expInv])),
              ("plus", FPair (plusFwd, [plusInv1, plusInv2]))]

getHornClause :: (Eq a, Floating a) => Expr a -> [HornClause a]
getHornClause e = case e of
  InjF t name params -> (constructHornClause subst eFwd): map (constructHornClause subst) eInv
    where
      subst = (outV, eCN):zip inV (getInputChainNames e)
      eCN = chainName $ getTypeInfo e
      FDecl (_, inV, [outV], _, _) = eFwd
      Just (FPair (eFwd, eInv)) = lookup name globalFenv
  _ -> error "Cannot get horn clause of non-predefined function"

constructHornClause :: (Eq a) => [(String, ChainName)] -> FDecl a -> HornClause a
constructHornClause subst decl = (map lookUpSubstAddDet inV, map lookUpSubstAddDet outV, (StubInjF, 0)) --FIXME correct inversion parameters 
  where
    FDecl (_, inV, outV, _, _) = decl
    lookupSubst v = fromJust (lookup v subst)
    lookUpSubstAddDet v = (lookupSubst v, CInferDeterministic)


getInputChainNames :: Expr a -> [ChainName]
getInputChainNames e = map (chainName . getTypeInfo) (getSubExprs e)