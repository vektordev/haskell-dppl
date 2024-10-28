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
import SPLL.Lang.Types

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

plusFwd :: FDecl
plusFwd = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["a", "b"], ["c"], IROp OpPlus (IRVar "a") (IRVar "b"), [("a", IRConst (VFloat 1)), ("b", IRConst (VFloat 1))])
plusInv1 :: FDecl
plusInv1 = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["a", "c"], ["b"], IROp OpSub (IRVar "c") (IRVar "a"), [("a", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))])
plusInv2 :: FDecl
plusInv2 = FDecl (TFloat `TArrow` (TFloat `TArrow` TFloat), ["b", "c"], ["a"], IROp OpSub (IRVar "c") (IRVar "b"), [("b", IRConst (VFloat (-1))), ("c", IRConst (VFloat 1))])

globalFenv :: FEnv
globalFenv = [("double", FPair (doubleFwd, [doubleInv])),
              ("exp", FPair (expFwd, [expInv])),
              ("plus", FPair (plusFwd, [plusInv1, plusInv2]))]

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