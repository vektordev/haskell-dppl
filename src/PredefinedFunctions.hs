module PredefinedFunctions where

import SPLL.Typing.RType (RType(..))
import SPLL.IntermediateRepresentation (IRExpr, IRExpr(..), Operand(..)) --FIXME
import SPLL.Lang


  
-- InputVars, OutputVars, fwd, grad
newtype FDecl a = FDecl (RType, [String], [String], IRExpr a, [(String, IRExpr a)])
-- Forward, inverse
newtype FPair a = FPair (FDecl a, [FDecl a])
type FEnv a = [(String, FPair a)]

doubleFwd :: (Floating a) => FDecl a
doubleFwd = FDecl (TArrow TFloat TFloat, ["a"], ["b"], IROp OpMult (IRVar "a") (IRConst $ VFloat 2) , [("a", IRConst $ VFloat 2)])

doubleInv :: (Floating a) => FDecl a
doubleInv = FDecl (TArrow TFloat TFloat, ["b"], ["a"], IROp OpDiv (IRVar "b") (IRConst $ VFloat 2) , [("b", IRConst $ VFloat 0.5)])

globalFenv :: (Floating a) => FEnv a
globalFenv = [("double", FPair (doubleFwd, [doubleInv]))]