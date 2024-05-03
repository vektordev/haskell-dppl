{-# LANGUAGE FlexibleContexts #-}
module InjectiveFunctions (
  globalFenv
, rangeSwap
, rangeMap
, rangeGrad
, autoEnv
, autoExpr
, autoVal
) where

import SPLL.Lang
import SPLL.Typing.RType
import SPLL.Typing.Typing
import Numeric.AD (grad', auto)
import Numeric.AD.Internal.Reverse ( Reverse, Tape)
import Data.Reflection (Reifies)
globalFenv2 :: (Num a, Floating a) => FEnv2 a
globalFenv2 = [("plus", FPair2 (\[VFloat p] x->  x + p, \[VFloat p] x->  x - p,
                        \[VFloat p] x -> 1)),
               ("mult", FPair2 (\[VFloat p] x->  x * p, \[VFloat p] x->  x / p,
                                        \[VFloat p] x -> 1/p))
                        ]
invTest :: (Floating a) => Params a -> Value a ->  Value a
invTest  [VFloat p] (VFloat x)  = VFloat $ x/ p
-- Debug FEnv
globalFenv :: (Floating a) => FEnv a
globalFenv = [("plus", FPair (TArrow TFloat (TArrow TFloat TFloat), plusFwd, plusInv, plusInvGrad)),
              ("mult", FPair (TArrow TFloat (TArrow TFloat TFloat), multFwd, multInv, multInvGrad)),
              ("sig", FPair (TArrow TFloat TFloat, sigFwd, sigInv, sigInvGrad)),
              ("not", FPair (TArrow TBool TBool, notFwd, notFwd, notInvGrad)),
              ("listAdd", FPair (TArrow (ListOf TFloat) (TArrow (ListOf TFloat) (ListOf TFloat)),
                  plusListFwd, plusListInv, plusListInvGrad)),
              ("listMult", FPair (TArrow (ListOf TFloat) (TArrow (ListOf TFloat) (ListOf TFloat)),
                                multListFwd, multListInv, multListInvGrad))  ]
rangeSwap :: (Floating a, Ord a) => (Value a -> a) -> Value a -> Value a
rangeSwap f l@(VRange limits) = if (f (VFloat 0.0)) < 0 then swapLimits l else l
rangeSwap _ v = v

rangeMap :: (Floating a) => (Value a -> Value a) -> Value a -> Value a
rangeMap f (VRange (Limits v1 v2)) = VRange (Limits (fmap f v1) (fmap f v2))
rangeMap f v = f v

rangeGrad :: (Floating a) => (Value a -> a) -> Value a -> a
rangeGrad f (VRange (Limits v1 v2)) = 1.0
rangeGrad f v = f v

plusFwd :: (Floating a) => Params a -> Value a -> Value a
plusFwd [VFloat p] (VFloat x) = VFloat $ x + p
plusFwd _ _ = error "plus called with non-fitting arguments"

plusInv :: (Floating a) => Params a -> Value a -> Value a
plusInv [VFloat p] (VFloat x) = VFloat $ x - p
plusInv _ _ = error "plus called with non-fitting arguments"

plusInvGrad :: (Floating a) => Params a -> Value a -> a
plusInvGrad [VFloat p] (VFloat x) = 1
plusInvGrad _ _ = error "plus called with non-fitting arguments"

multFwd :: (Floating a) => Params a -> Value a -> Value a
multFwd [VFloat p] (VFloat x) = VFloat $ x * p
multFwd _ _ = error "mult called with non-fitting arguments"

multInv :: (Floating a) => Params a -> Value a -> Value a
multInv val (VFloat x) = VFloat $ divScalar val x
mulInv _ _ = error "mult called with non-fitting arguments"

divScalar :: (Floating a) => Params a -> a -> a
divScalar [VFloat p] x = x/p

gradScalar :: (Floating a) => Params a -> a -> a
gradScalar par v =  head (snd (grad' (\[val] -> divScalar (map autoVal par) val) [v]))

multInvGrad :: (Floating a) => Params a -> Value a -> a
multInvGrad val (VFloat x) =  gradScalar val x
multInvGrad _ _ = error "mult called with non-fitting arguments"

sigFwd :: (Floating a) => Params a -> Value a -> Value a
sigFwd [] (VFloat x) = VFloat $ 1/(1 + (exp (-x)))
sigFwd _ _ = error "sig called with non-fitting arguments"

sigInv :: (Floating a) => Params a -> Value a -> Value a
sigInv [] (VFloat x) = VFloat $ sigScalar [] x
sigInv _ _ = error "sig called with non-fitting arguments"

sigScalar :: (Floating a) => Params a -> a -> a
sigScalar [] x = log (x/(1-x))

gradSig :: (Floating a) => Params a -> a -> a
gradSig [] v =  head (snd (grad' (\[val] -> sigScalar [] val) [v]))

sigInvGrad :: (Floating a) => Params a -> Value a -> a
sigInvGrad [] (VFloat x) = gradSig [] x
sigInvGrad _ _ = error "sig called with non-fitting arguments"

notFwd :: (Floating a) => Params a -> Value a -> Value a
notFwd [] (VBool x) = VBool $ not x
notFwd _ _ = error "not called with non-fitting arguments"


notInvGrad :: (Floating a) => Params a -> Value a -> a
notInvGrad [] (VBool x) = 1
notInvGrad _ _ = error "not called with non-fitting arguments"

plusListFwd :: (Floating a) => Params a -> Value a -> Value a
plusListFwd [VList vl] (VList x) = VList $ zipWith (\a b -> plusFwd [a] b) vl x
plusListFwd _ _ = error "pluslist called with non-fitting arguments"

plusListInv :: (Floating a) => Params a -> Value a -> Value a
plusListInv [VList vl] (VList x) = VList $ zipWith (\a b -> plusInv [a] b) vl x
plusListInv _ _ = error "pluslist called with non-fitting arguments"

plusListInvGrad :: (Floating a) => Params a -> Value a -> a
plusListInvGrad [VList vl] (VList x) = product (zipWith (\a b -> plusInvGrad [a] b) vl x)
plusListInvGrad _ _ = error "pluslist called with non-fitting arguments"

multListFwd :: (Floating a) => Params a -> Value a -> Value a
multListFwd [VList vl] (VList x) = VList $ zipWith (\a b -> multFwd [a] b) vl x
multListFwd _ _ = error "multinv called with non-fitting arguments"

multListInv :: (Floating a) => Params a -> Value a -> Value a
multListInv [VList vl] (VList x) = VList $ zipWith (\a b -> multInv [a] b) vl x
multListInv _ _ = error "pluslist called with non-fitting arguments"

multListInvGrad :: (Floating a) => Params a -> Value a -> a
multListInvGrad [VList vl] (VList x) = product (zipWith (\a b -> multInvGrad [a] b) vl x)
multListInvGrad _ _ = error "pluslist called with non-fitting arguments"


autoExpr :: (Num a, Reifies s Tape) => Expr x a -> Expr x (Reverse s a)
autoExpr = exprMap auto

autoEnv :: (Num a, Reifies s Tape) => Env x a -> Env x (Reverse s a)
autoEnv = map (\ (name, expr) -> (name, autoExpr expr))

autoVal :: (Num a, Reifies s Tape) => Value a -> Value (Reverse s a)
autoVal (VBool x) = VBool x
autoVal (VFloat y) = VFloat (auto y)
autoVal (VList xs) = VList (map autoVal xs)
autoVal (VTuple x1 x2) = VTuple (autoVal x1) (autoVal x2)
autoVal (VInt x) = VInt x
autoVal (VSymbol x) = VSymbol x
