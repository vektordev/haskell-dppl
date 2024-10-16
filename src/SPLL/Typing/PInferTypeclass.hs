{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module SPLL.Typing.PInferTypeclass (
  showInfer
) where

import SPLL.Typing.ResultTypes

class ListMatch a b
instance ListMatch a ()
instance ListMatch a a

class SameOrList a b res | a b -> res
instance {-# OVERLAPS #-} SameOrList (List ()) (List ()) (List ())
instance SameOrList (List ()) (List x) (List x)
instance SameOrList (List x) (List ()) (List x)
instance SameOrList a a a

data List x

data CExpr rt pt where
  Add :: SumResultType a b res => CExpr Double a -> CExpr Double b -> CExpr Double res
  Mult :: SumResultType a b res => CExpr Double a -> CExpr Double b -> CExpr Double res
  GreaterThan :: CompResultType a b res => CExpr Double a -> CExpr Double b -> CExpr Bool res
  IfThenElse :: (DowngradeResultType cond a tmp,
                 DowngradeResultType tmp b res,
                 SameOrList x y z) => CExpr Bool cond -> CExpr x a -> CExpr y b -> CExpr z res
  ThetaI :: CExpr Double ClassD
  Constant :: Show a => a -> CExpr a ClassD
  Uniform :: CExpr Double ClassI
  Normal :: CExpr Double ClassI
  Null :: CExpr (List ()) ClassD
  Cons :: (DowngradeResultType a b res, ListMatch x y) => CExpr x a -> CExpr (List y) b -> CExpr (List x) res
deriving instance Show (CExpr a b)

data CExpr2 rt pt where
  Add2 :: SumResultType a b res => CExpr2 Double a -> CExpr2 Double b -> CExpr2 Double res
  Constant2 :: Show a => a -> CExpr2 a ClassD
  Lam :: CExpr2 x b
  App :: CExpr2 x b 
deriving instance Show (CExpr2 a c)
-- examDet :: CExpr (List ()) ClassI
examDet = Add2 (Constant2 0.2) (Constant2 0.2)
  
showInfer ::  IO ()
showInfer = do print examDet


