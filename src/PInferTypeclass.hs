{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module PInferTypeclass (
  showInfer
) where

import ResultTypes

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
  Add :: SumResultType a b res => CExpr Float a -> CExpr Float b -> CExpr Float res
  Mult :: SumResultType a b res => CExpr Float a -> CExpr Float b -> CExpr Float res
  GreaterThan :: CompResultType a b res => CExpr Float a -> CExpr Float b -> CExpr Bool res
  IfThenElse :: (DowngradeResultType cond a tmp,
                 DowngradeResultType tmp b res,
                 SameOrList x y z) => CExpr Bool cond -> CExpr x a -> CExpr y b -> CExpr z res
  ThetaI :: CExpr Float ClassD
  Constant :: Show a => a -> CExpr a ClassD
  Uniform :: CExpr Float ClassI
  Normal :: CExpr Float ClassI
  Null :: CExpr (List ()) ClassD
  Cons :: (DowngradeResultType a b res, ListMatch x y) => CExpr x a -> CExpr (List y) b -> CExpr (List x) res
deriving instance Show (CExpr a b)

data CExpr2 rt pt where
  Add2 :: SumResultType a b res => CExpr2 Float a -> CExpr2 Float b -> CExpr2 Float res
  Constant2 :: Show a => a -> CExpr2 a ClassD
  Lam :: CExpr2 x b
  App :: CExpr2 x b 
deriving instance Show (CExpr2 a c)
-- examDet :: CExpr (List ()) ClassI
examDet = Add2 (Constant2 0.2) (Constant2 0.2)
  
showInfer ::  IO ()
showInfer = do print examDet


