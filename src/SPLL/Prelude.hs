module SPLL.Prelude where

import SPLL.Lang.Lang
import SPLL.Lang.Types (makeTypeInfo)
{-
class (Num b, Show b) => Const a where
  value :: a -> Value b
  const :: a -> Expr () b
  const x = Constant () (value x)

instance Const Bool where
  value bl = VBool bl

--instance Const Float where
--  const bl = Constant () (VFloat bl)

instance Const Int where
  value i = VInt i

instance (Const a) => Const [a] where
  value lst = VList (map value lst)
-}
ite :: (Num a, Show a) => Expr a -> Expr a -> Expr a -> Expr a
ite = IfThenElse makeTypeInfo

(>=) :: (Num a, Show a) => Expr a -> Expr a -> Expr a
(>=) = GreaterThan makeTypeInfo

theta :: (Num a, Show a) => Int -> Expr a
theta = undefined -- ThetaI makeTypeInfo 

uniform :: (Num a, Show a) => Expr a
uniform = Uniform makeTypeInfo

normal :: (Num a, Show a) => Expr a
normal = Normal makeTypeInfo

(*) :: (Num a, Show a) => Expr a -> Expr a -> Expr a
(*) = MultF makeTypeInfo

(+) :: (Num a, Show a) => Expr a -> Expr a -> Expr a
(+) = PlusF makeTypeInfo

null :: (Num a, Show a) => Expr a
null = Null makeTypeInfo

cons :: (Num a, Show a) => Expr a -> Expr a -> Expr a
cons = Cons makeTypeInfo

(<:>) :: (Num a, Show a) => Expr a -> Expr a -> Expr a
(<:>) = cons
