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
ite :: Expr -> Expr -> Expr -> Expr
ite = IfThenElse makeTypeInfo

(>=) :: Expr -> Expr -> Expr
(>=) = GreaterThan makeTypeInfo

theta :: Int -> Expr
theta = undefined -- ThetaI makeTypeInfo 

uniform :: Expr
uniform = Uniform makeTypeInfo

normal :: Expr
normal = Normal makeTypeInfo

(*) :: Expr -> Expr -> Expr
(*) = MultF makeTypeInfo

(+) :: Expr -> Expr -> Expr
(+) = PlusF makeTypeInfo

null :: Expr
null = Null makeTypeInfo

cons :: Expr -> Expr -> Expr
cons = Cons makeTypeInfo

(<:>) :: Expr -> Expr -> Expr
(<:>) = cons
