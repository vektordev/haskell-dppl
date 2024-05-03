module SPLL.Typing.RType where

newtype TVarR = TV String
  deriving (Show, Eq, Ord)
  
data RType = TBool
           | TInt
           | TSymbol
           | TFloat
           | ListOf RType
           | Tuple RType RType
           | NullList
           | BottomTuple
           | RIdent String
           | RConstraint String RType RType
           | TArrow RType RType
           | TVarR TVarR
           | GreaterType RType RType
           | NotSetYet
           deriving (Show, Ord)


instance Eq RType where
  (==) TBool TBool = True
  (==) TInt TInt = True
  (==) TSymbol TSymbol = True
  (==) TFloat TFloat = True
  (==) (TArrow left right) (TArrow left2 right2) = left == left2 && right == right2
  (==) (ListOf x) (ListOf y) = x == y
  (==) NullList NullList = True
  (==) BottomTuple BottomTuple = True
  (==) (RIdent a) (RIdent b) = a == b
  (==) (RConstraint _ _ retT) (RConstraint _ _ retT2) = retT == retT2
  (==) (GreaterType t1 t2) (GreaterType t3 t4) = greaterType t1 t2 == greaterType t1 t2
  (==) (Tuple t11 t12) (Tuple t21 t22) = t11 == t21 && t12 == t22
  (==) _ _ = False

greaterType :: RType -> RType -> Maybe RType
greaterType (ListOf t1) NullList = Just $ ListOf t1
greaterType NullList (ListOf t1)  = Just $ ListOf t1
greaterType t1 t2 | t1 == t2 =  Just t1
greaterType _ _ = Nothing
