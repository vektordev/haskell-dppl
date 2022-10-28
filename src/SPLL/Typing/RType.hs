module SPLL.Typing.RType where

newtype TVar = TV String
  deriving (Show, Eq, Ord)
  
data RType = TBool
           | TInt
           | TSymbol
           | TFloat
           | ListOf RType
           | NullList
           | RIdent String
           | RConstraint String RType RType
           | Arrow RType RType
           | TVar TVar
           | TArr RType RType
           deriving (Show)

instance Eq RType where
  (==) TBool TBool = True
  (==) TInt TInt = True
  (==) TSymbol TSymbol = True
  (==) TFloat TFloat = True
  (==) (Arrow left right) (Arrow left2 right2) = left == left2 && right == right2
  (==) (ListOf x) (ListOf y) = x == y
  (==) NullList NullList = True
  (==) (RIdent a) (RIdent b) = a == b
  (==) (RConstraint _ _ retT) (RConstraint _ _ retT2) = retT == retT2
  (==) _ _ = False
