module RType where

data RType = TBool
           | TFloat
           | ListOf RType
           | NullList
           | RIdent String
           | RConstraint String RType RType
           | Arrow RType RType
           deriving (Show)

instance Eq RType where
  (==) TBool TBool = True
  (==) TFloat TFloat = True
  (==) (ListOf x) (ListOf y) = x == y
  (==) NullList NullList = True
  (==) (RIdent a) (RIdent b) = a == b
  (==) (RConstraint _ _ retT) (RConstraint _ _ retT2) = retT == retT2
  (==) _ _ = False
