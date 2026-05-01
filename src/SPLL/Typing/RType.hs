module SPLL.Typing.RType where

newtype TVarR = TV String
  deriving (Show, Eq, Ord)
  
data RType = TBool
           | TInt
           | TSymbol
           | TFloat
           | TUnit
           | TThetaTree
           | ListOf RType
           | Tuple RType RType
           | TEither RType RType
           | TADT String
           | NullList
           | BottomTuple
           | RIdent String
           | RConstraint String RType RType
           | TArrow RType RType
           | TVarR TVarR
           | GreaterType RType RType
           | NotSetYet
           deriving (Show, Eq, Ord)

matches :: RType -> RType -> Bool
matches TBool TBool = True
matches TInt TInt = True
matches TSymbol TSymbol = True
matches TFloat TFloat = True
matches TUnit TUnit = True
matches TThetaTree TThetaTree = True
matches (TADT ty1) (TADT ty2) = ty1 == ty2
matches (TVarR x) (TVarR y) = x == y
matches (TArrow left right) (TArrow left2 right2) = left `matches` left2 && right `matches` right2
matches (ListOf x) (ListOf y) = x `matches` y
matches NullList NullList = True
matches BottomTuple BottomTuple = True
matches (RIdent a) (RIdent b) = a == b
matches (RConstraint _ _ retT) (RConstraint _ _ retT2) = retT `matches` retT2
matches (GreaterType t1 t2) (GreaterType t3 t4) = case (greaterType t1 t2, greaterType t1 t2)
  of
    (Just a, Just b) -> a `matches` b
    (Nothing, Nothing) -> True
    (x, y) -> False
matches (Tuple t11 t12) (Tuple t21 t22) = t11 `matches` t21 && t12 `matches` t22
matches (TEither t11 t12) (TEither t21 t22) = t11 `matches` t21 && t12 `matches` t22
matches _ _ = False -- TODO: This might be too aggressive, or it might not break when RType changes.
  
data ClassConstraint = CNum TVarR
                     | CFractional TVarR
                     | COrd TVarR
                     | CEq TVarR
                     | CDiscrete TVarR
                     deriving (Show, Eq, Ord)

data Scheme = Forall [TVarR] [ClassConstraint] RType
  deriving (Show, Eq)

greaterType :: RType -> RType -> Maybe RType
greaterType (ListOf t1) NullList = Just $ ListOf t1
greaterType NullList (ListOf t1)  = Just $ ListOf t1
greaterType t1 t2 | t1 `matches` t2 =  Just t1
greaterType _ _ = Nothing

isOnlyNumbers :: RType -> Bool
isOnlyNumbers TFloat = True
isOnlyNumbers TInt = True
isOnlyNumbers (a `TArrow` b) = isOnlyNumbers b
isOnlyNumbers (ListOf t) = isOnlyNumbers t
isOnlyNumbers (Tuple a b) = isOnlyNumbers a && isOnlyNumbers b
isOnlyNumbers (TEither a b) = isOnlyNumbers a && isOnlyNumbers b
isOnlyNumbers _ = False

satisfiesClass :: ClassConstraint -> RType -> Bool
satisfiesClass (CNum _)        TFloat = True
satisfiesClass (CNum _)        TInt   = True
satisfiesClass (CFractional _) TFloat = True
satisfiesClass (COrd _)        TFloat = True
satisfiesClass (COrd _)        TInt   = True
satisfiesClass (CEq _)         TFloat = True
satisfiesClass (CEq _)         TInt   = True
satisfiesClass (CEq _)         TBool  = True
satisfiesClass (CEq _)         TSymbol = True
satisfiesClass (CEq _)         (TADT _) = True
satisfiesClass (CDiscrete _)   TBool  = True
satisfiesClass (CDiscrete _)   TSymbol = True
satisfiesClass (CDiscrete _)   (TADT _) = True
satisfiesClass (CDiscrete _)   TInt   = True
satisfiesClass _               _      = False

-- Extract the TVarR from any ClassConstraint
constraintTV :: ClassConstraint -> TVarR
constraintTV (CNum tv)        = tv
constraintTV (CFractional tv) = tv
constraintTV (COrd tv)        = tv
constraintTV (CEq tv)         = tv
constraintTV (CDiscrete tv)   = tv

