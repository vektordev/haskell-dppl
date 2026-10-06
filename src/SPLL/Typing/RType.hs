-- | Core return-type definitions for SPLL.
module SPLL.Typing.RType
  ( TVarR(..)
  , RType(..)
  , Shape
  , Extent(..)
  , extentSize
  , shapeNumel
  , shapeRank
  , dropAxis
  , isTensorElemType
  , prettyShape
  , ClassConstraint(..)
  , Scheme(..)
  , matches
  , greaterType
  , satisfiesClass
  , constraintTV
  ) where

import Data.List (intercalate)

newtype TVarR = TV String
  deriving (Show, Eq, Ord)

-- | The shape of a tensor: the extent of each axis, outermost first. The rank
-- is the length. Shared by the IR tensor value ('VTensor') and the surface
-- type @TTensor Shape RType@ (design tensors-in-core-language §2.2), so the
-- surface type lowers onto the IR value already carrying the shape, with
-- nothing to re-represent. Rank 0 is not a shape: the parser refuses
-- @Tensor[] τ@.
type Shape = [Extent]

-- | The extent of one axis.
--
-- A sum type with a single constructor on purpose (design
-- tensors-in-core-language §2.2, and §7 on why restrictive choices are the
-- cheap ones to lift): shape /variables/ are deliberately out (decision B), and spelling this @type Shape = [Int]@ would make admitting an
-- @EVar@ later a change to the arity of every shape pattern in the compiler
-- rather than one new constructor.
newtype Extent = EFixed Int
  deriving (Show, Eq, Ord)

extentSize :: Extent -> Int
extentSize (EFixed n) = n

-- | The number of elements a shape holds -- the product of its extents. A
-- rank-0 shape has one element by this rule, but rank 0 is not an inhabited
-- shape (see the note on 'shapeRank').
shapeNumel :: Shape -> Int
shapeNumel = product . map extentSize

shapeRank :: Shape -> Int
shapeRank = length

-- | Drop one axis from a shape, as a reduction or an index along that axis
-- does. 'Nothing' when the axis is out of range.
dropAxis :: Int -> Shape -> Maybe Shape
dropAxis i sh
  | i >= 0 && i < length sh = Just (take i sh ++ drop (i + 1) sh)
  | otherwise = Nothing

-- | The element types a 'TTensor' may carry: a scalar base type only
-- (design tensors-in-core-language §2.3). Tensor-of-tuple/ADT raises a layout
-- question neither goal needs, and a nested tensor is rejected rather than
-- normalized, so @TTensor _ (TTensor _ _)@ is never constructed.
isTensorElemType :: RType -> Bool
isTensorElemType t = t `elem` [TFloat, TInt, TBool, TSymbol]

-- | A shape as the user writes it: @[3,4]@.
prettyShape :: Shape -> String
prettyShape sh = "[" ++ intercalate "," (map (show . extentSize) sh) ++ "]"
  
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
           | TArrow RType RType
           -- | A statically shaped, homogeneous block of scalars (design
           -- tensors-in-core-language §2): @Tensor[3,4] Float@. The element
           -- type is a scalar base type ('isTensorElemType'), the shape is
           -- never rank 0, and @Tensor[1] Float@ is not @Float@ -- no squeeze,
           -- no coercion. Shapes unify only when equal (no shape variables, no
           -- broadcasting).
           | TTensor Shape RType
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
matches (GreaterType t1 t2) (GreaterType t3 t4) = case (greaterType t1 t2, greaterType t3 t4)
  of
    (Just a, Just b) -> a `matches` b
    (Nothing, Nothing) -> True
    (_, _) -> False
matches (Tuple t11 t12) (Tuple t21 t22) = t11 `matches` t21 && t12 `matches` t22
matches (TEither t11 t12) (TEither t21 t22) = t11 `matches` t21 && t12 `matches` t22
matches (TTensor s1 e1) (TTensor s2 e2) = s1 == s2 && e1 `matches` e2
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

