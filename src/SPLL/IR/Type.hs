-- | The value types of the IR, and the translation of a monomorphic 'RType'
-- into one. Kept apart from "SPLL.IRTypeCheck" so that the IR's ADT functions
-- ("SPLL.IR.ADT") can state their types without importing the checker.
module SPLL.IR.Type
  ( IRType(..)
  , irTypeOfRType
  ) where
import SPLL.Typing.RType (RType(..), Shape)

-- | The value types of the IR.
--
-- Unlike 'RType', a tensor's element type is not restricted to a scalar: the
-- compiler builds 'BTensor's over enumerated domains of tuples, 'Either's and
-- ADT values (an enumerated sum maps over one). A tensor's shape is part of
-- its type, as in 'TTensor', and two tensor types unify only at equal shapes.
data IRType
  = ITBool
  | ITInt
  | ITFloat
  | ITSymbol
  | ITUnit
  | ITThetaTree
  | ITList IRType
  | ITTuple IRType IRType
  | ITEither IRType IRType
  | ITADT String          -- ^ By type name, as 'TADT'.
  | ITTensor Shape IRType
  | ITArrow IRType IRType
  | ITVar Int             -- ^ A type variable. In a checker result, a variable is universally quantified.
  deriving (Show, Eq, Ord)

-- | A monomorphic 'RType' as an 'IRType'. 'Nothing' when it holds a type
-- variable or one of the 'RType's with no runtime content of their own.
irTypeOfRType :: RType -> Maybe IRType
irTypeOfRType rt = case rt of
  TBool -> Just ITBool
  TInt -> Just ITInt
  TSymbol -> Just ITSymbol
  TFloat -> Just ITFloat
  TUnit -> Just ITUnit
  TThetaTree -> Just ITThetaTree
  ListOf a -> ITList <$> irTypeOfRType a
  Tuple a b -> ITTuple <$> irTypeOfRType a <*> irTypeOfRType b
  TEither a b -> ITEither <$> irTypeOfRType a <*> irTypeOfRType b
  TADT n -> Just (ITADT n)
  TArrow a b -> ITArrow <$> irTypeOfRType a <*> irTypeOfRType b
  TTensor sh a -> ITTensor sh <$> irTypeOfRType a
  NullList -> Nothing
  BottomTuple -> Nothing
  TVarR _ -> Nothing
  GreaterType _ _ -> Nothing
  NotSetYet -> Nothing
