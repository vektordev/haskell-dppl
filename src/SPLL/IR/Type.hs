-- | The value types of the IR, and the translation of a monomorphic 'RType'
-- into one. Kept apart from "SPLL.IRTypeCheck" so that the IR's ADT functions
-- ("SPLL.IR.ADT") can state their types without importing the checker.
module SPLL.IR.Type
  ( IRType(..)
  , irTypeOfRType
  , irConformanceType
  , IRADTDecl(..)
  , IRADTConstructorDecl
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

-- | The type a runtime tag check ('SPLL.IntermediateRepresentation.IRConformsTo')
-- tests against: total, where 'irTypeOfRType' is not. A part with no checkable
-- runtime tag (a type variable, a frontend-only type state) becomes
-- @'ITVar' 0@, which every runtime accepts, so the guard never rejects on it.
irConformanceType :: RType -> IRType
irConformanceType rt = case rt of
  ListOf a -> ITList (irConformanceType a)
  Tuple a b -> ITTuple (irConformanceType a) (irConformanceType b)
  TEither a b -> ITEither (irConformanceType a) (irConformanceType b)
  TArrow a b -> ITArrow (irConformanceType a) (irConformanceType b)
  TTensor sh a -> ITTensor sh (irConformanceType a)
  _ -> maybe (ITVar 0) id (irTypeOfRType rt)

-- | An algebraic data type as the IR knows it: constructors with typed fields.
data IRADTDecl = IRADTDecl
  { irDataName :: String
  , irConstructors :: [IRADTConstructorDecl]
  } deriving (Show, Eq)

type IRADTConstructorDecl = (String, [(String, IRType)])
