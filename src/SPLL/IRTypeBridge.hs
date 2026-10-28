-- | The frontend's translation of its 'RType' into the IR's 'IRType'. It lives
-- here, not in "SPLL.IR.Type", because the IR package knows nothing of 'RType'.
module SPLL.IRTypeBridge
  ( irTypeOfRType
  , irConformanceType
  ) where

import SPLL.IR.Type (IRType(..))
import SPLL.Typing.RType (RType(..))

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
