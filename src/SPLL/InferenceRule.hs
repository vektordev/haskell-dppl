module SPLL.InferenceRule (
  InferenceRule(..)
, Constraint(..)
, ExprStub(..)
, allAlgorithms
) where

import SPLL.Typing.PType
  

data ExprStub = StubIfThenElse
              | StubGreaterThan
              | StubThetaI
              | StubUniform
              | StubNormal
              | StubConstant
              | StubMultF
              | StubMultI
              | StubPlusF
              | StubPlusI
              | StubNull
              | StubCons
              | StubCall
              | StubVar
              | StubLetIn
              | StubArg
              | StubCallArg
              | StubLambda
              | StubReadNN
              deriving (Show, Eq)

data Constraint = SubExprNIsType Int PType
                | SubExprNIsNotType Int PType
                | ResultingTypeMatch
                deriving Show


-- can we encode symmetries?
data InferenceRule = InferenceRule { forExpression :: ExprStub
                           , constraints :: [Constraint]
                           , algName :: String
                           --apply all subexpr PTypes to find PType
                           , resultingType :: [PType] -> PType
                           }

instance Show InferenceRule where
  show (InferenceRule _ _ name _ ) = name
  
instance Eq InferenceRule where
  a1 == a2 = algName a1 == algName a2

greaterThanLeft :: InferenceRule
greaterThanLeft = InferenceRule StubGreaterThan [SubExprNIsType 0 Deterministic] "greaterThanLeft" (const Integrate)

greaterThanRight :: InferenceRule
greaterThanRight = InferenceRule StubGreaterThan [SubExprNIsType 1 Deterministic] "greaterThanRight" (const Integrate)

greaterThanSigmoid :: InferenceRule
greaterThanSigmoid = InferenceRule StubGreaterThan [SubExprNIsType 0 Deterministic, SubExprNIsType 1 Deterministic] "greaterThanSigmoid" (const Integrate)

--TODO: Lacking implementation of invertible arithmetic on Integers.
plusLeft :: InferenceRule
plusLeft = InferenceRule StubPlusF [SubExprNIsType 0 Deterministic] "plusLeft" mostChaotic

plusRight :: InferenceRule
plusRight = InferenceRule StubPlusF [SubExprNIsType 1 Deterministic] "plusRight" mostChaotic

multLeft :: InferenceRule
multLeft = InferenceRule StubMultF [SubExprNIsType 0 Deterministic] "multLeft" mostChaotic

multRight :: InferenceRule
multRight = InferenceRule StubMultF [SubExprNIsType 1 Deterministic] "multRight" mostChaotic

enumeratePlusLeft :: InferenceRule
enumeratePlusLeft = InferenceRule StubPlusI [SubExprNIsNotType 0 Deterministic, SubExprNIsNotType 1 Deterministic] "enumeratePlusLeft" (const Chaos)

allAlgorithms :: [InferenceRule]
allAlgorithms = [greaterThanLeft, greaterThanRight, greaterThanSigmoid, plusLeft, plusRight, multLeft, multRight, enumeratePlusLeft]
