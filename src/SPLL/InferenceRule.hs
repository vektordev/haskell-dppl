{-# LANGUAGE OverloadedStrings #-}

module SPLL.InferenceRule (
  InferenceRule(..)
, Constraint(..)
, ExprStub(..)
, toStub
, allAlgorithms
) where

import SPLL.Typing.PType
import Data.List (isInfixOf, isSuffixOf)
import SPLL.Lang (Expr(..))

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

toStub :: Expr x a -> ExprStub
toStub expr = case expr of
  IfThenElse {}  -> StubIfThenElse
  GreaterThan {} -> StubGreaterThan
  (ThetaI _ _)   -> StubThetaI
  (Uniform _)    -> StubUniform
  (Normal _)     -> StubNormal
  (Constant _ _) -> StubConstant
  MultF {}       -> StubMultF
  MultI {}       -> StubMultI
  PlusF {}       -> StubPlusF
  PlusI {}       -> StubPlusI
  (Null _)       -> StubNull
  Cons {}        -> StubCons
  (Call _ _)     -> StubCall
  (Var _ _)      -> StubVar
  LetIn {}       -> StubLetIn
  Arg {}         -> StubArg
  CallArg {}     -> StubCallArg
  Lambda {}      -> StubLambda
  (ReadNN _ _ _) -> StubReadNN

data Constraint = SubExprNIsType Int PType
                | SubExprNIsNotType Int PType
                | SubExprNIsAtLeast Int PType
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

mirror2 :: InferenceRule -> InferenceRule
mirror2 (InferenceRule stub constrs name pty) = InferenceRule stub (map mirrorC constrs) (mirrorN name) (mirrorPty pty)

mirrorN :: String -> String
mirrorN name
  | "Left"  `isSuffixOf` name = take (length name - 4) name ++ "Right"
  | "Right" `isSuffixOf` name = take (length name - 5) name ++ "Left"
  | otherwise = name ++ "'"

mirrorPty :: ([PType] -> PType) -> ([PType] -> PType)
mirrorPty function subexprTypes = function (reverse subexprTypes)

mirrorC :: Constraint -> Constraint
mirrorC ResultingTypeMatch = ResultingTypeMatch
mirrorC (SubExprNIsNotType 0 a) = SubExprNIsNotType 1 a
mirrorC (SubExprNIsNotType 1 a) = SubExprNIsNotType 0 a
mirrorC (SubExprNIsType 0 a) = SubExprNIsType 1 a
mirrorC (SubExprNIsType 1 a) = SubExprNIsType 0 a
mirrorC c = error ("can not mirror Constraint: " ++ show c)

greaterThanLeft :: InferenceRule
greaterThanLeft = InferenceRule StubGreaterThan [SubExprNIsType 0 Deterministic] "greaterThanLeft" (const Integrate)

greaterThanRight :: InferenceRule
greaterThanRight = mirror2 greaterThanLeft --InferenceRule StubGreaterThan [SubExprNIsType 1 Deterministic] "greaterThanRight" (const Integrate)

greaterThanSigmoid :: InferenceRule
greaterThanSigmoid = InferenceRule StubGreaterThan [SubExprNIsType 0 Deterministic, SubExprNIsType 1 Deterministic] "greaterThanSigmoid" (const Integrate)

--TODO: Lacking implementation of invertible arithmetic on Integers.
plusLeft :: InferenceRule
plusLeft = InferenceRule StubPlusF [SubExprNIsType 0 Deterministic] "plusLeft" mostChaotic

plusRight :: InferenceRule
plusRight = mirror2 plusLeft
-- = InferenceRule StubPlusF [SubExprNIsType 1 Deterministic] "plusRight" mostChaotic

multLeft :: InferenceRule
multLeft = InferenceRule StubMultF [SubExprNIsType 0 Deterministic] "multLeft" mostChaotic

multRight :: InferenceRule
multRight = mirror2 multLeft
--multRight = InferenceRule StubMultF [SubExprNIsType 1 Deterministic] "multRight" mostChaotic

enumeratePlusLeft :: InferenceRule
--TODO: Introduce a new type for intractable results? Does that expand the lattice into a 2d configuration?
enumeratePlusLeft = InferenceRule StubPlusI [SubExprNIsNotType 0 Deterministic, SubExprNIsNotType 1 Deterministic] "enumeratePlusLeft" (const Prob)

ifThenElse :: InferenceRule
ifThenElse = InferenceRule StubIfThenElse [SubExprNIsAtLeast 0 Integrate] "ifThenElse" (\[_, a, b] -> mostChaotic [a,b])

theta :: InferenceRule
theta = InferenceRule StubThetaI [] "theta" (const Deterministic)

uniform :: InferenceRule
uniform = InferenceRule StubUniform [] "uniform" (const Integrate)

normal :: InferenceRule
normal = InferenceRule StubNormal [] "normal" (const Integrate)

constant :: InferenceRule
constant = InferenceRule StubConstant [] "constant" (const Deterministic)

exprNull :: InferenceRule
exprNull = InferenceRule StubNull [] "null" (const Deterministic)

cons :: InferenceRule
cons = InferenceRule StubCons [] "cons" (mostChaotic . (Prob:))

allAlgorithms :: [InferenceRule]
allAlgorithms = [ifThenElse, theta, uniform, normal, constant, exprNull, greaterThanLeft, greaterThanRight, greaterThanSigmoid, plusLeft, plusRight, multLeft, multRight, enumeratePlusLeft]
