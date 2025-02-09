{-# LANGUAGE OverloadedStrings #-}

module SPLL.InferenceRule (
  InferenceRule(..)
, RuleConstraint(..)
, ExprStub(..)
, toStub
, allAlgorithms
, checkExprMatches
) where

import SPLL.Typing.PType hiding (TV, NotSetYet)
import Data.List (isInfixOf, isSuffixOf)
import SPLL.Lang.Lang (Expr(..), ExprStub(..), toStub)
import SPLL.Typing.RType
import SPLL.Lang.Types

checkExprMatches :: Expr -> InferenceRule -> Bool
checkExprMatches e alg = toStub e == forExpression alg


--mirror the constraints and the ptype of a 2-arg function.
mirror2 :: InferenceRule -> InferenceRule
mirror2 (InferenceRule stub constrs name pty rty) = InferenceRule stub (map mirrorC constrs) (mirrorN name) (mirrorPty pty) rty

mirrorN :: String -> String
mirrorN name
  | "Left"  `isSuffixOf` name = take (length name - 4) name ++ "Right"
  | "Right" `isSuffixOf` name = take (length name - 5) name ++ "Left"
  | otherwise = name ++ "'"

mirrorPty :: ([PType] -> PType) -> ([PType] -> PType)
mirrorPty function subexprTypes = function (reverse subexprTypes)

mirrorC :: RuleConstraint -> RuleConstraint
mirrorC ResultingTypeMatch = ResultingTypeMatch
mirrorC (SubExprNIsNotType 0 a) = SubExprNIsNotType 1 a
mirrorC (SubExprNIsNotType 1 a) = SubExprNIsNotType 0 a
mirrorC (SubExprNIsType 0 a) = SubExprNIsType 1 a
mirrorC (SubExprNIsType 1 a) = SubExprNIsType 0 a
mirrorC (SubExprNIsEnumerable 0) = SubExprNIsEnumerable 1
mirrorC (SubExprNIsEnumerable 1) = SubExprNIsEnumerable 0
mirrorC c = error ("can not mirror Constraint: " ++ show c)

greaterThanLeft :: InferenceRule
greaterThanLeft = InferenceRule
                    StubGreaterThan
                    [SubExprNIsType 0 Deterministic]
                    "greaterThanLeft"
                    (const Integrate)
                    (Forall [] (TFloat `TArrow` (TFloat `TArrow` TBool)))

greaterThanRight :: InferenceRule
greaterThanRight = mirror2 greaterThanLeft --InferenceRule StubGreaterThan [SubExprNIsType 1 Deterministic] "greaterThanRight" (const Integrate)

lessThanLeft :: InferenceRule
lessThanLeft = InferenceRule
                    StubLessThan
                    [SubExprNIsType 0 Deterministic]
                    "lessThanLeft"
                    (const Integrate)
                    (Forall [] (TFloat `TArrow` (TFloat `TArrow` TBool)))

lessThanRight :: InferenceRule
lessThanRight = mirror2 lessThanLeft

greaterThanSigmoid :: InferenceRule
greaterThanSigmoid = InferenceRule
                       StubGreaterThan
                       [SubExprNIsType 0 Deterministic, SubExprNIsType 1 Deterministic]
                       "greaterThanSigmoid"
                       (const Integrate)
                       (Forall [] (TFloat `TArrow` (TFloat `TArrow` TBool)))

--multRight = InferenceRule StubMultF [SubExprNIsType 1 Deterministic] "multRight" mostChaotic

injF2Left :: InferenceRule
injF2Left = InferenceRule
             StubInjF
             [SubExprNIsType 0 Deterministic]
             "injF2Left"
             mostChaotic
             (Forall [TV "a"] (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "a"))))
            
injF2Right :: InferenceRule
injF2Right = mirror2 injF2Left

injF2Enumerable :: InferenceRule
injF2Enumerable = InferenceRule
             StubInjF
             [SubExprNIsEnumerable 0, SubExprNIsEnumerable 1, SubExprNIsNotType 0 Deterministic, SubExprNIsNotType 1 Deterministic]
             "injF2Enumerable"
             (const Prob)
             (Forall [TV "a"] (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "a"))))

ifThenElse :: InferenceRule
ifThenElse = InferenceRule
               StubIfThenElse
               [SubExprNIsAtLeast 0 Integrate]
               "ifThenElse"
               (\[_, a, b] -> mostChaotic [a,b])
               (Forall [TV "a"] (TBool `TArrow` (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "a")))))

theta :: InferenceRule
theta = InferenceRule
          StubThetaI
          []
          "theta"
          (const Deterministic)
          (Forall [] (TThetaTree `TArrow` TFloat))


thetaSubTree :: InferenceRule
thetaSubTree = InferenceRule
          StubSubtree
          []
          "thetaSubTree"
          (const Deterministic)
          (Forall [] (TThetaTree `TArrow` TThetaTree))

uniform :: InferenceRule
uniform = InferenceRule
            StubUniform
            []
            "uniform"
            (const Integrate)
            (Forall [] TFloat)

normal :: InferenceRule
normal = InferenceRule
           StubNormal
           []
           "normal"
           (const Integrate)
           (Forall [] TFloat)

constant :: InferenceRule
constant = InferenceRule
             StubConstant
             []
             "constant"
             (const Deterministic)
             (Forall [TV "a"] $ TVarR $ TV "a")

exprNull :: InferenceRule
exprNull = InferenceRule
             StubNull
             []
             "null"
             (const Deterministic)
             (Forall [TV "a"] (ListOf $ TVarR $ TV "a"))

cons :: InferenceRule
cons = InferenceRule
         StubCons
         []
         "cons"
         (mostChaotic . (Prob:))
         (Forall [TV "a"] ((TVarR $ TV "a") `TArrow` ((ListOf $ TVarR $ TV "a") `TArrow` (ListOf $ TVarR $ TV "a"))))

tcons :: InferenceRule
tcons = InferenceRule
          StubTCons
          []
          "tcons"
          (mostChaotic . (Prob:))
          (Forall [TV "a", TV "b"] ((TVarR $ TV "a") `TArrow` ((TVarR $ TV "b") `TArrow` (Tuple (TVarR $ TV "a") (TVarR $ TV "b")))))

exprNot :: InferenceRule
exprNot = InferenceRule
            StubNot
            []
            "tcons"
            mostChaotic
            (Forall [] (TBool `TArrow` TBool))

allAlgorithms :: [InferenceRule]
allAlgorithms = [
  ifThenElse,
  theta,
  thetaSubTree,
  uniform,
  normal,
  constant,
  exprNull,
  greaterThanLeft,
  greaterThanRight,
  lessThanLeft,
  lessThanRight,
  greaterThanSigmoid,
  injF2Left, 
  injF2Right,
  injF2Enumerable,
  cons,
  tcons,
  exprNot
  ]
