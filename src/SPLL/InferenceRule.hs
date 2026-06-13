{-# LANGUAGE OverloadedStrings #-}

module SPLL.InferenceRule (
  InferenceRule(..)
, ExprStub(..)
, toStub
, allAlgorithms
, checkExprMatches
) where

import Data.List (isSuffixOf)
import SPLL.Lang.Lang (toStub)
import SPLL.Typing.RType
import SPLL.Lang.Types

checkExprMatches :: Expr -> InferenceRule -> Bool
checkExprMatches e alg = toStub e == forExpression alg


-- mirror the name of a 2-arg rule (Left <-> Right). The rule now only carries an
-- ExprStub and an RType scheme, so mirroring is purely a renaming.
mirror2 :: InferenceRule -> InferenceRule
mirror2 (InferenceRule stub name rty) = InferenceRule stub (mirrorN name) rty

mirrorN :: String -> String
mirrorN name
  | "Left"  `isSuffixOf` name = take (length name - 4) name ++ "Right"
  | "Right" `isSuffixOf` name = take (length name - 5) name ++ "Left"
  | otherwise = name ++ "'"

greaterThanLeft :: InferenceRule
greaterThanLeft = InferenceRule
                    StubGreaterThan
                    "greaterThanLeft"
                    (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TBool)))

greaterThanRight :: InferenceRule
greaterThanRight = mirror2 greaterThanLeft

lessThanLeft :: InferenceRule
lessThanLeft = InferenceRule
                    StubLessThan
                    "lessThanLeft"
                    (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TBool)))

lessThanRight :: InferenceRule
lessThanRight = mirror2 lessThanLeft

greaterThanSigmoid :: InferenceRule
greaterThanSigmoid = InferenceRule
                       StubGreaterThan
                       "greaterThanSigmoid"
                       (Forall [] [] (TFloat `TArrow` (TFloat `TArrow` TBool)))

andRule :: InferenceRule
andRule = InferenceRule
        StubAnd
        "and"
        (Forall [] [] (TBool `TArrow` (TBool `TArrow` TBool)))

orRule :: InferenceRule
orRule = InferenceRule
        StubOr
        "or"
        (Forall [] [] (TBool `TArrow` (TBool `TArrow` TBool)))

injF2Left :: InferenceRule
injF2Left = InferenceRule
             StubInjF
             "injF2Left"
             (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "a"))))

injF2Right :: InferenceRule
injF2Right = mirror2 injF2Left

injF2Enumerable :: InferenceRule
injF2Enumerable = InferenceRule
             StubInjF
             "injF2Enumerable"
             (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "a"))))

injF2ResolvesToDistribution :: InferenceRule
injF2ResolvesToDistribution = InferenceRule
             StubInjF
             "injFResolvesToDistribution"
             (Forall [TV "a"] [] (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "a"))))

ifThenElse :: InferenceRule
ifThenElse = InferenceRule
               StubIfThenElse
               "ifThenElse"
               (Forall [TV "a"] [] (TBool `TArrow` (TVarR (TV "a") `TArrow` (TVarR (TV "a") `TArrow` TVarR (TV "a")))))

theta :: InferenceRule
theta = InferenceRule
          StubThetaI
          "theta"
          (Forall [] [] (TThetaTree `TArrow` TFloat))


thetaSubTree :: InferenceRule
thetaSubTree = InferenceRule
          StubSubtree
          "thetaSubTree"
          (Forall [] [] (TThetaTree `TArrow` TThetaTree))

uniform :: InferenceRule
uniform = InferenceRule
            StubUniform
            "uniform"
            (Forall [] [] TFloat)

normal :: InferenceRule
normal = InferenceRule
           StubNormal
           "normal"
           (Forall [] [] TFloat)

constant :: InferenceRule
constant = InferenceRule
             StubConstant
             "constant"
             (Forall [TV "a"] [] $ TVarR $ TV "a")

errorr :: InferenceRule
errorr = InferenceRule
            StubError
            "error"
            (Forall [TV "a"] [] (TVarR $ TV "a"))

allAlgorithms :: [InferenceRule]
allAlgorithms = [
  ifThenElse,
  theta,
  thetaSubTree,
  uniform,
  normal,
  constant,
  greaterThanLeft,
  greaterThanRight,
  lessThanLeft,
  lessThanRight,
  greaterThanSigmoid,
  andRule,
  orRule,
  injF2Left,
  injF2Right,
  injF2Enumerable,
  injF2ResolvesToDistribution,
  errorr
  ]
