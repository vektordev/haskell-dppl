module SPLL.Typing.BruteForceSolver (
  addRTypeInfo,
  addPTypeInfo
) where

import SPLL.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import Control.Applicative (liftA2)
import SPLL.Typing.Infer

import SPLL.Examples

data TypeAnnotation = P Int | R Int

addRTypeInfo :: Program TypeInfo a -> Program TypeInfo a
--TODO: Assert that the solution is unique.
addRTypeInfo p = head $ filter isValidRTypingProg (allTypes (R 2) p)

getRTypes :: Int -> [RType]
getRTypes 0 = [TBool, TInt, TSymbol, TFloat, Tuple []]
getRTypes n =
  getRTypes 0
  ++ map ListOf (getRTypes (n-1))
  ++ [TArrow x y | x <- getRTypes (n-1), y <- getRTypes (n-1)]
  ++ map Tuple (concat [mkTupleType x x | x <- [0..(n-2)]])

--Note: the above generates a few duplicates:
-- [(x, length $ getRTypes x, length $ nubOrd $ getRTypes x) | x <- [1..]]
-- [(1,35,35),(2,1266,1265),(3,1604033,1601500),...]
-- Either fix that, or check valid redundant typings for identity.

mkTupleType :: Int -> Int -> [[RType]]
mkTupleType _ 0 = [[]]
mkTupleType 0 _ = []
mkTupleType depth 1 = liftA2 (:) fillerList [[]]
    where fillerList = getRTypes (depth - 1)
mkTupleType depth len =
  liftA2 (:) fillerList prevresult
    where
      prevresult = mkTupleType depth (len - 1)
      fillerList = getRTypes (depth - 1)

allTypes :: TypeAnnotation ->  Program TypeInfo a -> [Program TypeInfo a]
allTypes depth (Program defs main) = liftA2 (Program) (allTypesDef depth defs) (allTypesExpr depth main)

allTypesDef :: TypeAnnotation -> [(a1, Expr TypeInfo a2)] -> [[(a1, Expr TypeInfo a2)]]
allTypesDef depth [] = [[]]
allTypesDef depth ((name, expr) : defs) = liftA2 (:) (map (\x -> (name, x)) (allTypesExpr depth expr)) (allTypesDef depth defs)

allTypesExpr :: TypeAnnotation -> Expr TypeInfo a -> [Expr TypeInfo a]
allTypesExpr depth def = map unflip $ traverse (replaceTypeAnnotation depth) (ExprFlip def)

replaceTypeAnnotation :: TypeAnnotation -> TypeInfo -> [TypeInfo]
replaceTypeAnnotation (R depth) ti = map (setRType ti) $ getRTypes depth
replaceTypeAnnotation (P depth) ti = map (setPType ti) $ getPTypes depth

isValidRTypingProg :: Program TypeInfo a -> Bool
isValidRTypingProg (Program defs main) = isValidRTypingE main && all (isValidRTypingE . snd) defs

isValidRTypingE :: Expr TypeInfo a -> Bool
isValidRTypingE (Uniform (TypeInfo a b)) = a == TFloat

isValidPTypingProg :: Program TypeInfo a -> Bool
isValidPTypingProg (Program defs main) = isValidRTypingE main && all (isValidRTypingE . snd) defs

isValidPTypingE :: Expr TypeInfo a -> Bool
isValidPTypingE (Uniform (TypeInfo a b)) = b == Integrate

addPTypeInfo :: Program TypeInfo a -> Program TypeInfo a
addPTypeInfo p = head $ filter isValidPTypingProg (allTypes (P 2) p)

getPTypes :: Int -> [PType]
getPTypes 0 = [Deterministic, Integrate, Prob, Bottom]
getPTypes n =
  getPTypes 0
  ++ [PArr x y | x <- getPTypes (n-1), y <- getPTypes (n-1)]
