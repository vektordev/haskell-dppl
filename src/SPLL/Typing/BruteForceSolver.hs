module SPLL.Typing.BruteForceSolver (
  addRTypeInfo
, addPTypeInfo
, forceAddTypeInfo
, runBruteForceSolver
) where

import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
import SPLL.Typing.PType
import Control.Applicative (liftA2, liftA3)
import SPLL.Typing.Infer
import SPLL.InferenceRule
import SPLL.Typing.RInfer (Scheme (..))
import Debug.Trace

import SPLL.Examples
import Data.List (groupBy)

-- what types to fill into the type info of an expression, and how deep to generate recursive types
data TypeAnnotation = P Int | R Int

runBruteForceSolver :: Expr Float -> IO ()
runBruteForceSolver expr = do
  let env = [("main", expr)]
  let prog = Program env [] expr
  let p = addEmptyTypeInfo prog
  let ntypings = length (allTypes (R 0) p)
  print ntypings
  let test = forceAddTypeInfo prog
  print test

forceAddTypeInfo :: (Show a) => Program a -> Maybe (Program a)
forceAddTypeInfo prog = addPTypeInfo =<< addRTypeInfo (addEmptyTypeInfo prog)

addRTypeInfo :: (Show a) => Program a -> Maybe (Program a)
addRTypeInfo p = case filtered of
    [x] -> Just x
    _ -> Nothing
  where filtered = filter isValidRTypingProg (allTypes (R 0) p)

--TODO Implement Tuples
getRTypes :: Int -> [RType]
getRTypes 0 = [TBool, TInt, TSymbol, TFloat]
getRTypes n =
  getRTypes 0
  ++ map ListOf (getRTypes (n-1))
  ++ [TArrow x y | x <- getRTypes (n-1), y <- getRTypes (n-1)]

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

allTypes :: TypeAnnotation ->  Program a -> [Program a]
allTypes depth (Program defs nns main) = liftA3 (Program) (allTypesDef depth defs) [nns] (allTypesExpr depth main)

allTypesDef :: TypeAnnotation -> [(a1, Expr a2)] -> [[(a1, Expr a2)]]
allTypesDef depth [] = [[]]
allTypesDef depth ((name, expr) : defs) = liftA2 (:) (map (\x -> (name, x)) (allTypesExpr depth expr)) (allTypesDef depth defs)

allTypesExpr :: TypeAnnotation -> Expr a -> [Expr a]
allTypesExpr depth def = tTraverse (replaceTypeAnnotation depth) def

replaceTypeAnnotation :: TypeAnnotation -> TypeInfo a -> [TypeInfo a]
replaceTypeAnnotation (R depth) ti = map (setRType ti) $ getRTypes depth
replaceTypeAnnotation (P depth) ti = map (setPType ti) $ getPTypes depth

isValidRTypingProg :: (Show a) => Program a -> Bool
isValidRTypingProg (Program defs _ main) = isValidRTypingE main && all (isValidRTypingE . snd) defs

isValidRTypingE :: (Show a) => Expr a -> Bool
isValidRTypingE expr = matchingAlgs /= [] && all isValidRTypingE (getSubExprs expr)
  where
    plausibleAlgs = filter (checkExprMatches expr) allAlgorithms
    matchingAlgs = filter (\alg -> rTypeMatch (assumedRType alg) expr) plausibleAlgs

isConsistent :: [(TVarR, RType)] -> [TVarR] -> Bool
isConsistent substitutions _ =
  all grpIsEqual groups
    where
      groups = map (map snd) $ groupBy (\a b -> fst a == fst b) substitutions
      grpIsEqual (item:grprest) = all (item==) grprest

rTypeMatch :: (Show a) => Scheme -> Expr a -> Bool
rTypeMatch (Forall vars rty) expr = result && isConsistent subst vars
  where 
    (subst, result) = matchCombine (map (rType . getTypeInfo) (getSubExprs expr) ++ [rType (getTypeInfo expr)]) rty


--first arg is a completely grounded list of types. second could contain TVars that should be accepted into Substitution.
matchCombine :: [RType] -> RType -> ([(TVarR, RType)], Bool)
matchCombine (ty:tys) (TArrow t1 t2) = (substitutions ++ tailsubst, tyMatch && tailresult)
  where
    substitutions = case t1 of
                      TVarR x -> [(x, ty)]
                      _ -> []
    tyMatch = if null substitutions then ty == t1 else True
    (tailsubst, tailresult) = matchCombine tys t2
matchCombine [ty] t1 = (substitutions, tyMatch)
  where
    substitutions = case t1 of
                      TVarR x -> [(x, ty)]
                      _ -> []
    tyMatch = if null substitutions then ty == t1 else True
matchCombine a b = error ("unexpected error in MatchCombine" ++ show a ++ show b)

isValidPTypingProg :: (Show a) => Program a -> Bool
isValidPTypingProg (Program defs _ main) = isValidPTypingE main && all (isValidPTypingE . snd) defs

isValidPTypingE :: Expr a -> Bool
--isValidPTypingE (Uniform (TypeInfo a b)) = b == Integrate
isValidPTypingE expr = matchingAlgs /= [] && all isValidPTypingE (getSubExprs expr)
  where
    plausibleAlgs = filter (checkExprMatches expr) allAlgorithms
    matchingAlgs = filter (\alg -> applyAlg alg expr == pType (getTypeInfo expr)) plausibleAlgs

applyAlg :: InferenceRule -> Expr a -> PType
applyAlg alg expr = resultingPType alg (map (pType . getTypeInfo) $ getSubExprs expr)

addPTypeInfo :: (Show a) => Program a -> Maybe (Program a)
--addPTypeInfo p = head $ filter isValidPTypingProg (allTypes (P 2) p)
addPTypeInfo p = case filtered of
    [x] -> Just x
    _ -> Nothing
  where filtered = filter isValidPTypingProg (allTypes (P 0) p)

getPTypes :: Int -> [PType]
getPTypes 0 = [Deterministic, Integrate, Prob, Bottom]
getPTypes n =
  getPTypes 0
  ++ [PArr x y | x <- getPTypes (n-1), y <- getPTypes (n-1)]
