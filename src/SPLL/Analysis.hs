module SPLL.Analysis (
  Tag(..)
, StaticAnnotations(..)
, annotate
) where

import SPLL.Lang
import Transpiler (Algorithm, allAlgorithms, checkExprMatches, checkConstraint, constraints, likelihoodFunctionUsesTypeInfo, toStub)
import SPLL.Typing.RType
import SPLL.Typing.PType
import Data.Maybe (maybeToList, fromJust, isNothing)
import Data.List (nub)
  
data Tag a = EnumRange (Value a, Value a)
           | EnumList [Value a]
           | Alg Algorithm
           deriving (Show)

data StaticAnnotations a = StaticAnnotations RType PType [Tag a] deriving (Show)

annotate :: (Show a) => Expr TypeInfo a -> Expr (StaticAnnotations a) a
annotate = tMap annotateLocal
  where
    annotateLocal e = StaticAnnotations rt pt tags
      where
        TypeInfo rt pt = getTypeInfo e
        tags =
          [Alg $ findAlgorithm e | likelihoodFunctionUsesTypeInfo $ toStub e]
          ++ fmap EnumList (maybeToList (findEnumerable e))

findEnumerable :: Expr TypeInfo a -> Maybe [Value a]
findEnumerable ReadNN {} = Just [VInt i | i <- [0..9]]
findEnumerable (PlusI _ left right) =
  if isNothing leftEnum || isNothing rightEnum
    then Nothing
    else Just $ map VInt $ nub [a + b | VInt a <- fromJust leftEnum, VInt b <- fromJust rightEnum]
      where
        leftEnum = findEnumerable left
        rightEnum = findEnumerable right
findEnumerable _ = Nothing

findAlgorithm :: (Show a) => Expr TypeInfo a -> Algorithm
findAlgorithm expr = case validAlgs of
  [alg] -> alg
  [] -> error ("no valid algorithms found in expr: " ++ show expr)
  (_:_:_) -> error "multiple valid algorithms found" -- TODO: There might be leeway here.
  where
    validAlgs = filter (\alg -> all (checkConstraint expr alg) (constraints alg) ) correctExpr
    correctExpr = filter (checkExprMatches expr) allAlgorithms

--2A: do static analysis to determine various statically known properties we're interested in.
--2A.1: For now, that's exclusively Enum Ranges.
--2B: using those type annotations, decide on algorithms to use. We can reuse the list of all algorithms from Transpiler.
--  Here, we still have Expr Annotation a, with Annotation being a big ol' mess.