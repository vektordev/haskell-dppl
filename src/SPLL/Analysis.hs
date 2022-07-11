module SPLL.Analysis (
  Tag(..)
, StaticAnnotations(..)
, annotate
) where

import SPLL.Typing.Typing
import SPLL.Lang
import Transpiler (Algorithm, allAlgorithms, checkExprMatches, checkConstraint, constraints, likelihoodFunctionUsesTypeInfo, toStub)
import SPLL.Typing.RType
import SPLL.Typing.PType
  
data Tag a = EnumRange (Value a, Value a)
           | EnumList [Value a]
           | Alg Algorithm
           deriving (Show)

data StaticAnnotations a = StaticAnnotations RType PType [Tag a] deriving (Show)

annotate :: Expr TypeInfo a -> Expr (StaticAnnotations a) a 
annotate expr = tMap annotateLocal expr
  where
    annotateLocal e = StaticAnnotations rt pt tags
      where
        TypeInfo rt pt = getTypeInfo e
        tags = if likelihoodFunctionUsesTypeInfo $ toStub e
          then [Alg $ findAlgorithm e]
          else []

findAlgorithm :: Expr TypeInfo a -> Algorithm
findAlgorithm expr = case validAlgs of
  [alg] -> alg
  [] -> error "no valid algorithms found"
  [x] -> error "multiple valid algorithms found"
  where
    validAlgs = filter (\alg -> all (checkConstraint expr alg) (constraints alg) ) correctExpr
    correctExpr = filter (checkExprMatches expr) allAlgorithms

--2A: do static analysis to determine various statically known properties we're interested in.
--2A.1: For now, that's exclusively Enum Ranges.
--2B: using those type annotations, decide on algorithms to use. We can reuse the list of all algorithms from Transpiler.
--  Here, we still have Expr Annotation a, with Annotation being a big ol' mess.