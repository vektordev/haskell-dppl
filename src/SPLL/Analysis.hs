module SPLL.Analysis (
  annotate,
  annotateProg
) where

import SPLL.Lang.Types
import SPLL.Lang.Lang
import SPLL.InferenceRule
import SPLL.Typing.RType
import SPLL.Typing.PType
import Data.Maybe (maybeToList, fromJust, isNothing)
import Data.List (nub)
import Data.Bifunctor
import SPLL.Typing.Typing (TypeInfo, TypeInfo(..), Tag(..), setTags)


annotateProg :: (Show a) => Program a -> Program a
annotateProg p@Program {functions=f} = p{functions = map (second (annotate p)) f}

annotate :: (Show a) => Program a -> Expr a -> Expr a
annotate p = tMap annotateLocal
  where
    annotateLocal e = setTags ti tags
      where
        ti = getTypeInfo e
        tags =
          [Alg $ findAlgorithm e | likelihoodFunctionUsesTypeInfo $ toStub e]
          ++ fmap EnumList (maybeToList (findEnumerable p e))

findEnumerable :: Program a -> Expr a -> Maybe [Value a]
findEnumerable p (ReadNN _ name _) = case getNeuralDeclTag name (neurals p) of
  (EnumList l) -> return l
  (EnumRange (VInt a, VInt b)) -> return [VInt i | i <- [a..b]]
  _ -> error $ "Invalid Neural declaration for " ++ name
findEnumerable p (PlusI _ left right) =
  if isNothing leftEnum || isNothing rightEnum
    then Nothing
    else Just $ map VInt $ nub [a + b | VInt a <- fromJust leftEnum, VInt b <- fromJust rightEnum]
      where
        leftEnum = findEnumerable p left
        rightEnum = findEnumerable p right
findEnumerable p _ = Nothing

getNeuralDeclTag :: String -> [NeuralDecl a] -> Tag a
getNeuralDeclTag name ((n, _, tag):_) | n == name = tag
getNeuralDeclTag name (_:rest) = getNeuralDeclTag name rest
getNeuralDeclTag name [] = error $ "No neural declaration found for name: " ++ name

findAlgorithm :: (Show a) => Expr a -> InferenceRule
findAlgorithm expr = case validAlgs of
  [alg] -> alg
  [] -> error ("no valid algorithms found in expr: " ++ show expr)
  --(_:_:_) -> error "multiple valid algorithms found" -- TODO: There might be leeway here.
  alg:_ -> alg  --If multiple choose the first one TODO: Check if correct
  where
    validAlgs = filter (\alg -> all (checkConstraint expr alg) (constraints alg) ) correctExpr
    correctExpr = filter (checkExprMatches expr) allAlgorithms

checkConstraint :: Expr a -> InferenceRule -> RuleConstraint -> Bool
checkConstraint expr _ (SubExprNIsType n ptype) = ptype == p
  where p = pType $ getTypeInfo (getSubExprs expr !! n)
checkConstraint expr _ (SubExprNIsNotType n ptype) = ptype /= p
  where p = pType $ getTypeInfo (getSubExprs expr !! n)
checkConstraint expr alg ResultingTypeMatch = resPType == annotatedType
  where
    annotatedType = pType $ getTypeInfo expr
    resPType = resultingPType alg (map (pType . getTypeInfo) (getSubExprs expr))

likelihoodFunctionUsesTypeInfo :: ExprStub -> Bool
likelihoodFunctionUsesTypeInfo expr = expr `elem` [StubGreaterThan, StubLessThan, StubMultF, StubMultI, StubPlusF, StubPlusI, StubInjF]
--2A: do static analysis to determine various statically known properties we're interested in.
--2A.1: For now, that's exclusively Enum Ranges.
--2B: using those type annotations, decide on algorithms to use. We can reuse the list of all algorithms from Transpiler.
--  Here, we still have Expr Annotation a, with Annotation being a big ol' mess.