module SPLL.Analysis (
  annotate,
  annotateEnumsProg,
  annotateConditionalProg
) where

import SPLL.Lang.Types
import SPLL.Lang.Lang
import Data.Maybe (maybeToList, listToMaybe)
import Data.List (nub)
import Data.Bifunctor
import SPLL.Typing.Typing (setTags)
import PredefinedFunctions
import Utils
import SPLL.Typing.ForwardChaining (FCData, ExprInfo (LambdaInfo), findEquivalentExpression, findExprWithCN, progToFCData)

type TagEnv = [(String, [Tag])]

annotateEnumsProg :: Program -> Program
annotateEnumsProg p@Program {functions=f, neurals=n, adts=adts} = p{functions = finalExprEnv}
  --TODO this is really unclean. It does the the job of initializing the environment with correct tags, and also prevents infinite recursion, by only evaluating twice, but annotates the program twice
  where
    finalExprEnv = fixpoint iterateExprEnv []
    iterateExprEnv eEnv = map (second (annotate adts (neuralEnv ++ map (second $ tags . getTypeInfo) eEnv))) f
    -- Resolve "_" (MultiAuto) placeholders against the declared output/input type before
    -- this MultiValue is used for discrete-value propagation.
    neuralEnv = [(name, [DiscreteValues (resolveTag declType mv)]) | (name, declType, Just mv) <- n]
    resolveTag declType mv = maybe mv (\ty -> resolveMultiAuto adts ty mv) (neuralValueType declType)

annotate :: [ADTDecl] -> TagEnv -> Expr -> Expr
--annotate _ e | trace ((show e)) False = undefined
annotate _ env e@(Var ti n) = case lookup n env of
  (Just tgs) -> setTypeInfo e (ti{tags=tgs})
  _ -> e
annotate _ env e@(ReadNN ti n _) = case lookup n env of
  (Just tgs) -> setTypeInfo e (ti{tags=tgs})
  _ -> e
annotate adts env e = withNewTypeInfo
  where
    oldTags = tags $ getTypeInfo e
    withNewSubExpr = case e of
      Apply _ l@(Lambda _ _ _) v -> do
        let annotatedV = annotate adts env v
            annotatedL = annotate adts env l in
              setSubExprs e [annotatedL, annotatedV]
      _ -> setSubExprs e (map (annotate adts env) (getSubExprs e))
    valueTgs = discretesTags adts withNewSubExpr
    newTags = valueTgs ++ oldTags
    withNewTypeInfo = setTypeInfo withNewSubExpr (setTags (getTypeInfo withNewSubExpr) newTags)

discretesTags :: [ADTDecl] -> Expr -> [Tag]
discretesTags adts e = maybeToList valuesTag
  where
    valuesTag = fmap DiscreteValues values
    values = case e of
      (Constant _ a) -> Just $ MultiDiscretes [a]
      (InjF _ (Named name) params) -> do
        paramValues <- mapM getValuesFromExpr params
        let unpackedMultiVals = map multiValueToValueList paramValues
        return $ valueListToMultiValue $ nub $ propagateValues adts name unpackedMultiVals
      (IfThenElse _ _ left right) -> do
        valuesLeft <- getValuesFromExpr left
        valuesRight <- getValuesFromExpr right
        return $ unionMultiValues valuesLeft valuesRight
      _ -> Nothing

getSingleDiscrete :: Expr -> Maybe Double
getSingleDiscrete e = listToMaybe [x | DiscreteValues (MultiDiscretes [VFloat x]) <- tags (getTypeInfo e)]

getValuesFromExpr :: Expr -> Maybe MultiValue
getValuesFromExpr e = case [mv | DiscreteValues mv <- tags $ getTypeInfo e] of
  [mv] -> Just mv
  [] -> Nothing

isRecursive :: String -> Expr -> Bool
isRecursive name (Var _ n) | name == n = True
isRecursive n e = any (isRecursive n) (getSubExprs e)

annotateConditionalProg :: Program -> Program
annotateConditionalProg p@Program {functions=fs} = p{functions=map (Data.Bifunctor.second (tMap (tagConditional (progToFCData p) p))) fs}

tagConditional :: FCData -> Program -> Expr -> TypeInfo
tagConditional fcData p (Lambda ti _ b) = if isConditional fcData p [] b then ti{tags=IsConditional:tags ti} else ti
tagConditional fcData p e@(Var ti _) = if isConditional fcData p [] e then ti{tags=IsConditional:tags ti} else ti
tagConditional _ _ x = getTypeInfo x

isConditional :: FCData -> Program -> [ChainName] -> Expr -> Bool
isConditional _ _ visited e | chainName (getTypeInfo e) `elem` visited = False
isConditional _ _ _ (IfThenElse _ _ _ _) = True
isConditional _ _ _ (Lambda _ _ _) = False
-- An application is conditional if the applied function or any argument is:
-- the enumeration fallback in toIREnumerate evaluates the whole application
-- forward, so conditionality anywhere below makes the result conditional.
isConditional fcData p visited (Apply _ l v) = isConditional fcData p visited l || isConditional fcData p visited v
isConditional fcData p visited (Var (TypeInfo{chainName=cn}) _) = case findEquivalentExpression fcData cn of
  Just (_, LambdaInfo _ bodyCn, _) -> isConditional fcData p (cn:visited) (findExprWithCN (map snd (functions p)) bodyCn)
  _ -> False
isConditional fcData p visited x = any (isConditional fcData p visited) (getSubExprs x)