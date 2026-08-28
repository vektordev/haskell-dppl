module SPLL.Analysis (
  annotate,
  annotateEnumsProg,
  annotateConditionalProg,
  materializationDomain,
  withinMaterializationBudget
) where

import SPLL.Lang.Types
import SPLL.Lang.Lang
import Data.Maybe (maybeToList)
import Data.List (nub)
import Data.Bifunctor
import SPLL.Typing.Typing (setTags)
import PredefinedFunctions
import Utils
import SPLL.Typing.ForwardChaining (FCData, ExprInfo (LambdaInfo), findEquivalentExpression, findExprWithCN)

type TagEnv = [(String, [Tag])]

annotateEnumsProg :: Program -> Program
annotateEnumsProg p@Program {functions=f, neurals=n, adts=adtsDecls} = p{functions = finalExprEnv}
  --TODO this is really unclean. It does the the job of initializing the environment with correct tags, and also prevents infinite recursion, by only evaluating twice, but annotates the program twice
  where
    finalExprEnv = fixpoint iterateExprEnv []
    iterateExprEnv eEnv = map (second (annotate adtsDecls (neuralEnv ++ map (second $ tags . getTypeInfo) eEnv))) f
    -- Resolve "_" (MultiAuto) placeholders against the declared output/input type before
    -- this MultiValue is used for discrete-value propagation.
    -- A MultiValue with a continuous (Real) leaf has no finite enumeration; tagging it
    -- would make the enumeration machinery sum over only its discrete residue, silently
    -- dropping the continuous probability mass. Decline to tag instead, the same as a
    -- neural with no `of` annotation at all.
    neuralEnv = [(name, [DiscreteValues mv]) | (name, declType, Just rawMv) <- n,
                 let mv = resolveTag declType rawMv,
                 not (multiValueContainsContinuous mv)]
    resolveTag declType mv = maybe mv (\ty -> resolveMultiAuto adtsDecls ty mv) (neuralValueType declType)

annotate :: [ADTDecl] -> TagEnv -> Expr -> Expr
--annotate _ e | trace ((show e)) False = undefined
annotate _ env e@(Expr ti (Var n)) = case lookup n env of
  (Just tgs) -> setTypeInfo e (ti{tags=tgs})
  _ -> e
annotate _ env e@(Expr ti (ReadNN n _)) = case lookup n env of
  (Just tgs) -> setTypeInfo e (ti{tags=tgs})
  _ -> e
annotate adtsParam env e = withNewTypeInfo
  where
    oldTags = tags $ getTypeInfo e
    withNewSubExpr = case e of
      Expr _ (Apply l@(Expr _ (Lambda _ _)) v) -> do
        let annotatedV = annotate adtsParam env v
            annotatedL = annotate adtsParam env l in
              setSubExprs e [annotatedL, annotatedV]
      _ -> setSubExprs e (map (annotate adtsParam env) (getSubExprs e))
    valueTgs = discretesTags adtsParam withNewSubExpr
    newTags = valueTgs ++ oldTags
    withNewTypeInfo = setTypeInfo withNewSubExpr (setTags (getTypeInfo withNewSubExpr) newTags)

discretesTags :: [ADTDecl] -> Expr -> [Tag]
-- The continuous-leaf filter mirrors neuralEnv above: never emit a DiscreteValues
-- tag whose enumeration would be a discrete residue of a partly-continuous set.
discretesTags adtsParam e = [DiscreteValues mv | mv <- maybeToList values, not (multiValueContainsContinuous mv)]
  where
    values = case e of
      (Expr _ (Constant a)) -> Just $ MultiDiscretes [a]
      -- Comparisons (gt/lt) are Bool-valued, hence finitely enumerable regardless
      -- of whether their operands are, unlike the generic InjF case below (which
      -- requires every operand to already carry a DiscreteValues tag). Tagging
      -- them lets and/or (and any boolean InjF above them) take the
      -- discrete-enumeration path. Must come before the generic InjF case.
      (Expr _ (InjF (Named name) [_, _])) | name `elem` ["gt", "lt"] -> Just $ MultiDiscretes [VBool True, VBool False]
      (Expr _ (InjF (Named name) params)) -> do
        paramValues <- mapM getValuesFromExpr params
        let unpackedMultiVals = map multiValueToValueList paramValues
        return $ valueListToMultiValue $ nub $ propagateValues adtsParam name unpackedMultiVals
      (Expr _ (IfThenElse _ left right)) -> do
        valuesLeft <- getValuesFromExpr left
        valuesRight <- getValuesFromExpr right
        return $ unionMultiValues valuesLeft valuesRight
      _ -> Nothing

getValuesFromExpr :: Expr -> Maybe MultiValue
getValuesFromExpr e = case [mv | DiscreteValues mv <- tags $ getTypeInfo e] of
  [mv] -> Just mv
  [] -> Nothing

-- The FCData certificate is built once in 'Prelude.compile' and threaded in,
-- rather than rebuilt here (modality-split-forwardchaining).
annotateConditionalProg :: FCData -> Program -> Program
annotateConditionalProg fcData p@Program {functions=fs} = p{functions=map (Data.Bifunctor.second (tMap (tagConditional fcData p))) fs}

tagConditional :: FCData -> Program -> Expr -> TypeInfo
tagConditional fcData p (Expr ti (Lambda _ b)) = if isConditional fcData p [] b then ti{tags=IsConditional:tags ti} else ti
tagConditional fcData p e@(Expr ti (Var _)) = if isConditional fcData p [] e then ti{tags=IsConditional:tags ti} else ti
tagConditional _ _ x = getTypeInfo x

isConditional :: FCData -> Program -> [ChainName] -> Expr -> Bool
isConditional _ _ visited e | chainName (getTypeInfo e) `elem` visited = False
isConditional _ _ _ (Expr _ (IfThenElse _ _ _)) = True
isConditional _ _ _ (Expr _ (Lambda _ _)) = False
-- An application is conditional if the applied function or any argument is:
-- the enumeration fallback in toIREnumerate evaluates the whole application
-- forward, so conditionality anywhere below makes the result conditional.
-- A directly-applied lambda (as produced by `let` desugaring) is looked through
-- into its body -- the body *is* evaluated by the application, unlike a bare
-- (un-applied) lambda which is a closure value. This lets nested enumerable
-- `let`s (let c = .. in let d = .. in ..) propagate conditionality outward.
isConditional fcData p visited (Expr _ (Apply (Expr _ (Lambda _ b)) v)) = isConditional fcData p visited b || isConditional fcData p visited v
isConditional fcData p visited (Expr _ (Apply l v)) = isConditional fcData p visited l || isConditional fcData p visited v
isConditional fcData p visited (Expr (TypeInfo{chainName=cn}) (Var _)) = case findEquivalentExpression fcData cn of
  -- A named function reference resolves to its (possibly curried) lambda body. Strip
  -- the leading lambdas of a multi-argument function so the conditional inside a helper
  -- like `contrib u x = if u then x else 0` is reached, rather than stopping at the
  -- intermediate `\x -> ...` lambda.
  Just (_, LambdaInfo _ bodyCn, _) -> isConditional fcData p (cn:visited) (stripLambdas (findExprWithCN (map snd (functions p)) bodyCn))
  _ -> False
isConditional fcData p visited x = any (isConditional fcData p visited) (getSubExprs x)

-- Strip leading lambdas from a (curried) function body.
stripLambdas :: Expr -> Expr
stripLambdas (Expr _ (Lambda _ b)) = stripLambdas b
stripLambdas e = e

-- ===== Cardinality guard for marginal materialization =====
-- (task materialization-cardinality-guard, design materialized-marginals-semiring)

-- | The finite domain a node's marginal may be materialized over, or 'Nothing'
-- if it may not be -- the decidable guard that lets Tier 0 marginal
-- materialization (IRCompiler's 'materializeOperandTable') proceed WITHOUT the
-- "coarsest sufficient statistic for the downstream query" analysis the parent
-- design firewalls out: set- and bag-valued intermediates have 2^k domains, and
-- this refuses them rather than analysing them.
--
-- @bound@ is 'materializationCardinality' from the 'CompilerConfig'. The
-- predicate is cheap by construction: the domains are already computed --
-- 'annotateEnumsProg' above tags every enumerable node with a 'DiscreteValues'
-- range via 'propagateValues' -- so this reads a number already sitting in the
-- node's tags. No new analysis, no new pass.
--
-- It is TOTAL: every node gets an answer, and anything unannotated, non-finite
-- (a continuous leaf, an unresolved @_@ / type reference), or over budget
-- answers "do not materialize". Being over-conservative costs performance;
-- being wrong costs correctness silently, so every unknown resolves to
-- 'Nothing'.
--
-- LOAD-BEARING COINCIDENCE, do not let it drift: this is the SAME predicate as
-- the let-unrolling affordability condition. Tier 0 materializes a table as
-- let-bound scalar cells rather than as a runtime array (IRExpr has no dense
-- array type; 'IRIndex' is an O(n) cons-cell walk), so "the domain is small
-- enough to tabulate" and "the unrolling is affordable" are one question, not
-- two. A change to either side has to be made on both.
materializationDomain :: Int -> [Tag] -> Maybe [Value]
materializationDomain bound tgs = case [mv | DiscreteValues mv <- tgs] of
  (mv:_) | multiValueIsFinite mv
         , let vals = multiValueToValueList mv
         , withinMaterializationBudget bound (length vals) -> Just vals
  _ -> Nothing

-- | Is a cell count within the materialization budget? Split out from
-- 'materializationDomain' because the same budget also bounds the operand GRID
-- a convolution unrolls (@|D_left| * |D_right|@ compile-time pairs), which is
-- not any node's own tag but is the same "how much unrolling is affordable"
-- question -- see the note above. A non-positive @bound@ disables
-- materialization entirely, which is the off-switch differential tests use.
withinMaterializationBudget :: Int -> Int -> Bool
withinMaterializationBudget bound n = n > 0 && n <= bound
