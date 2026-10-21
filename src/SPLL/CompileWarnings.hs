-- | Compile-time warnings: diagnostics about a program that compiles, which
-- never change the compiled result and never block compilation.
--
-- This module is the channel's vocabulary: the 'CompileWarning' type, its
-- rendering, and the pure analyses behind the warnings. Computing a program's
-- warnings (which needs the front end, and for some warnings the compiled
-- 'SPLL.IntermediateRepresentation.IREnv') is "SPLL.Prelude"'s
-- 'SPLL.Prelude.programWarnings' / 'SPLL.Prelude.compiledWarnings' /
-- 'SPLL.Prelude.compileWarnings'. The CLI prints them on stderr; library
-- callers read them as values.
--
-- A new warning is a new constructor here, a line in 'renderCompileWarning',
-- and a producer in one of the Prelude functions: in 'programWarnings' when it
-- reads only the program, in 'compiledWarnings' when it has to know what the
-- compile emitted.
module SPLL.CompileWarnings
  ( CompileWarning(..)
  , CorrelatedClass(..)
  , ChartClass(..)
  , warningFunction
  , renderCompileWarning
  , correlatedWriteLogitsClasses
  , planLeafSlot
  , chartDependentClasses
  ) where

import SPLL.Lang.Types
import SPLL.Lang.Lang (getTypeInfo, getSubExprs)
import SPLL.Typing.RType (RType(..))
import SPLL.Typing.ForwardChaining (FCData, witnessPath, untag)
import SPLL.ReservedNames (uniformName, normalName, isFrontendBinder)
import SPLL.ObservationMask
import SPLL.MaskVariants (overBudgetNote)
import SPLL.AutoNeural (PartitionPlan(..))

import Data.List (intercalate)
import Data.Maybe (isJust, listToMaybe)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set

-- | One compile-time warning. Every warning concerns one top-level function.
data CompileWarning
  = MarginalSlotsOverBudget String Int Int
    -- ^ The function, its number of enumerated observation slots, and the
    -- @--marginalSlots@ budget it exceeds: it gets no per-mask variants (task
    -- per-mask-variants-by-pruning).
  | CorrelatedWriteLogitsSlots String [CorrelatedClass]
    -- ^ The function's writeLogits encodes these groups of slots
    -- independently although each group shares a random variable: the logit
    -- vector holds the product of the slots' marginals, not their joint (task
    -- warn-correlated-slots). One entry per correlation class.
  | ChartDependentDensity String [ChartClass]
    -- ^ The function's result has groups of @Float@ slots that depend on
    -- fewer continuous draws than there are slots, so their support is a
    -- lower-dimensional set (a curve in the plane, ...). The density a
    -- probability query reports there is the draws' density in the chart of
    -- the slots they are recovered through, not the density with respect to
    -- the support's Hausdorff measure, and so depends on how the program is
    -- written (task warn-chart-dependent-cov-factor). One entry per group.
  deriving (Eq, Show)

-- | A group of writeLogits slots that are correlated, and why.
data CorrelatedClass = CorrelatedClass
  { ccSlots   :: [String]
    -- ^ The slots, as accessor chains (@fst@, @snd.fst@, an ADT field name),
    -- in output order. Each is one leaf of the writeLogits 'PartitionPlan'.
  , ccLatents :: [String]
    -- ^ The variables the shared draws are bound to (see 'slotLatentNames'),
    -- sorted; empty only when every shared draw is unnamed.
  } deriving (Eq, Show)

-- | A group of @Float@ slots whose support is lower-dimensional than the group.
data ChartClass = ChartClass
  { chSlots     :: [String]
    -- ^ The slots, as accessor chains, in output order.
  , chDraws     :: Int
    -- ^ How many continuous draws they depend on: fewer than 'chSlots', and an
    -- upper bound on the support's dimension.
  , chLatents   :: [String]
    -- ^ The variables those draws are bound to, sorted; unnamed draws omitted.
  , chWitnesses :: [(String, String)]
    -- ^ For each named draw whose recovery forward chaining can trace, the
    -- slot whose coordinate its density is taken in ('witnessPath').
  } deriving (Eq, Show)

-- | The top-level function a warning is about.
warningFunction :: CompileWarning -> String
warningFunction (MarginalSlotsOverBudget f _ _)  = f
warningFunction (CorrelatedWriteLogitsSlots f _) = f
warningFunction (ChartDependentDensity f _)      = f

-- | The one-paragraph text a warning prints as, prefixed @Warning: @.
renderCompileWarning :: CompileWarning -> String
renderCompileWarning w = "Warning: " ++ case w of
  MarginalSlotsOverBudget f k budget -> overBudgetNote f k budget
  CorrelatedWriteLogitsSlots f classes ->
    "the writeLogits of '" ++ f ++ "' encodes its slots independently, but "
    ++ intercalate "; and " (map clause classes)
    ++ ". The logit vector holds the product of those slots' marginals, not their joint "
    ++ "distribution: the correlation is discarded. Compiled anyway."
  ChartDependentDensity f classes ->
    "the probability density of '" ++ f ++ "' depends on how the program is written: "
    ++ intercalate "; and " (map chartClause classes)
    ++ ". The density reported there is each draw's density in the coordinate of the slot it is "
    ++ "recovered through, with that slot's change-of-variables factor; the other slots only "
    ++ "contribute a consistency check. It is not the density with respect to the support's "
    ++ "Hausdorff measure, so an equivalent program with those slots reordered or rescaled reports "
    ++ "a different number. A cumulative query, the probability of a set, carries no such factor. "
    ++ "Compiled anyway."
  where
    chartClause (ChartClass slots k latents witnesses) =
      "slots " ++ intercalate ", " slots ++ " depend on only " ++ show k
      ++ " continuous draw" ++ (if k == 1 then "" else "s")
      ++ (if null latents then "" else " (" ++ intercalate ", " [ "'" ++ l ++ "'" | l <- latents ] ++ ")")
      ++ ", so their support is at most " ++ show k ++ "-dimensional in "
      ++ show (length slots) ++ " coordinates"
      ++ concat [ " ('" ++ l ++ "' is recovered through slot " ++ s ++ ")" | (l, s) <- witnesses ]
    clause (CorrelatedClass slots latents) =
      "slots " ++ intercalate ", " slots ++ " read "
      ++ case latents of
           []  -> "a shared random draw"
           [l] -> "the same random draw (bound to '" ++ l ++ "')"
           ls  -> "shared random draws (bound to " ++ intercalate ", " [ "'" ++ l ++ "'" | l <- ls ] ++ ")"

-- | The correlation classes, of two or more writeLogits slots each, of one
-- top-level function whose writeLogits is laid out by @plan@.
--
-- The latent walk is the observation-mask analysis's ('slotLatentNames',
-- 'correlationClasses'), on the function's observation tree. One refinement:
-- writeLogits encodes each /plan leaf/ as one joint group (a @Discretes@ leaf
-- annotated over a whole tuple is one softmax), so observation slots are first
-- coarsened to the plan leaf holding them ('planLeafSlot') and only a
-- correlation /across/ plan leaves is reported. Name-based, as the analysis
-- is: one @let@-bound draw read twice is flagged, two syntactic draws are not.
--
-- A function whose body is not a constructor application has a single slot
-- and is never reported, even when its value is a tuple: the warning fires
-- only where the correlation is statically visible in the observation tree.
correlatedWriteLogitsClasses :: [ADTDecl] -> [FnDecl] -> PartitionPlan -> FnDecl -> [CorrelatedClass]
correlatedWriteLogitsClasses decls fenv plan decl =
  [ CorrelatedClass (map (prettySlot decls) cls)
                    (sharedLatentNames [ latentsAt s | s <- cls ])
  | cls <- correlationClasses [ (s, Map.keysSet ls) | (s, ls) <- coarse ]
  , length cls > 1 ]
  where
    coarse = mergeBy (planLeafSlot plan) (slotLatentNames decls fenv (observationTree decls decl))
    latentsAt s = Map.findWithDefault Map.empty s (Map.fromList coarse)

-- | Group slots by a key, in order of the key's first appearance, merging
-- their latent maps.
mergeBy :: (Slot -> Slot) -> [(Slot, Map Latent (Set String))] -> [(Slot, Map Latent (Set String))]
mergeBy key = foldl step []
  where
    step acc (s, ls) = case lookup k acc of
      Just old -> [ if k' == k then (k', Map.unionWith Set.union old ls) else e | e@(k', _) <- acc ]
      Nothing  -> acc ++ [(k, ls)]
      where k = key s

-- | The prefix of an observation slot that names the writeLogits plan leaf
-- holding it: descend the plan along the slot's accessors, stopping at a
-- @Discretes@ or @Continuous@ leaf (whose inside is encoded jointly). An
-- accessor the plan has no child for also stops the descent, which merges
-- rather than splits slots, so an unexpected shape can only suppress a
-- warning, never invent one.
planLeafSlot :: PartitionPlan -> Slot -> Slot
planLeafSlot _ [] = []
planLeafSlot plan (a@(Accessor c i) : rest) = case child of
  Just p  -> a : planLeafSlot p rest
  Nothing -> []
  where
    child = case plan of
      TuplePlan l r | c == "TCons" -> pick [l, r]
      EitherPlan l _ | c == "left"  && i == 0 -> Just l
      EitherPlan _ r | c == "right" && i == 0 -> Just r
      ADTPlan _ ctors -> lookup c ctors >>= pick
      _ -> Nothing
    pick ps
      | i >= 0 && i < length ps = Just (ps !! i)
      | otherwise               = Nothing

-- | The groups of @Float@ slots of one top-level function whose support is
-- lower-dimensional than the group: each a correlation class of two or more
-- @Float@ leaf slots that, between them, depend on fewer continuous draws than
-- there are slots.
--
-- There a reported density carries a chart's change-of-variables factor, not
-- the Hausdorff one: forward chaining recovers each draw through one slot and
-- the others are paid for by the dim-0 consistency indicator, so the speed of
-- the support in the other coordinates is never accounted for. When the group
-- has as many draws as slots the support is full-dimensional, and the chained
-- factor is the Hausdorff one (design tensors-in-core-language §4.4).
--
-- Dependence is /continuous/ dependence ('continuousLatents'): a slot reading
-- a draw only through a comparison, an integer, or an @if@ condition does not
-- count, so @(x, if x > 0.5 then 1.0 else 2.0)@ (piecewise an isometric
-- embedding) is not reported. Counting draws is an upper bound on the
-- support's dimension, so a group with as many draws as slots whose map is
-- nonetheless rank-deficient (@(x + y, x + y)@) is missed; a group reading a
-- neural output or a drawing top-level function, whose dimension is unknown
-- here, is skipped. Both err towards silence.
--
-- @fc@ is the program's forward-chaining data, read only to name the slot
-- each draw is recovered through; it is not forced for a function with no
-- such group.
chartDependentClasses :: [ADTDecl] -> [FnDecl] -> FCData -> FnDecl -> [ChartClass]
chartDependentClasses decls fenv fc decl@(_, body) = case tree of
  ObsLeaf{} -> []
  ObsCon{}  -> [ c | cls <- correlationClasses [ (s, Map.keysSet ls) | (s, ls) <- floats ]
                   , Just c <- [classify cls] ]
  where
    tree   = observationTree decls decl
    floats = [ (s, continuousLatents decls fenv env [] Nothing e)
             | (s, e, env) <- obsLeaves tree, rType (getTypeInfo e) == TFloat ]
    primitiveDraws = Set.fromList
      [ chainName (getTypeInfo e) | e <- universeExpr body, isPrimitiveDraw e ]
    primitive (LDist cn) = cn `Set.member` primitiveDraws
    primitive LNeural{}  = False
    classify cls
      | length cls < 2                     = Nothing
      | not (all primitive (Map.keys ls))  = Nothing
      | length cls <= Map.size ls          = Nothing
      | otherwise = Just ChartClass
          { chSlots     = map (prettySlot decls) cls
          , chDraws     = Map.size ls
          , chLatents   = Set.toList (Set.unions (Map.elems ls))
          , chWitnesses =
              [ (n, prettySlot decls s)
              | (LDist cn, ns) <- Map.toList ls
              , Just n <- [listToMaybe (Set.toList ns)]
              , Just s <- [binderOfValueWith cn >>= witnessSlot] ]
          }
      where ls = Map.unionsWith Set.union [ m | (s, m) <- floats, s `elem` cls ]
    -- The first slot (in tree order) on the recovery path of the variable a
    -- lambda binds. Through a chain of bindings (@draw y = x in (y, y * 2.0)@)
    -- the path runs through the outer binding's slot as well.
    witnessSlot lamCN = do
      path <- Set.fromList . map untag <$> witnessPath fc lamCN
      listToMaybe [ s | (s, root) <- leafRoots, root `Set.member` path ]
    leafRoots = [ (s, chainName (getTypeInfo e)) | (s, e, _) <- obsLeaves tree ]
    -- The chain name of the innermost lambda whose @let@ value contains @cn@.
    binderOfValueWith cn = listToMaybe
      [ chainName lti
      | Expr _ (Apply (Expr lti (Lambda _ _)) v) <- reverse (universeExpr body)
      , cn `elem` subtreeChainNames v ]

-- | Every node of an expression, preorder.
universeExpr :: Expr -> [Expr]
universeExpr e = e : concatMap universeExpr (getSubExprs e)

subtreeChainNames :: Expr -> [ChainName]
subtreeChainNames = map (chainName . getTypeInfo) . universeExpr

isPrimitiveDraw :: Expr -> Bool
isPrimitiveDraw (Expr _ (Var v)) = v == uniformName || v == normalName
isPrimitiveDraw _                = False

-- | The latents an expression depends on /continuously/: 'namedLatentsOf',
-- except that the walk stops at a node of a discrete type (a comparison, an
-- integer) and does not descend into an @if@ condition. A draw read only
-- through those moves the value in jumps, if at all, and adds no dimension to
-- the expression's support.
continuousLatents :: [ADTDecl] -> [FnDecl] -> LetEnv -> [String] -> Maybe String -> Expr
                  -> Map Latent (Set String)
continuousLatents decls fenv env seen via e
  | discrete (rType (getTypeInfo e)) = Map.empty
  | otherwise = case node e of
      IfThenElse _ t f -> Map.unionWith Set.union (descend t) (descend f)
      Var x
        | x `elem` seen -> Map.empty
        | Just b <- lookupBinding x env ->
            let via' = if isFrontendBinder x && isJust via then via else Just x
            in continuousLatents decls fenv (bndEnv b) (x : seen) via' (bndValue b)
      Var _    -> namedLatentsOf decls fenv env seen via e
      ReadNN{} -> namedLatentsOf decls fenv env seen via e
      _        -> Map.unionsWith Set.union (map descend (getSubExprs e))
  where
    descend = continuousLatents decls fenv env seen via
    discrete t = t `elem` [TBool, TInt, TSymbol]
