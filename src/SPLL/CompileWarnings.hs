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
  , warningFunction
  , renderCompileWarning
  , correlatedWriteLogitsClasses
  , planLeafSlot
  ) where

import SPLL.Lang.Types (ADTDecl, FnDecl)
import SPLL.ObservationMask
import SPLL.MaskVariants (overBudgetNote)
import SPLL.AutoNeural (PartitionPlan(..))

import Data.List (intercalate)
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

-- | The top-level function a warning is about.
warningFunction :: CompileWarning -> String
warningFunction (MarginalSlotsOverBudget f _ _)  = f
warningFunction (CorrelatedWriteLogitsSlots f _) = f

-- | The one-paragraph text a warning prints as, prefixed @Warning: @.
renderCompileWarning :: CompileWarning -> String
renderCompileWarning w = "Warning: " ++ case w of
  MarginalSlotsOverBudget f k budget -> overBudgetNote f k budget
  CorrelatedWriteLogitsSlots f classes ->
    "the writeLogits of '" ++ f ++ "' encodes its slots independently, but "
    ++ intercalate "; and " (map clause classes)
    ++ ". The logit vector holds the product of those slots' marginals, not their joint "
    ++ "distribution: the correlation is discarded. Compiled anyway."
  where
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
