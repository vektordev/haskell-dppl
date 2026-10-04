-- | Per-mask inference variants and the runtime mask dispatcher (task
-- @per-mask-variants-by-pruning@, task 3 of design
-- @witnessed-per-query-capability@).
--
-- "SPLL.ObservationMask" says which slots of a function's observation a query
-- can mask, and how to turn a mask into an ordinary program (pruning). This
-- module is the IR half: given what "SPLL.Prelude" compiled from the pruned
-- programs, it builds the variant groups @f__m\<bits\>@ and turns the base
-- function's own probability and integrate bodies into a /dispatcher/ that
-- reads the query's mask with @isAny@ tests and hands the query to the
-- matching variant.
--
-- Everything here is pure IR construction. Compiling the variants is
-- 'SPLL.Prelude.compileRTyped''s job, because only the module that drives the
-- pipeline can run it again on a pruned program.
module SPLL.MaskVariants
  ( MaskVariant(..)
  , variantGroupName
  , maskBits
  , withDispatcher
  , maskedAtIR
  , overBudgetNote
  ) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types (ADTDecl(..), GenericValue(..), GenericList(..))
import SPLL.ObservationMask (Accessor(..), Slot, Mask, prettyMask)

import Data.List (intercalate)
import Data.Maybe (isJust, catMaybes)
import qualified Data.Set as Set

-- | One non-empty mask of a function, and what its masked program offers per
-- mode.
--
-- Each mode is @Nothing@ when the lattice does not admit the masked program
-- for it (or the mode is suppressed), and otherwise @Just@ the compiled body
-- or, on 'Left', why compiling it failed. The two layers are deliberately of
-- different cost: whether a mode is admitted is a modality verdict, read
-- without compiling any IR, while the body is the whole IR compile of the
-- masked program, and stays an unevaluated thunk until something reads it. So
-- the dispatcher can be built, and a query that never masks anything can be
-- answered, without paying for the variants — which matters, because a masked
-- program can cost far more than its unmasked one (a latent that the full
-- observation recovers is enumerated once a slot no longer pins it).
data MaskVariant = MaskVariant
  { mvMask  :: Mask
  , mvProb  :: Maybe (Either String IRFunDecl)
  , mvInteg :: Maybe (Either String IRFunDecl)
  }

-- | The mask's bits over the enumerated slots, in tree order: @1@ for a masked
-- slot, @0@ for a concrete one. W's @(ANY, _)@ is @"10"@.
maskBits :: [Slot] -> Mask -> String
maskBits slots m = [ if s `Set.member` m then '1' else '0' | s <- slots ]

-- | @f__m\<bits\>@: the group a mask's variant is emitted as.
--
-- A user may name a function @f__m10@ beside an @f@ with two enumerated slots;
-- 'SPLL.Prelude' checks for that collision and compiles no variants for @f@
-- rather than emit two groups of one name. Monomorphization's
-- @__int@/@__float@ clones use the same separator and never end in @m@
-- followed by bits.
variantGroupName :: String -> [Slot] -> Mask -> String
variantGroupName f slots m = f ++ "__m" ++ maskBits slots m

-- | A base group with its probability and integrate functions turned into
-- dispatchers, followed by its variant groups.
--
-- The dispatcher sits where the design puts it: under the parameter lambdas
-- and the query-type guard, so a wrong-typed query is still refused before any
-- accessor runs, and /around/ the unchanged all-concrete body, which keeps its
-- own root @isAny sample@ unit factor. Its shape, for enumerated slots
-- @s_1 .. s_k@:
--
-- > if (not (isAny sample)) && (<s_1 is ANY> || ... || <s_k is ANY>)
-- >   then <decision tree over the same tests>
-- >   else <the all-concrete body, byte-identical to before>
--
-- The all-concrete body appears exactly once. A root @ANY@ falls through to it
-- (its own root unit factor answers), and so does a query whose enumerated
-- slots are all concrete. Each leaf of the decision tree calls the mask's
-- variant with the dispatcher's own arguments, or, for a mask the lattice does
-- not admit, is an 'IRError' naming the function, the mask, and the masks it
-- does answer.
--
-- A variant group carries only the modes its base group has: the dispatcher
-- replaces a base body, and with no base body there is nothing to dispatch
-- from. Generate stays the base function's (a mask is a property of a query,
-- not of a sample), as do the normal shortcut and writeLogits.
withDispatcher :: [ADTDecl] -> [Slot] -> [MaskVariant] -> IRFunGroup -> [IRFunGroup]
withDispatcher decls slots variants g =
  g { probFun  = fmap (dispatch "prob" "probability" mvProb) (probFun g)
    , integFun = fmap (dispatch "integ" "integrate" mvInteg) (integFun g)
    , groupDoc = groupDoc g ++ dispatchNote
    }
  : variantGroups
  where
    fname = groupName g
    vname = variantGroupName fname slots

    variantGroups =
      [ IRFunGroup { groupName = vname (mvMask v)
                   , genFun = Nothing
                   , probFun = realise "probability" (mvMask v) (probFun g) (mvProb v)
                   , integFun = realise "integrate" (mvMask v) (integFun g) (mvInteg v)
                   , writeLogitsFun = Nothing
                   , normalFun = Nothing
                   , groupDoc = "Per-mask inference variant of " ++ fname ++ " at query mask "
                                ++ prettyMask slots (mvMask v) ++ " (" ++ show (length slots)
                                ++ " correlated slots): compiled from the program with those slots unobserved"
                   , refusedVariants = []
                   , sampleDomain = Nothing
                   , maskVariantOf = Just fname }
      | v <- variants
      , isJust (realise "" (mvMask v) (probFun g) (mvProb v)) || isJust (realise "" (mvMask v) (integFun g) (mvInteg v)) ]

    -- A base mode and an admitted variant mode give a variant body: the
    -- compiled one, or -- if compiling the masked program failed -- a refusal
    -- with the base body's parameter spine, so the dispatcher's call still has
    -- a function of the right arity to call.
    realise modeWord m base vmode = case (base, vmode) of
      (Just (baseBody, _), Just compiled) -> Just $ case compiled of
        Right d   -> d
        Left why  -> ( spineOf baseBody (IRError (refusal modeWord m ("NeST refused to compile it: " ++ why)))
                     , "Refused per-mask variant" )
      _ -> Nothing

    dispatchNote =
      "\nPer-mask dispatcher over " ++ show (length slots) ++ " correlated slots; variants: "
      ++ intercalate ", " (map groupName variantGroups)

    dispatch :: String -> String -> (MaskVariant -> Maybe (Either String IRFunDecl)) -> IRFunDecl -> IRFunDecl
    dispatch suffix modeWord field (body, doc) = (underLambdas [] body, doc)
      where
        underLambdas ps (IRLambda n b) = IRLambda n (underLambdas (ps ++ [n]) b)
        underLambdas ps (IRIf c@(IRConformsTo _ _) b err) = IRIf c (wrap ps b) err
        underLambdas ps b = wrap ps b

        wrap [] inner = inner   -- no query parameter: nothing to dispatch on
        wrap ps@(q : _) inner =
          let sample = IRVar q
              flags = [ maskedAtIR decls sample s | s <- slots ]
              anyMasked = IRIf (IRUnaryOp OpIsAny sample) falseIR (orAll flags)
          in IRIf anyMasked (decide ps flags []) inner

        -- Branch on each slot's mask flag in tree order; a leaf is a full mask.
        -- The flags are written out at each use rather than let-bound: they are
        -- a handful of isAny and tag tests, the optimizer's CSE shares them
        -- anyway, and an inline isAny test is what the batched backend and the
        -- select pass recognise as a structural (bucket-uniform) condition, so
        -- the dispatch stays a real branch there instead of a select that
        -- evaluates every variant eagerly.
        decide ps (f : fs) acc = IRIf f (decide ps fs (acc ++ [True])) (decide ps fs (acc ++ [False]))
        decide ps [] acc = leaf ps (Set.fromList [ s | (s, True) <- zip slots acc ])

        leaf ps m
          | Set.null m = IRError ("internal: the mask dispatcher of '" ++ fname
                                  ++ "' reached the all-concrete leaf, which it never selects")
          | any (\v -> mvMask v == m && isJust (field v)) variants =
              foldl IRApply (IRVar (vname m ++ "_" ++ suffix)) (map IRVar ps)
          | otherwise = IRError (refusal modeWord m
              ("the masked program is intractable for this mode (typically, a latent the "
               ++ "remaining slots share could only be integrated out by a convolution)"))

    -- The masks the lattice admits for a mode, all-concrete first.
    viable modeWord = prettyMask slots Set.empty
      : [ prettyMask slots (mvMask v) | v <- variants, isJust (modeOf modeWord v) ]
    modeOf modeWord = if modeWord == "integrate" then mvInteg else mvProb

    refusal modeWord m reason =
      "cannot compute marginal of '" ++ fname ++ "' at query mask " ++ prettyMask slots m
      ++ ": there is no " ++ modeWord ++ " function for the observation with "
      ++ maskedNames m ++ " unobserved; " ++ reason ++ ". The masks over its "
      ++ show (length slots) ++ " correlated slots that '" ++ fname ++ "' answers are: "
      ++ intercalate ", " (viable modeWord) ++ "."

    maskedNames m = case [ show i | (i, s) <- zip [1 :: Int ..] slots, s `Set.member` m ] of
      [one] -> "slot " ++ one
      many  -> "slots " ++ intercalate ", " many

    spineOf (IRLambda n b) e = IRLambda n (spineOf b e)
    spineOf _ e = e

    falseIR = IRConst (VBool False)
    trueIR = IRConst (VBool True)
    orAll [] = falseIR
    orAll [e] = e
    orAll (e : es) = IRIf e trueIR (orAll es)

-- | Is the query value's slot at this accessor path @ANY@ — either itself, or
-- because a node above it is?
--
-- Tested outer node first, so no accessor is ever applied to a @VAny@. A
-- constructor whose tag the query value does not carry (@Right v@ against a
-- @left (..)@ tree, @[]@ against a cons) answers 'False': the slot is not
-- masked, and if no other slot is either, the all-concrete body gets the query
-- and answers its impossibility as it always has. If another slot /is/ masked,
-- the variant gets it, and the variant is an ordinary compiled program that
-- answers a tag mismatch the same way.
maskedAtIR :: [ADTDecl] -> IRExpr -> Slot -> IRExpr
maskedAtIR _ v [] = IRUnaryOp OpIsAny v
maskedAtIR decls v (Accessor c i : rest) =
  IRIf (IRUnaryOp OpIsAny v)
       (IRConst (VBool True))
       (guarded (maskedAtIR decls (project c i v) rest))
  where
    guarded k = case tagTest c v of
      Nothing -> k
      Just t  -> IRIf t k (IRConst (VBool False))
    tagTest ctor x = case ctor of
      "TCons" -> Nothing
      "Cons"  -> Just (IRUnaryOp OpNot (IROp OpEq x (IRConst (VList EmptyList))))
      "left"  -> Just (IRDestruct AcIsLeft x)
      "right" -> Just (IRDestruct AcIsRight x)
      _       -> Just (IRApply (IRVar ("is" ++ ctor)) x)
    project ctor idx x = case (ctor, idx) of
      ("TCons", 0) -> IRDestruct AcFst x
      ("TCons", _) -> IRDestruct AcSnd x
      ("Cons", 0)  -> IRDestruct AcHead x
      ("Cons", _)  -> IRDestruct AcTail x
      ("left", _)  -> IRDestruct AcFromLeft x
      ("right", _) -> IRDestruct AcFromRight x
      _            -> IRApply (IRVar (adtField ctor idx)) x
    adtField ctor idx =
      case catMaybes [ if idx < length fields then Just (fst (fields !! idx)) else Nothing
                     | d <- decls, (cName, fields) <- constructors d, cName == ctor ] of
        (name : _) -> name
        [] -> error ("maskedAtIR: constructor " ++ ctor ++ " has no field " ++ show idx
                     ++ " (invariant: slots come from this program's own observation tree)")

-- | The doc note and warning text for a function over the slot budget.
overBudgetNote :: String -> Int -> Int -> String
overBudgetNote fname k budget =
  "'" ++ fname ++ "' has " ++ show k ++ " correlated observation slots, more than --marginalSlots "
  ++ show budget ++ " allows: no per-mask inference variants were compiled for it, so an ANY in "
  ++ "one of those slots is answered by the runtime marginal guard alone (which may refuse). "
  ++ "Raise --marginalSlots to " ++ show k ++ " to compile all " ++ show ((2 :: Int) ^ k) ++ " masks."
