-- | The modality type system: the capability lattice, the universal
-- marginalization rule, and the type-directed structured 'Mod'.
--
-- This is milestone 1 of the modality port (see the design doc
-- @modality-typesystem-port@). It ports the @nest_typing@ prototype's
-- @Modality.Lattice@ and @Modality.Core@ into this repo, applying the agreed
-- rename table and the three repo-specific adaptations:
--
--   * an orthogonal distribution-/family/ axis 'gFam' on 'GroundMod' (design §6),
--   * 'Fin' derived from the existing @DiscreteValues@ annotation (decision C),
--   * a family-aware projection from structured 'Mod' down to the flat 'PType'
--     this repo's @IRCompiler@ already consumes (decision B / §6).
--
-- It is /pure data + operators/: the bottom-up inference engine that builds
-- these modalities from expressions is milestone 4 ('SPLL.Typing.Modality' will
-- gain it then). The terse prototype identifiers are renamed here per the
-- rename table in @modality-port-lattice-core@; design §2 holds the living
-- prototype↔local glossary.
module SPLL.Typing.Modality
  ( -- * The capability lattice
    Capability(..)
  , CapabilitySet(..)
  , caps
  , allCapabilitySets
  , leqCap, joinCap, meetCap
    -- * Support finiteness (orthogonal to capability)
  , Fin(..)
  , joinFin
  , finFromTags
    -- * Distribution family (orthogonal to capability; design §6)
  , Family(..)
  , joinFamily, meetFamily
    -- * Ground modalities
  , GroundMod(..)
  , groundMod
  , validGroundMod
  , topGround, bottomGround
  , leqGround, joinGround, meetGround
    -- * The universal marginalization combinator (the doc's "▷")
  , marginalize
    -- * Structured modalities
  , Mod(..)
  , Transfer
  , mkTransfer, runTransfer, joinTransfer
    -- * The application rule and combinators
  , applyMod
  , applyOuter
  , joinModality
  , bottomModality
  , outerGround
    -- * Subtyping
  , subMod
  , modEq
  , reprInputs
    -- * Projection onto the flat PType (design §6)
  , projectGround
  , projectMod
    -- * Pretty-printing
  , prettyMod
  , prettyGround
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import SPLL.Typing.PType (PType(..))
import SPLL.Typing.RType (RType(..))
import SPLL.Lang.Types (Tag(..))

-- * The capability lattice -----------------------------------------------------

-- | Atomic capabilities. A modality is identified with the set it grants.
-- The @Can*@ prefix keeps these clear of the 'PType' constructors
-- (@Deterministic@/@Integrate@) they ultimately project /onto/ — a different
-- layer (see 'projectGround').
--
--   * 'CanSample'    — a black-box simulator exists (draw samples).
--   * 'CanDensity'   — a pointwise (unnormalized) density / mass function.
--   * 'CanIntegrate' — integrals: CDFs, P(event), expectations.
--   * 'CanExact'     — the value is exact / deterministic (a Dirac).
data Capability = CanSample | CanDensity | CanIntegrate | CanExact
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- | The six named lattice elements, each encoding the capability set it grants.
-- The partial order is subset inclusion; join/meet are union/intersection.
data CapabilitySet
  = Opaque        -- ^ @{}@          nothing computable
  | SampleOnly    -- ^ @{S}@         simulator only
  | DensityOnly   -- ^ @{S,D}@       density but no integral
  | IntegralOnly  -- ^ @{S,I}@       integral but no closed density
  | DensInt       -- ^ @{S,D,I}@     fully analytic
  | Exact         -- ^ @{S,D,I,T}@   exact / Dirac (top)
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- | All elements, for finite enumeration (what makes 'Transfer' tabulatable).
allCapabilitySets :: [CapabilitySet]
allCapabilitySets = [minBound .. maxBound]

-- | The capability set granted by an element. Order = subset on these sets.
caps :: CapabilitySet -> Set Capability
caps Opaque       = Set.empty
caps SampleOnly   = Set.fromList [CanSample]
caps DensityOnly  = Set.fromList [CanSample, CanDensity]
caps IntegralOnly = Set.fromList [CanSample, CanIntegrate]
caps DensInt      = Set.fromList [CanSample, CanDensity, CanIntegrate]
caps Exact        = Set.fromList [CanSample, CanDensity, CanIntegrate, CanExact]

-- | Inverse of 'caps' on the (closed) set of valid capability sets.
fromCaps :: Set Capability -> CapabilitySet
fromCaps s =
  case [ m | m <- allCapabilitySets, caps m == s ] of
    (m:_) -> m
    []    -> error ("fromCaps: not a valid lattice element: " ++ show (Set.toList s))

-- | @a `leqCap` b@ iff @a@ is less capable than or equal to @b@ (subset of caps).
-- 'Opaque' is bottom, 'Exact' is top; 'DensityOnly' and 'IntegralOnly' are
-- incomparable.
leqCap :: CapabilitySet -> CapabilitySet -> Bool
leqCap a b = caps a `Set.isSubsetOf` caps b

-- | Least upper bound (union of capabilities).
joinCap :: CapabilitySet -> CapabilitySet -> CapabilitySet
joinCap a b = fromCaps (caps a `Set.union` caps b)

-- | Greatest lower bound (intersection of capabilities).
meetCap :: CapabilitySet -> CapabilitySet -> CapabilitySet
meetCap a b = fromCaps (caps a `Set.intersection` caps b)

-- * Support finiteness ---------------------------------------------------------

-- | Support finiteness. Orthogonal to the capability lattice but decisive in
-- the marginalization rule: integrating out a /finite-discrete/ law is a finite
-- sum (keeps density), whereas integrating out a continuous law does not.
data Fin = Finite | Infinite
  deriving (Eq, Ord, Show, Read)

-- | A combination of two supports is finite only if both are.
joinFin :: Fin -> Fin -> Fin
joinFin Finite Finite = Finite
joinFin _      _      = Infinite

-- | Decision C: finiteness is /derived/ from the existing @DiscreteValues@
-- annotation (which strictly dominates a bare boolean — it carries the actual
-- enumerated values). A present @DiscreteValues@ tag ⇒ 'Finite'.
finFromTags :: [Tag] -> Fin
finFromTags ts = if any isDiscrete ts then Finite else Infinite
  where isDiscrete (DiscreteValues _) = True
        isDiscrete _                  = False

-- * Distribution family (design §6) --------------------------------------------

-- | The distribution-family closure property: a non-capability fact carried
-- /alongside/ the capability set, modeled exactly on 'Fin'. It is /not/ a fifth
-- 'Capability' atom — being Normal is a closure property that only pays off
-- under specific operators (the operator-aware @primSem@ layer, milestone 4),
-- not a query-capability. Only @{None, Normal, LogNormal}@ are populated now
-- (parity with today's @PNormal@/@PLogNormal@); the type is extensible to
-- Gamma/Beta/… later.
data Family = FamNone | FamNormal | FamLogNormal
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- | Family join/meet behave identically: keep the family if both agree,
-- otherwise bottom to 'FamNone' (a generic combination of two distinct
-- families is no longer in either).
joinFamily :: Family -> Family -> Family
joinFamily a b = if a == b then a else FamNone

meetFamily :: Family -> Family -> Family
meetFamily a b = if a == b then a else FamNone

-- * Ground modalities ----------------------------------------------------------

-- | The modality of a ground random quantity: a capability level, the
-- finiteness of its support, and its distribution family.
data GroundMod = GroundMod
  { gCap :: CapabilitySet
  , gFin :: Fin
  , gFam :: Family
  } deriving (Eq, Ord, Show, Read)

-- | Smart constructor enforcing the family validity constraint (design §6, the
-- analogue of the @Exact ⟹ Finite@ convention): a known distribution family is
-- only meaningful where the value is fully analytic, so
-- @gFam ∈ {Normal, LogNormal} ⟹ gCap = DensInt@. Fails loudly on violation —
-- this guards leaf construction (distribution primitives in milestone 4).
groundMod :: CapabilitySet -> Fin -> Family -> GroundMod
groundMod c f fam
  | validGroundMod gm = gm
  | otherwise = error ("groundMod: a family-annotated modality must be DensInt, got "
                       ++ show gm)
  where gm = GroundMod c f fam

-- | The family validity predicate behind 'groundMod' (exported for testing).
validGroundMod :: GroundMod -> Bool
validGroundMod (GroundMod c _ fam) = fam == FamNone || c == DensInt

topGround :: GroundMod
topGround = GroundMod Exact Finite FamNone     -- a known value: exact, finite

-- | The order-least ground modality (the fixpoint seed): 'Opaque' with the
-- order-least finiteness. Under 'leqGround' 'Finite' is /below/ 'Infinite' (a
-- finite thing can stand in where an infinite one is expected), so the lattice
-- bottom is @Opaque/Finite@ — matching the prototype's @botMod@ seed.
bottomGround :: GroundMod
bottomGround = GroundMod Opaque Finite FamNone

-- | Ground subtyping: more capable capability, 'Finite' more informative than
-- 'Infinite', and a known family is more informative than 'FamNone'.
leqGround :: GroundMod -> GroundMod -> Bool
leqGround (GroundMod c1 f1 m1) (GroundMod c2 f2 m2) =
  leqCap c1 c2 && finLeq f1 f2 && famLeq m1 m2
  where finLeq Finite   _        = True
        finLeq Infinite Infinite = True
        finLeq Infinite Finite   = False
        famLeq a b = a == b || b == FamNone

joinGround :: GroundMod -> GroundMod -> GroundMod
joinGround (GroundMod c1 f1 m1) (GroundMod c2 f2 m2) =
  GroundMod (joinCap c1 c2) (joinFin f1 f2) (joinFamily m1 m2)

meetGround :: GroundMod -> GroundMod -> GroundMod
meetGround (GroundMod c1 f1 m1) (GroundMod c2 f2 m2) =
  GroundMod (meetCap c1 c2)
            (if f1 == Finite || f2 == Finite then Finite else Infinite)
            (meetFamily m1 m2)

-- | The /universal marginalization combinator/ — the design doc's @▷@.
--
-- It returns the modality of a generic binary combination @z = g(x,y)@ with no
-- special structure (so the joint must actually be marginalized). The same
-- operator integrates out a random function choice in application
-- (@rho ▷ phi(m)@).
--
-- The rule, straight from the doc:
--
--   * Combining with a Dirac ('Exact') is free (monadic @return@): the result is
--     the other side. We still drop the family there — 'marginalize' is the
--     operator-/agnostic/ floor, and recognizing that e.g. @x + const@ is an
--     affine shift that /preserves/ the family is the job of the operator-aware
--     @shiftSem@ layer (milestone 4), a peer that consumes this one.
--   * Otherwise you pay one marginalization, which always costs 'CanExact', and
--     costs the density unless the integrated-out side is finite-discrete.
--
-- 'marginalize' is /family-agnostic/: its result always has @gFam = FamNone@.
marginalize :: GroundMod -> GroundMod -> GroundMod
marginalize a b
  | gCap a == Exact = b { gFam = FamNone }   -- combining with a Dirac is free
  | gCap b == Exact = a { gFam = FamNone }
  | otherwise       = GroundMod (fromCaps survive) finR FamNone
  where
    sa = caps (gCap a); sb = caps (gCap b)
    finR = joinFin (gFin a) (gFin b)
    has x s = x `Set.member` s
    -- Sampling survives if both sides can be sampled (joint sample + pushforward).
    keepS = has CanSample sa && has CanSample sb
    -- Integrals survive if each side offers a density or an integral.
    keepI = (has CanDensity sa || has CanIntegrate sa)
         && (has CanDensity sb || has CanIntegrate sb)
    -- A closed marginal density survives only with densities on both sides AND
    -- at least one finite-discrete side (so the marginal is a finite sum).
    keepD = has CanDensity sa && has CanDensity sb
         && (gFin a == Finite || gFin b == Finite)
    raw = Set.fromList $ concat [ [CanSample | keepS], [CanIntegrate | keepI], [CanDensity | keepD] ]
    -- Normalize: any of D/I implies S; guarantees a valid lattice element.
    survive | Set.null raw = raw
            | otherwise    = Set.insert CanSample raw

-- * Structured modalities ------------------------------------------------------

-- | The /transfer/ @phi@ of a function modality: a monotone map from the
-- argument's modality to the result's. Per design decision A it is a /finite
-- map/ — not an opaque Haskell closure — so it is @Show@/@Read@/@Eq@-able
-- (needed to serialize, diff-harness, and render an unapplied lambda's type).
-- The ground input domain is finite ('allCapabilitySets'), so the transfer is
-- tabulated by capability. The closure fallback for genuinely higher-order
-- arguments lands in milestone 4 (and must fail loudly, never silently
-- degrade).
type Transfer = Map CapabilitySet Mod

-- | A modality, mirroring the shape of a type.
data Mod
  = MGround GroundMod          -- ^ ground modality (a lattice element)
  | MProd Mod Mod              -- ^ product
  | MArr GroundMod Transfer    -- ^ function: outer @rho@, then transfer @phi@
  | MSum GroundMod Mod Mod     -- ^ sum: tag modality (how well we know /which/
                               --   branch), then each payload (left, right)
  | MRec GroundMod Mod         -- ^ recursive value (Option-A summary): a /spine/
                               --   modality (how tractable the shape/length is)
                               --   and the homogeneous /element/ modality. Folds
                               --   the would-be infinite modality tree into two
                               --   finite fields — see DESIGN §8.
  deriving (Eq, Ord, Show, Read)

-- | Tabulate a transfer from a function over the finite ground input lattice.
mkTransfer :: (GroundMod -> Mod) -> Transfer
mkTransfer f = Map.fromList [ (gCap g, f g) | g <- reprInputs ]

-- | Apply a transfer to an argument modality. Ground arguments are looked up by
-- capability (the dominant axis the transfer is tabulated over). Higher-order
-- arguments are the milestone-4 closure-fallback case and fail loudly here.
runTransfer :: Transfer -> Mod -> Mod
runTransfer t (MGround g) =
  case Map.lookup (gCap g) t of
    Just r  -> r
    Nothing -> error ("runTransfer: input capability outside the tabulated domain: "
                      ++ show (gCap g))
runTransfer _ m =
  error ("runTransfer: higher-order argument (closure fallback is milestone 4): "
         ++ prettyMod m)

-- | Pointwise join of two transfers (tabulated over the same domain).
joinTransfer :: Transfer -> Transfer -> Transfer
joinTransfer = Map.intersectionWith joinModality

-- | The application rule:  @Mod(f e) = rho ▷ phi(m)@. Apply the transfer to the
-- argument (the result /conditional/ on knowing which function we have), then
-- marginalize out the function choice @rho@ with 'applyOuter'.
applyMod :: Mod -> Mod -> Mod
applyMod (MArr rho phi) m = applyOuter rho (runTransfer phi m)
applyMod _ _ = error "applyMod: applied a non-function modality"

-- | Marginalize an outer (function-choice) law @rho@ into a conditional result,
-- extended over the type structure. When @rho@ is a Dirac the marginalization
-- is free and nothing changes.
applyOuter :: GroundMod -> Mod -> Mod
applyOuter rho (MGround g)  = MGround (marginalize rho g)
applyOuter rho (MProd a b)  = MProd (applyOuter rho a) (applyOuter rho b)
applyOuter rho (MArr r phi) = MArr (marginalize rho r) phi   -- transfer survives
applyOuter rho (MSum t a b) = MSum (marginalize rho t) (applyOuter rho a) (applyOuter rho b)
applyOuter rho (MRec s e)   = MRec (marginalize rho s) (applyOuter rho e)

-- | The outer (value-level) ground modality summarizing any 'Mod'. Used both
-- when an @if@ condition's law is marginalized out and by 'projectMod'.
outerGround :: Mod -> GroundMod
outerGround (MGround g)  = g
outerGround (MArr rho _) = rho
outerGround (MProd a b)  = meetGround (outerGround a) (outerGround b)
outerGround (MSum t a b) = meetGround t (meetGround (outerGround a) (outerGround b))
outerGround (MRec s e)   = meetGround s (outerGround e)

-- | Pointwise join of two modalities of the same shape (used for @if@ branches).
joinModality :: Mod -> Mod -> Mod
joinModality (MGround a)    (MGround b)    = MGround (joinGround a b)
joinModality (MProd a1 a2)  (MProd b1 b2)  = MProd (joinModality a1 b1) (joinModality a2 b2)
joinModality (MArr r1 p1)   (MArr r2 p2)   = MArr (joinGround r1 r2) (joinTransfer p1 p2)
joinModality (MSum t1 a1 b1)(MSum t2 a2 b2)= MSum (joinGround t1 t2) (joinModality a1 a2) (joinModality b1 b2)
joinModality (MRec s1 e1)   (MRec s2 e2)   = MRec (joinGround s1 s2) (joinModality e1 e2)
joinModality _ _ = error "joinModality: shape mismatch"

-- | The least modality at a given type shape — bottom of the modality lattice,
-- used to /seed/ least-fixpoint iteration for recursive definitions
-- (milestone 4). Driven by this repo's 'RType' (RInfer already produced these).
bottomModality :: RType -> Mod
bottomModality (Tuple a b)   = MProd (bottomModality a) (bottomModality b)
bottomModality (TEither a b) = MSum bottomGround (bottomModality a) (bottomModality b)
bottomModality (TArrow _ b)  = MArr bottomGround (mkTransfer (const (bottomModality b)))
bottomModality (ListOf a)    = MRec bottomGround (bottomModality a)
bottomModality _             = MGround bottomGround   -- ground scalars / ADTs / vars

-- * Subtyping ------------------------------------------------------------------

-- | Subtyping (@a <: b@ means @a@ is at most as capable as @b@). Functions are
-- covariant in @rho@; the transfer is compared pointwise over the finite ground
-- input lattice (sound for ground-domain functions; the type-directed version
-- for richer domains lands with the milestone-4 fixpoint).
subMod :: Mod -> Mod -> Bool
subMod (MGround a)     (MGround b)     = leqGround a b
subMod (MProd a1 a2)   (MProd b1 b2)   = subMod a1 b1 && subMod a2 b2
subMod (MArr r1 p1)    (MArr r2 p2)    =
  leqGround r1 r2 && and [ subMod (runTransfer p1 (MGround g)) (runTransfer p2 (MGround g))
                         | g <- reprInputs ]
subMod (MSum t1 a1 b1) (MSum t2 a2 b2) = leqGround t1 t2 && subMod a1 a2 && subMod b1 b2
subMod (MRec s1 e1)    (MRec s2 e2)    = leqGround s1 s2 && subMod e1 e2
subMod _ _ = False

-- | Modality equality, decided by subtyping in both directions. Because 'subMod'
-- tabulates transfers over the finite input lattice this is decidable — the
-- convergence test for fixpoint iteration.
modEq :: Mod -> Mod -> Bool
modEq a b = subMod a b && subMod b a

-- | Representative ground inputs used to tabulate and compare transfers: the six
-- capability levels (with their canonical finiteness, family-free).
reprInputs :: [GroundMod]
reprInputs =
  [ GroundMod Exact        Finite   FamNone
  , GroundMod DensInt      Infinite FamNone
  , GroundMod DensityOnly  Infinite FamNone
  , GroundMod IntegralOnly Infinite FamNone
  , GroundMod SampleOnly   Infinite FamNone
  , GroundMod Opaque       Infinite FamNone
  ]

-- * Projection onto the flat PType (design §6) ---------------------------------

-- | Project a ground modality onto the linear 'PType' this repo's @IRCompiler@
-- consumes (design decision B + the family axis, §6):
--
--   * @{}@ / @{S}@ → 'Bottom';
--   * the /partial/ sets @{S,D}@ and @{S,I}@ → 'Bottom' too — each is missing a
--     leg of a usable 'Integrate', and is held unreachable (the diff harness
--     asserts they never occur); projecting them to 'Integrate' would
--     /overpromise/;
--   * @{S,D,I}@ → 'PNormal' / 'PLogNormal' read off 'gFam', else 'Integrate';
--   * @{S,D,I,T}@ → 'Deterministic'.
--
-- The analytic-kernel refinement is thus read off 'gFam' here, not computed by a
-- separate @tryNormalClosure@ pass. No 'Prob' rung (decision B).
projectGround :: GroundMod -> PType
projectGround (GroundMod c _ fam) = case c of
  Opaque       -> Bottom
  SampleOnly   -> Bottom
  DensityOnly  -> Bottom
  IntegralOnly -> Bottom
  DensInt      -> case fam of
                    FamNormal    -> PNormal
                    FamLogNormal -> PLogNormal
                    FamNone      -> Integrate
  Exact        -> Deterministic

-- | Project any 'Mod' onto a flat per-node 'PType'. Non-function nodes project
-- losslessly through their ground summary; a function node ('MArr') projects its
-- /outer/ modality only — the transfer cannot fit in a flat 'PType' (design
-- §3-A, intentionally lossy).
projectMod :: Mod -> PType
projectMod = projectGround . outerGround

-- * Pretty-printing ------------------------------------------------------------

capName :: CapabilitySet -> String
capName Opaque       = "opaque"
capName SampleOnly   = "sample"
capName DensityOnly  = "dens"
capName IntegralOnly = "int"
capName DensInt      = "densint"
capName Exact        = "det"

famSuffix :: Family -> String
famSuffix FamNone      = ""
famSuffix FamNormal    = "~N"
famSuffix FamLogNormal = "~LN"

prettyGround :: GroundMod -> String
prettyGround (GroundMod c f fam) = capName c ++ "/" ++ finName f ++ famSuffix fam
  where finName Finite   = "fin"
        finName Infinite = "inf"

prettyMod :: Mod -> String
prettyMod (MGround g)   = prettyGround g
prettyMod (MProd a b)   = "(" ++ prettyMod a ++ " , " ++ prettyMod b ++ ")"
prettyMod (MSum t a b)  =
  "[tag=" ++ prettyGround t ++ " | inl " ++ prettyMod a ++ " | inr " ++ prettyMod b ++ "]"
prettyMod (MRec s e)    =
  "Rec<spine=" ++ prettyGround s ++ ", elem=" ++ prettyMod e ++ ">"
prettyMod (MArr rho phi) =
  "<rho=" ++ prettyGround rho ++ ", phi=[" ++ rows ++ "]>"
  where rows = intercalate ", "
          [ capName c ++ "->" ++ prettyMod m | (c, m) <- Map.toList phi ]
        intercalate sep = foldr1 (\x y -> x ++ sep ++ y)
