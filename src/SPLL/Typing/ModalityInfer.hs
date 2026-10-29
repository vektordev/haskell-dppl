-- | Stage 3 of the modality pipeline (design @modality-typesystem-port@ §4,
-- milestone 4, task @modality-inference-engine@): the bottom-up modality
-- inference engine that replaces 'SPLL.Typing.PInfer2'.
--
-- == What it does
--
-- For every node it builds a structured modality and writes the projected flat
-- 'PType' into the node's 'TypeInfo' — exactly the annotation @IRCompiler@ reads
-- today, so the interface is unchanged (design decision B / §3-A). The engine is
-- the adapted port of the @nest_typing@ prototype's @Modality.Infer@:
--
--   * the universal marginalization rule ('marginalize' / 'applyOuterI') is the
--     combinator behind application and generic binary ops; a random @if@
--     condition has its own rule ('mixtureGround' / 'mixOuterI'), which reads
--     no support finiteness;
--   * a syntactic lambda is a /known/ closure (outer @rho = det@) whose transfer
--     is obtained by partial evaluation of the body — so application is resolved
--     by β-reduction at the call site, which is what preserves the distribution
--     family ('Family') through application (design §6 motivating program 2);
--   * recursion among top-level declarations is a greatest fixpoint,
--     seeded at the top of the lattice and iterated downward via Kleene
--     iteration over the whole decl graph (covers mutual recursion; see
--     the note above 'topI' for why a least fixpoint would collapse
--     multi-clause recursion to 'Bottom').
--
-- == Internal representation
--
-- The engine carries an /internal/ modality 'IMod' whose 'IArr' transfer is a
-- genuine Haskell closure (not the finite 'SPLL.Typing.Modality.Transfer' map):
-- the closure receives the actual argument modality, family and all, so β-reduced
-- application is lossless. The finite-map 'Mod' of milestone 1 is the /projected/
-- form — produced by 'toMod' (tabulating the closure over the finite ground
-- input lattice) only when a serialisable value is needed (e.g. rendering an
-- unapplied lambda's type, or the diff harness). Per design §3-A this is where
-- the lossy/loud-fail finite-map fallback lives; the engine's own computation
-- never goes through it.
module SPLL.Typing.ModalityInfer
  ( addModalityPTypeInfo
  , collapseMomentable
  , collapsePoint
  , perNodeOuterGrounds
  , IMod(..)
  , Law(..)
  , Justification(..)
  , AffineCert(..)
  , Recovery(..)
  , EngineCert(..)
  , engineName
  , Engine(..)
  , callBindingKey
  , engineOrder
  , engineLabel
  , bindingCerts
  , mkICtx
  , ICtx
  , affineOf
  , LawTable
  , Env
  , renderJustification
  , jointAffineMaxSlots
  , lawValue
  , inferProgram
  , bindingLawEnv
  , bareLawOfPType
  , lambdaParamLaw
  , toMod
  , ReinferCtx
  , reinferCtx
  , reinferGiven
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Map.Lazy as LMap
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import SPLL.ReservedNames (uniformName, normalName)
import Data.Graph (SCC(..), stronglyConnComp)

import SPLL.Lang.Types
  ( Expr(..), ExprF(..), Program(..), TypeInfo(..), InjFName(..), ChainName, ADTDecl, CompilerError, FnDecl
  , Value, GenericValue(..), GenericList(..), Tag(..), MultiValue, GenericMultiValue(..) )
import SPLL.Lang.Lang (getTypeInfo, getSubExprs, containedVars, varsOfExpr, isZeroValue, freeVarsExpr, readOnceInPlace)
import SPLL.Analysis (enumerableDomain, enumerableApplication)
import SPLL.AutoNeural (planReadOf, planProjectedReadOf)
import Data.Maybe (isJust, isNothing, listToMaybe, mapMaybe)
import Control.Monad (guard)
import Data.List (intercalate, find)
import SPLL.Typing.Typing (setPType)
import SPLL.Typing.PType (PType(..))
import SPLL.Typing.RType (RType(..))
import SPLL.Typing.Modality
import SPLL.Typing.ForwardChaining (FCData(..), ExprInfo(..), InvChain, toInvExprMaybeWith, findEquivalentExpression, untag, isWitnessedLambda, WitnessCert(..), pointWitnessCert, WorldsShape, WorldsCtx(..), worldsShape, hasRandomLeaf, permissiveDet, unwrapLambdas)
import PredefinedFunctions (isFieldConstructor, propagateValuesLazily, isCollapse, collapseName)

-- ---------------------------------------------------------------------------
-- Internal closure-carrying modality
-- ---------------------------------------------------------------------------

-- | The engine's internal modality. Mirrors 'SPLL.Typing.Modality.Mod' but the
-- 'IArr' transfer is a real closure so β-reduced application keeps the full
-- argument modality (family included). Converted to the finite-map 'Mod' by
-- 'toMod' only when a serialisable value is required.
data IMod
  = IG GroundMod
  | IProd IMod IMod
  | IArr GroundMod (IMod -> IMod)
  | ISum GroundMod IMod IMod
  | IRec GroundMod IMod
  | IWit IMod
    -- ^ Witnessed value (design @modality-witnessed-inference@, milestone 2): a
    -- value that is a /deterministic function of the observation/ — an
    -- FC-witnessed let binding, or a deterministic image of one. The payload is
    -- its /standalone/ law (family and all): projection reads the standalone law
    -- unchanged (witnessing never lifts a value's own modality), while
    -- combinations ('injFMod's floor) treat the operand as Exact — recovering it
    -- from the observation is free, so it does not pay a marginalization. The
    -- once-counting ledger is positional: a witnessed value's density is counted
    -- exactly once, at its own standalone slot, never as a combination cost.

-- | Wrap as witnessed (idempotent).
iwit :: IMod -> IMod
iwit m@(IWit _) = m
iwit m          = IWit m

isWitI :: IMod -> Bool
isWitI (IWit _) = True
isWitI _        = False

-- | Is a value a /point/ given the observation: Deterministic, or witnessed
-- ('IWit'), field by field? A tuple input @(x_t, t)@ with @x_t@ witnessed and
-- @t@ deterministic is a point although its 'outerI' meet is not 'Exact', so a
-- product is decided per field. Any other structure must be 'Exact' outright.
-- Used by the 'ReadNN' rule of 'inferE'.
inputIsPoint :: IMod -> Bool
inputIsPoint (IWit _)    = True
inputIsPoint (IProd a b) = inputIsPoint a && inputIsPoint b
inputIsPoint m           = gCap (outerI m) == Exact

-- | The value-level ground summary of any 'IMod' (mirrors 'outerGround').
--
-- A scalar distribution family ('Family') is meaningful only on a bare scalar
-- value, so the structured cases ('IProd'/'ISum'/'IRec') drop it: a tuple, sum,
-- or list of Normals is not itself a Normal (mirrors @PInfer2.degradeNormal@ for
-- containers). The per-field family survives /inside/ the structure, so the
-- @fst@/@snd@ accessors still recover a field's Gaussian.
outerI :: IMod -> GroundMod
outerI (IG g)      = g
outerI (IArr rho _)= rho
outerI (IProd a b) = (meetGroundParts (outerI a) (outerI b))       { gFam = FamNone }
outerI (ISum t a b)= (meetGroundParts t (meetGroundMixture (outerI a) (outerI b))) { gFam = FamNone }
outerI (IRec s e)  = (meetGroundParts s (outerI e))               { gFam = FamNone }
outerI (IWit m)    = outerI m   -- witnessing never lifts the standalone law

-- | Project an 'IMod' onto the flat 'PType' (the per-node annotation).
projectI :: IMod -> PType
projectI = projectGround . outerI

-- | Project a /node/ onto the flat 'PType' @IRCompiler@ reads. A function-typed
-- modality ('IArr') is annotated with its /result (body)/ pType — apply the
-- transfer to a representative argument and recurse to the final result — not the
-- lossy outer-closure 'Deterministic'. This matches @PInfer2@ (which annotates a
-- function node with its body's pType) and is what @IRCompiler@ selects
-- prob/integrate codegen from: a @Var@ referencing a top-level
-- @distr x = 2*Uniform+x@ must read 'Integrate'. Non-function nodes project
-- losslessly through 'projectI'.
projectNode :: RType -> IMod -> PType
projectNode t            (IWit m)     = projectNode t m
projectNode (TArrow a b) (IArr _ phi) = projectNode b (phi (repIMod a))
projectNode _            m            = projectI m

-- | Marginalise an outer law into a conditional result over the structure
-- (mirrors 'applyOuter'; the design doc's @rho ▷@).
--
-- When the outer law is a Dirac (@rho = Exact@) — the case for /every/ syntactic
-- function and every deterministic @if@ condition — the marginalisation is free
-- and the result is the conditional unchanged, /family included/. This is the
-- crux of family-through-application: routing the Dirac case through
-- 'marginalize' instead would drop the family (the generic-floor design of
-- 'marginalize', M1), defeating the whole point of the closure transfer.
applyOuterI :: GroundMod -> IMod -> IMod
applyOuterI rho m | gCap rho == Exact = m
applyOuterI rho (IG g)      = IG (marginalize rho g)
applyOuterI rho (IProd a b) = IProd (applyOuterI rho a) (applyOuterI rho b)
applyOuterI rho (IArr r p)  = IArr (marginalize rho r) p
applyOuterI rho (ISum t a b)= ISum (marginalize rho t) (applyOuterI rho a) (applyOuterI rho b)
applyOuterI rho (IRec s e)  = IRec (marginalize rho s) (applyOuterI rho e)
-- Marginalising a genuinely random outer law into a witnessed value mixes it:
-- the result is no longer a deterministic function of the observation.
applyOuterI rho (IWit m)    = applyOuterI rho m

-- | A random-condition @if@ over the structure: 'mixtureGround' at every
-- ground (mirrors 'applyOuterI', whose 'marginalize' step this replaces for
-- @if@; see 'mixtureGround' for why the two differ). A Dirac condition is
-- free and keeps the family, exactly as in 'applyOuterI'.
mixOuterI :: GroundMod -> IMod -> IMod
mixOuterI c m | gCap c == Exact = m
mixOuterI c (IG g)       = IG (mixtureGround c g)
mixOuterI c (IProd a b)  = IProd (mixOuterI c a) (mixOuterI c b)
mixOuterI c (IArr r p)   = IArr (mixtureGround c r) p
mixOuterI c (ISum t a b) = ISum (mixtureGround c t) (mixOuterI c a) (mixOuterI c b)
mixOuterI c (IRec s e)   = IRec (mixtureGround c s) (mixOuterI c e)
-- As in 'applyOuterI': mixing over a random condition is no longer a
-- deterministic function of the observation.
mixOuterI c (IWit m)     = mixOuterI c m

-- | The application rule @Mod(f e) = rho ▷ phi(e)@. For a syntactic function the
-- transfer is the body closure (β-reduction). A non-function head is applied
-- opaquely through its outer ground (a safe, never-failing fallback for the
-- ill-typed / unknown-head case).
applyI :: IMod -> IMod -> IMod
applyI (IWit f)       arg = applyI f arg   -- a witnessed function is still that function
applyI (IArr rho phi) arg = applyOuterI rho (phi arg)
applyI other          arg = applyOuterI (outerI other) arg

-- | Pointwise /meet/ of two same-shape modalities — the combinator for @if@/case
-- branches. The result of a mixture is only as capable as the /weakest/ branch
-- (you need every branch's machinery to evaluate the mixture), so the
-- capability set is the meet, not the join. (Using the join is the prototype's
-- known "mixture join optimism" unsoundness — design §9 — which would type a
-- continuous mixture as 'Deterministic'.) The shape-mismatch fallback meets the
-- outer grounds.
--
-- Every ground combined here describes /alternative/ branches of one mixed
-- value, so — unlike a genuinely orthogonal combination such as an 'IProd'
-- pair's own two components — the 'Fin' axis wants 'meetGroundMixture', not
-- plain 'meetGround': a mixture's support is the union of the branch supports,
-- finite only when both branches are (task @modality-mixture-fin-joins-not-meets@).
meetI :: IMod -> IMod -> IMod
meetI (IWit a)     (IWit b)      = iwit (meetI a b)   -- both alternatives witnessed
meetI (IWit a)     b             = meetI a b
meetI a            (IWit b)      = meetI a b
meetI (IG a)       (IG b)        = IG (meetGroundMixture a b)
meetI (IProd a1 a2)(IProd b1 b2) = IProd (meetI a1 b1) (meetI a2 b2)
meetI (IArr r1 p1) (IArr r2 p2)  = IArr (meetGroundMixture r1 r2) (\m -> meetI (p1 m) (p2 m))
meetI (ISum t1 a1 b1)(ISum t2 a2 b2) = ISum (meetGroundMixture t1 t2) (meetI a1 a2) (meetI b1 b2)
meetI (IRec s1 e1) (IRec s2 e2)  = IRec (meetGroundMixture s1 s2) (meetI e1 e2)
meetI a b = IG (meetGroundMixture (outerI a) (outerI b))

-- | The greatest modality at a type shape — the /seed for the recursion
-- fixpoint/. Because every operation only ever loses capability (the rules are
-- 'marginalize'/'meetI', both monotone-decreasing), a recursive definition's
-- modality is a /greatest/ fixpoint: start every recursive occurrence at the top
-- (assume maximal capability) and let the body iterate it downward to the
-- stable value. Seeding at bottom instead would, with 'meetI' branches, collapse
-- a multi-clause recursion to 'Bottom' (the recursive branch never climbs).
topI :: RType -> IMod
topI (Tuple a b)   = IProd (topI a) (topI b)
topI (TEither a b) = ISum topGround (topI a) (topI b)
topI (TArrow _ b)  = IArr topGround (const (topI b))
topI (ListOf a)    = IRec topGround (topI a)
-- A tensor is a fixed-arity /homogeneous/ product (design tensors-in-core-language
-- §4.1: an n-ary 'IProd'). Folding 'IProd' at numel 784 is the cost the design's
-- implementation hint warns about; 'IRec' over the one element modality is the
-- compact homogeneous form it suggests as the fallback. Its spine ground is
-- 'topGround' because a tensor's shape is static, and its 'outerI' is the
-- element's own law without a family -- a tensor of Normals is not a Normal --
-- which is exactly the homogeneous n-ary product's projection.
topI (TTensor _ a) = IRec topGround (topI a)
topI _             = IG topGround

-- | A representative modality for an /unknown/ binder of a given type: ground
-- binders are taken 'Deterministic' (matching the @PInfer2@ default for a binder
-- not in scope), an unknown function passes its argument through (marginalising
-- the argument's law into a deterministic result skeleton).
repIMod :: RType -> IMod
repIMod (Tuple a b)   = IProd (repIMod a) (repIMod b)
repIMod (TEither a b) = ISum topGround (repIMod a) (repIMod b)
repIMod (TArrow _ b)  = IArr topGround (\arg -> applyOuterI (outerI arg) (repIMod b))
repIMod (ListOf a)    = IRec topGround (repIMod a)
repIMod (TTensor _ a) = IRec topGround (repIMod a)   -- see 'topI'
repIMod _             = IG topGround

-- | Subtyping over 'IMod' (transfers compared pointwise over the finite ground
-- input lattice). The convergence test for the fixpoint.
subI :: IMod -> IMod -> Bool
subI (IWit a)     b             = subI a b   -- the flag is bookkeeping, capability-equal
subI a            (IWit b)      = subI a b
subI (IG a)       (IG b)        = leqGround a b
subI (IProd a1 a2)(IProd b1 b2) = subI a1 b1 && subI a2 b2
subI (IArr r1 p1) (IArr r2 p2)  =
  leqGround r1 r2 && and [ subI (p1 (IG g)) (p2 (IG g)) | g <- reprInputs ]
subI (ISum t1 a1 b1)(ISum t2 a2 b2) = leqGround t1 t2 && subI a1 a2 && subI b1 b2
subI (IRec s1 e1) (IRec s2 e2)  = leqGround s1 s2 && subI e1 e2
subI _ _ = False

eqI :: IMod -> IMod -> Bool
eqI a b = subI a b && subI b a

-- | Tabulate the internal modality into the serialisable finite-map 'Mod'
-- (design §3-A: the projected/escaped form, where 'Transfer' is a finite map).
toMod :: IMod -> Mod
toMod (IG g)      = MGround g
toMod (IProd a b) = MProd (toMod a) (toMod b)
toMod (IArr rho p)= MArr rho (mkTransfer (\g -> toMod (p (IG g))))
toMod (ISum t a b)= MSum t (toMod a) (toMod b)
toMod (IRec s e)  = MRec s (toMod e)
toMod (IWit m)    = toMod m   -- the serialisable form carries only the standalone law

-- ---------------------------------------------------------------------------
-- Ground leaves
-- ---------------------------------------------------------------------------

-- | Decision C: a node with an enumerable domain ('SPLL.Analysis.enumerableDomain',
-- read through 'finFromTags') has finite support, so its ground modality is
-- 'Finite' regardless of how the combination rule arrived at its capability.
-- Applied to the enumerable leaves and results (ReadNN of a categorical net,
-- integer @plusI@/equality, …) where it turns the marginalization floor from
-- @{S,I}@ (no closed density) into @{S,D,I}@ (a finite mixture has a density).
--
-- Only the tag counts. A node whose /type/ is structurally finite but which
-- carries no tag has nothing an IRCompiler equation could enumerate, so a
-- 'Finite' there would let 'marginalize''s @keepD@ promise a density no
-- equation builds (task finiteness-single-producer). The shape that once
-- needed finite-by-type, a random Bool condition of an @if@, is the
-- 'mixtureGround' rule's, which reads no 'Fin'.
tagFin :: TypeInfo -> GroundMod -> GroundMod
tagFin ti g
  | finFromTags (tags ti) == Finite = g { gFin = Finite }
  | otherwise                       = g

tagFinMod :: TypeInfo -> IMod -> IMod
tagFinMod ti (IG g)   = IG (tagFin ti g)
tagFinMod ti (IWit m) = IWit (tagFinMod ti m)
tagFinMod _  m        = m

-- | A scalar distribution family ('FamNormal'/'FamLogNormal') only attaches to a
-- bare 'TFloat' value. A field constructor that builds a container/sum (e.g.
-- @left :: a -> Either a b@, @cons@) yields a value that is not itself Gaussian,
-- so drop the family there (mirrors @PInfer2.degradeNormal@ for containers). The
-- single-field 'IG' case — @left (Normal …)@, which the @injFMod@ floor passes
-- through unchanged — is the one this catches that 'outerI' alone cannot, since
-- no 'IProd'/'ISum' wrapper marks it as a container.
gateScalarFamily :: RType -> IMod -> IMod
gateScalarFamily TFloat m        = m
gateScalarFamily t      (IWit m) = IWit (gateScalarFamily t m)
gateScalarFamily _      (IG g)   = IG g { gFam = FamNone }
gateScalarFamily _      m        = m

gExact, gIntegrate, gNormal, gLogNormal :: GroundMod
gExact     = topGround                                 -- Deterministic
gIntegrate = groundMod DensInt Infinite FamNone        -- Integrate
gNormal    = groundMod DensInt Infinite FamNormal      -- PNormal
gLogNormal = groundMod DensInt Infinite FamLogNormal   -- PLogNormal

-- | Lift the result of 'tryNormalClosure' (a flat 'PType') back to a ground
-- modality with its family axis set.
fromClosurePType :: PType -> GroundMod
fromClosurePType PNormal       = gNormal
fromClosurePType PLogNormal    = gLogNormal
fromClosurePType Deterministic = gExact
fromClosurePType _             = gIntegrate

-- ---------------------------------------------------------------------------
-- Environment and the bottom-up walk
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Laws: a capability summary with its justification (law-carrying-modality M3)
-- ---------------------------------------------------------------------------

-- | What the engine concluded about a value (design @law-carrying-modality@
-- §A): its capability summary ('lawMod', projected to the flat 'PType' by
-- 'projectI' exactly as before) together with /why/ -- the data an engine
-- would need to act on it ('lawJust').
--
-- Each engine consumes its own row rather than re-deriving the fact from
-- syntax (design law-carrying-modality); 'Justification' names the consumers.
data Law = Law
  { lawMod  :: IMod
  , lawJust :: Justification
  }

-- | Why a node has its law. The rule for adding a constructor: a row exists
-- only with an engine that consumes it, and it is issued only where that
-- engine can act on it. A node none of them describes is 'JUnjustified',
-- which says nothing about its capability (that is 'lawMod''s job), only that
-- no certificate backs it yet.
--
-- The three that need no engine came first (M3); the affine Gaussian form is
-- the first engine-backed one (M4). The rest are later milestones' (witnessed,
-- worlds, plan, enumerable: M5), and until they land the nodes they will
-- describe are 'JUnjustified'.
data Justification
  = JDirac (Maybe Value)
    -- ^ A point mass: the node's capability is 'Exact'. Carries the value
    -- where it is statically known -- a constant, a node whose enumeration
    -- domain is a single value, a product with a literal zero factor, an
    -- 'InjF' of points of known value ('foldedValue'), a tuple field of known
    -- value ('projectedLaw'), a call whose callee returns a known point
    -- ('JReturns').
  | JLeaf String [Law]
    -- ^ A primitive distribution and the laws of its parameters: @Normal@ and
    -- @Uniform@ (no parameters), or a neural read whose input is a point
    -- (@neural <net>@, the input's law).
  | JStructured String [Law]
    -- ^ A field constructor (a tuple, @Cons@, a user-ADT constructor) and the
    -- laws of its fields, in order.
  | JAffine AffineCert
    -- ^ An affine Gaussian form (design @affine-gaussian-forms@ §2): the value
    -- is an affine combination of the independent standard-normal latents
    -- named. Consumed by the compiler's Gaussian collapse, which marginalises
    -- a binding certified this way ('IRCompiler.affineMarginalisable').
  | JPlan [ChainName]
    -- ^ A value read off a neural network's structured output through a
    -- @let@: bound to a plan read ('SPLL.AutoNeural.planReadOf'), or computed
    -- from such a binding. The chain names are the plan reads it projects
    -- from. Consumed by 'compareGround': the plan-guided engine measures a
    -- comparison whose operands both project from plan reads.
  | JBinding [EngineCert]
    -- ^ The applied lambda of a random binding the body reads: the
    -- certificates of the engines that apply to it, in dispatch order
    -- ('bindingCerts'). Empty when none does, and then the binding is
    -- sample-only (the let rule of 'inferE').
  | JSharedLatent String [ChainName] [Law]
    -- ^ A field constructor, with its fields' laws, two of whose density
    -- factors integrate the same 'Marginal' affine latents, listed
    -- ('structuredLaw'). Their joint law is a multivariate
    -- Gaussian, which no engine implements (affine-gaussian-forms M2), so the
    -- node is sample-only: this is the certificate saying so, and the lattice
    -- floors on it ('sampleOnlyI').
  | JReturns Int Justification
    -- ^ A function whose result, after @n@ more arguments (@n >= 1@), has
    -- the justification, whatever the arguments: its body's justification
    -- under the representative of its parameter, with every part that could
    -- depend on the argument dropped ('argumentFree'). @h z = 0.0 * z@
    -- returns @JDirac (Just 0.0)@. Consumed by the
    -- application rule, which gives the call that justification
    -- ('applyLaw'), and through it by the compiler's Dirac-law clause
    -- ('IRCompiler.lawPoint') at the call (task
    -- dirac-law-point-lost-under-plus-or-helper).
  | JUnjustified

-- | The certificate of an affine Gaussian form: the latents the value is an
-- affine combination of, keyed by the chain name of the node that drew each
-- (the keys @IRCompiler@'s own @AffineForm@ uses), each with whether it is
-- recovered from the observation. The coefficients are not here: they are
-- runtime quantities, which the compiler builds as IR from the expression the
-- certificate is about.
--
-- Two reads of one @draw@-bound variable carry the same key ('bindParam'), so
-- @x + x@ is one latent, while every other Gaussian leaf is a fresh one. An
-- empty map is a constant.
data AffineCert = AffineCert
  { acLatents :: Map ChainName Recovery
  , acFactors :: Map ChainName (Set.Set ChainName)
    -- ^ The density factors of the witnessed bindings the value reads, keyed
    -- by the binding's 'Recovered' latent: the 'Marginal' latents each one's
    -- density integrates out. The positional ledger counts each once,
    -- wherever the binding is read.
  }

-- | Whether an affine latent is known given the observation. A witnessed
-- binding is one 'Recovered' latent to everything that reads it
-- ('bindParam'). Only a 'Marginal' latent has to be integrated out, so only
-- those can correlate two density factors ('JSharedLatent').
--
-- A 'Joint' latent is integrated out too, but by the joint affine engine of
-- the binding that drew it ('jointAffineBindingCert'; design
-- affine-gaussian-forms M2), which measures every density leaf reading it as
-- one multivariate Gaussian. Two factors sharing it are therefore correlated
-- on purpose, and not a reason to floor ('marginalsOf' leaves it out).
data Recovery = Marginal | Joint | Recovered
  deriving (Eq, Ord, Show)

constantCert :: AffineCert
constantCert = AffineCert Map.empty Map.empty

-- | The 'Marginal' latents of a form.
marginalsOf :: AffineCert -> Set.Set ChainName
marginalsOf = Map.keysSet . Map.filter (== Marginal) . acLatents

-- | A law with no justification beyond its capability: 'JDirac' (value
-- unknown) when the value is a point mass, 'JUnjustified' otherwise. A
-- function is never a 'JDirac': its law is its transfer.
bareLaw :: IMod -> Law
bareLaw m = Law m (if isPointMass m then JDirac Nothing else JUnjustified)

-- | The law of a value known only by its flat annotation: a fallback for a
-- node no inference saw.
bareLawOfPType :: PType -> Law
bareLawOfPType = bareLaw . IG . fromClosurePType

isPointMass :: IMod -> Bool
isPointMass (IArr _ _) = False
isPointMass (IWit _)   = False
isPointMass m          = gCap (outerI m) == Exact

-- | An engine's certificate for a random binding (task
-- engine-applicability-as-data, law-carrying-modality M5): what the engine
-- reads off the binding to compile it. One per probabilistic-application
-- engine, in IRCompiler's dispatch order.
data EngineCert
  = CertEnumerable MultiValue
    -- ^ Enumeration: the argument's finite domain
    -- ('SPLL.Analysis.enumerableApplication').
  | CertPlan String
    -- ^ Plan-guided enumeration: the network whose structured output the
    -- argument reads ('SPLL.AutoNeural.planReadOf').
  | CertWitnessed WitnessCert
    -- ^ Point inversion: the inverse and the root-seeded witness verdict
    -- ('SPLL.Typing.ForwardChaining.pointWitnessCert').
  | CertAffine AffineCert
    -- ^ Affine marginalisation: the argument's affine Gaussian form, every use
    -- of which flows into one affine consumer ('affineBindingCert').
  | CertJointAffine AffineCert
    -- ^ Joint affine marginalisation: the argument's affine Gaussian form,
    -- read by a let spine of affine bindings ending in a tuple, whose affine
    -- fields are measured as one multivariate Gaussian
    -- ('jointAffineBindingCert').
  | CertWorlds WorldsShape
    -- ^ Set-valued witnesses: how the observation inverts onto the variable
    -- ('SPLL.Typing.ForwardChaining.worldsShape').
  | CertInPlace
    -- ^ The argument measured at the variable's one read
    -- ('SPLL.Lang.Lang.readOnceInPlace'): the body reads the variable once,
    -- with no binder on the way, so the read has the argument's own law
    -- (which is how 'bindParam' already types it) and the binding denotes
    -- @body[x := arg]@. Last: it is the engine of a binding no other engine
    -- measures, and moves no code of one another engine does. The compiler
    -- tries it after the set-witness engine's fallback as well
    -- ('IRCompiler.applyBinding'), so it must stay last in 'engineOrder'.

-- | The engines of a random binding (law-carrying-modality decision 1). The
-- constructor order is the dispatch order, and 'engineOrder' is its one
-- statement: 'bindingCerts' lists certificates in it, and IRCompiler's
-- 'applyBinding' tries its constructions in it. Each seam where two engines
-- can both apply has its reason, measured over the corpus, in
-- @docs/modality-and-admission.md@ ("Engine applicability").
data Engine
  = EnumerationEngine
  | PlanEngine
  | PointInversionEngine
  | JointAffineEngine
  | AffineEngine
  | WorldsEngine
  | InPlaceEngine
  deriving (Eq, Ord, Enum, Bounded, Show)

-- | The dispatch order of the binding engines.
engineOrder :: [Engine]
engineOrder = [minBound .. maxBound]

-- | An engine's name, as @-v@'s "compiled by" line prints it.
engineLabel :: Engine -> String
engineLabel k = case k of
  EnumerationEngine    -> "enumeration"
  PlanEngine           -> "plan-guided enumeration"
  PointInversionEngine -> "point inversion"
  AffineEngine         -> "affine marginalisation"
  JointAffineEngine    -> "joint affine marginalisation"
  WorldsEngine         -> "set-valued witnesses"
  InPlaceEngine        -> "in place"

-- | The engine a certificate is for, as @-d@ and @-v@ print it.
engineName :: EngineCert -> String
engineName c = case c of
  CertEnumerable _ -> "enumeration"
  CertPlan n       -> "plan " ++ n
  CertWitnessed w  -> "point inversion" ++ (if wcAtRoot w then " (witnessed)" else "")
  CertAffine _     -> "affine marginalisation"
  CertJointAffine _ -> "joint affine marginalisation"
  CertWorlds _     -> "set-valued witnesses"
  CertInPlace      -> "in place"

-- | One line per law, for the @-d@ dump and for tests.
renderJustification :: Justification -> String
renderJustification j = case j of
  JDirac Nothing   -> "dirac"
  JDirac (Just v)  -> "dirac " ++ renderValue v
  JLeaf p []       -> "leaf " ++ p
  JLeaf p ls       -> "leaf " ++ p ++ args ls
  JStructured c ls -> c ++ args ls
  JAffine c        -> "affine" ++ latents c
  JSharedLatent c ks ls -> c ++ args ls ++ " sharing latent " ++ intercalate ", " ks
  JPlan rs         -> "plan " ++ intercalate ", " rs
  JBinding []      -> "binding: no engine (sample-only)"
  JBinding cs      -> "binding: " ++ intercalate ", " (map engineName cs)
  JReturns n r     -> "returns " ++ renderJustification r ++ " after " ++ show n ++ " argument" ++ (if n == 1 then "" else "s")
  JUnjustified     -> "unjustified"
  where args ls = "(" ++ intercalate ", " (map (renderJustification . lawJust) ls) ++ ")"
        renderValue (VFloat x) = show x
        renderValue (VInt n)   = show n
        renderValue (VBool b)  = show b
        renderValue v          = show v
        latents (AffineCert m _) = "(" ++ intercalate ", "
          [ k ++ recovery r | (k, r) <- Map.toList m ] ++ ")"
        recovery r = case r of
          Marginal  -> ""
          Joint     -> " joint"
          Recovered -> " recovered"

-- | The per-node certificates of a program, keyed by chain name: what
-- 'inferProgram' concluded at every node of the program as written (not at
-- the β-reduced copies its closures evaluate).
type LawTable = Map ChainName Law

-- | The binder environment: the law of every variable in scope. 'inferE'
-- extends it at every binder, and the compiler keeps one too
-- (@CompilerMetadata.lawEnv@), extended by the same 'bindParam'.
type Env = Map String Law

-- | Per-node laws accumulated during the walk, keyed by chain name (every
-- node has one after @annotateProg@): the source of 'LawTable' and of the
-- diff harness's per-node outer grounds (design §6).
type GAcc = [(ChainName, Law)]

-- | The per-declaration inference context: the ADT declarations, the
-- forward-chaining certificate, and the chain name of the declaration root —
-- the /observed/ node the witnessed-binding query is seeded at (design
-- @modality-witnessed-inference@, milestone 2).
data ICtx = ICtx
  { icADTs :: [ADTDecl]
  , icFC   :: FCData
  , icObs  :: ChainName
    -- | The program, as written: the engine predicates of a binding read its
    -- declarations (a conditional callee, a call the set-witness walk enters)
    -- and its neural declarations (a plan read).
  , icProg :: Program
    -- | The chain names of the program's plan reads ('planReadCNs').
  , icPlanReads :: Set.Set ChainName
    -- | 'isWitnessedLambda' seeded at 'icObs', partially applied once so
    -- every application asked about shares one forward-chaining solve
    -- ('withObs' keeps the two in step).
  , icWitnessed :: ChainName -> Bool
    -- | Every node of the program, as written, by chain name: where a named
    -- callee's lambda is looked up ('calleeBindingCerts'). Lazy, so built
    -- only by a context that meets such a call.
  , icNodes :: Map ChainName Expr
    -- | 'calleeSyntax' of the head of every call in the program, by the
    -- head's chain name: lazy in its values, so each is solved at most once
    -- per declaration's context, however often a closure re-evaluates the
    -- call (the fixpoint's convergence test evaluates every closure over the
    -- whole input lattice). It does not read the observation, so 'withObs'
    -- keeps it.
  , icCallSyntax :: LMap.Map ChainName (Maybe CallSyntax)
    -- | The variables in scope the compiler holds at a point when it
    -- compiles this node, although their law may be random: the parameters
    -- of the closures being evaluated around it (the 'Lambda' rule's), and
    -- the variables of the @draw@s on the way whose binding an engine
    -- answers at a point (enumeration, a plan read, point inversion;
    -- 'letBinding'). A call binding only such variables has an argument
    -- that is a point where it is compiled ('calleeBindingCerts').
  , icPoint :: String -> Bool
  }

-- | The inference context of the declaration observed at @obsCN@.
mkICtx :: [ADTDecl] -> FCData -> ChainName -> Program -> ICtx
mkICtx adtsDecls fcData obsCN prog = ctx
  where
    ctx = ICtx adtsDecls fcData obsCN prog (planReadCNs prog) (isWitnessedLambda fcData adtsDecls obsCN)
            (Map.fromList [ (cnOf e, e) | (_, b) <- functions prog, e <- universe b ])
            (callSyntaxTable ctx) (const False)
    universe e = e : concatMap universe (getSubExprs e)

-- | The context with the observation moved to @obsCN@.
withObs :: ICtx -> ChainName -> ICtx
withObs ctx obsCN = ctx { icObs = obsCN, icWitnessed = isWitnessedLambda (icFC ctx) (icADTs ctx) obsCN }

-- | 'icCallSyntax', for a context.
callSyntaxTable :: ICtx -> LMap.Map ChainName (Maybe CallSyntax)
callSyntaxTable ctx = LMap.fromList
  [ (cnOf h, calleeSyntax ctx (cnOf h)) | (_, b) <- functions (icProg ctx), Expr _ (Apply h _) <- universe b ]
  where universe e = e : concatMap universe (getSubExprs e)

cnOf :: Expr -> ChainName
cnOf = chainName . getTypeInfo

-- | Infer the law of an expression, returning the law, the pType-annotated
-- expression, and the per-node law accumulation.
--
-- The modality ('lawMod') is computed by the rules below; the justification
-- is attached alongside it and never feeds back into a modality, so the
-- annotation is exactly what it was before laws existed.
inferE :: ICtx -> Env -> Expr -> (Law, Expr, GAcc)
inferE ctx env expr = case expr of

  -- The theta-tree source of ThetaI/Subtree is left untouched (PInfer2 does not
  -- annotate it either); only this node's own modality is recorded.
  Expr ti (ThetaI s i)  -> done' (IG gExact) (Expr (setPType ti Deterministic) (ThetaI s i)) []
  Expr ti (Subtree s i) -> done' (IG gExact) (Expr (setPType ti Deterministic) (Subtree s i)) []
  Expr ti (Constant v)  -> doneL (Law (IG gExact) (JDirac (Just v))) (Expr (setPType ti Deterministic) (Constant v)) []

  -- A variable's law is its binder's, justification included: a @draw@-bound
  -- variable reads as what it was bound to.
  Expr ti (Var name) ->
    let l = case Map.lookup name env of
              Just bl            -> bl
              Nothing
                | name == normalName  -> Law (IG gNormal) (JLeaf normalName [])
                | name == uniformName -> Law (IG gIntegrate) (JLeaf uniformName [])
                | otherwise         -> bareLaw (IG gExact)   -- unbound ⇒ Deterministic (PInfer2 default)
    in doneL l (Expr (setPType ti (projectNode (rType ti) (lawMod l))) (Var name)) []

  -- A neural read is a Gaussian head (Float) or an enumerable/integrable read
  -- /given its input/. That verdict is the read's own law only when the input
  -- is a point: Deterministic, or witnessed on the path ('inputIsPoint'). A
  -- random, unwitnessed input -- possible since inputs became program-computed
  -- (task tensor-type-shaped-neural-inputs) -- makes the read a continuous
  -- mixture over the input, @∫ N(y; mu(x), sigma(x)) p(x) dx@, which has no
  -- closed form: the read is sample-only ('Bottom'). This is the restrictive
  -- verdict (a) decided in diffusion-models-wishlist on 2026-10-01. Before it,
  -- the input's modality was discarded, which was sound only while every input
  -- was an opaque Symbol, and @mu Normal@ answered a silently wrong density.
  Expr ti (ReadNN name s) ->
    let (sl, s', sa) = inferE ctx env s
        given = tagFin ti (if rType ti == TFloat then gNormal else gIntegrate)
        l | inputIsPoint (lawMod sl) || pointGivenWitnesses ctx env s
                      = Law (IG given) (JLeaf ("neural " ++ name) [sl])
          | otherwise = bareLaw (IG (groundMod SampleOnly Infinite FamNone))
    in doneL l (Expr (setPType ti (projectI (lawMod l))) (ReadNN name s')) sa

  -- gt/lt are forward-only InjFs (PredefinedFunctions), but their modality is
  -- not the generic marginalize-combination floor 'injFMod' gives every other
  -- InjF: a comparison's Boolean result is a Bernoulli (finite support) whose
  -- capability depends on whether its operands are exactly comparable
  -- (Exact/DensInt) or only samplable, not on marginalizing two continuous
  -- operands together. This mirrors the old bespoke GreaterThan/LessThan
  -- dispatch (task gt-lt-range-propagation).
  Expr ti (InjF (Named fname) [a, b])
    | fname `elem` ["gt", "lt"] -> compareNode ti fname a b

  -- 'collapse' (task encode-07-collapse-operator) is the Gaussian with its
  -- operand's mean and variance, whatever the operand's own law: a mixture, a
  -- Gaussian (a no-op) or anything else whose moments the compiler can read
  -- ('IRCompiler.momentsOf' refuses the rest). A fresh leaf, like 'Normal': not
  -- an image of the operand's value, so neither witnessed by it nor sharing
  -- its latents. A point-mass operand stays the point.
  --
  -- The moments are taken over the operand's own draws, given the values of
  -- the variables it reads: under a function parameter (a point) that is a
  -- Gaussian, but over a random @let@-bound variable it is a mixture of
  -- Gaussians again, which is left sample-only. So is an operand whose moments
  -- the compiler cannot read ('collapseMomentable').
  Expr ti (InjF name@(Named fname) [a])
    | isCollapse fname ->
      let (la, a', aa) = inferE ctx env a
          givenPoints = all (\v -> maybe True (isPointLaw . lawMod) (Map.lookup v env))
                            (Set.toList (freeVarsExpr a) `excluding` topLevel)
          isPointLaw m = gCap (outerI m) == Exact
          topLevel v = isJust (lookup v (functions (icProg ctx)))
          excluding vs p = filter (not . p) vs
          l | isPointLaw (lawMod la) = la
            | givenPoints && collapseMomentable topLevel a' = Law (IG gNormal) (JLeaf collapseName [la])
            | otherwise = bareLaw (IG (groundMod SampleOnly Infinite FamNone))
      in doneL l (Expr (setPType ti (projectI (lawMod l))) (InjF name [a'])) aa

  -- An affine operator ('affineInjF') over operands that have affine forms
  -- is Gaussian, and its law is the form: the family verdict is the form's
  -- existence (design law-carrying-modality M4), not a table over the
  -- operands' projected pTypes.
  Expr ti (InjF name@(Named fname) args) ->
    let rs   = map (inferE ctx env) args
        laws = [ al | (al,_,_) <- rs ]
        es'  = [ e  | (_,e,_) <- rs ]
        acc  = concat [ a | (_,_,a) <- rs ]
        affine = case affineInjF fname (zipWith (affineOf . cnOf) args laws) of
                   Just c | not (Map.null (acLatents c)) -> Just c
                   _ -> Nothing
        m0   = gateScalarFamily (rType ti) (tagFinMod ti (injFMod (icADTs ctx) fname (isJust affine) (map lawMod laws)))
        l | Just z <- zeroFactor                  = Law (IG gExact) (JDirac (Just z))
          | isFieldConstructor (icADTs ctx) fname = structuredLaw fname laws m0
          | Just c <- affine                      = Law m0 (JAffine c)
          | Just pl <- projectedLaw fname laws m0 = pl
          | isPointMass m0, Just v <- foldedValue (icADTs ctx) fname laws
                                                  = Law m0 (JDirac (Just v))
          | otherwise                             = pointOr m0 (Expr ti (InjF name es'))
        -- mult(0, y) = 0 for every y, whatever y's own law: a point mass, not
        -- (as 'injFMod' would say) whatever family y belongs to (task
        -- mult-inversion-unguarded-at-zero). Read off the operands' laws (a
        -- Dirac at zero), so a zero bound by a @draw@, or a value set {0},
        -- counts as the literal does (design law-carrying-modality §E). The
        -- compiler measures the node from this law's value and never builds
        -- 'mult''s inversion through a division by zero.
        zeroFactor
          | fname `elem` ["mult", "multI"] = listToMaybe [ v | Just v <- map lawValue laws, isZeroValue v ]
          | otherwise = Nothing
        e'   = Expr (setPType ti (projectI (lawMod l))) (InjF name es')
    in doneL l e' acc

  -- The arms are inferred under an environment in which every random variable
  -- the condition reads has been /conditioned/ on the condition's outcome:
  -- see 'conditionEnv'. The condition itself is inferred under the unrefined
  -- environment (it reads the variable's standalone law).
  --
  -- An observed @if@ under a condition with no random leaf passes the
  -- observation on to its arms: whichever arm is taken, its value /is/ the
  -- observed value, so a binding the arm reads is witnessed from the arm's
  -- result ('armCtx'). Without it, a recursive call in the else arm of
  -- @step t x = if t < 0.5 then [x] else x : step (t - 1.0) (mu x)@ bound
  -- its parameter unwitnessed, so the inner @mu x@ read a random input and
  -- floored the whole trajectory to 'Bottom' (task
  -- tensor-gaussian-heads-rd-diffusion). IRCompiler already compiles each arm
  -- against the same sample, so this only aligns the verdict with it.
  Expr ti (IfThenElse c t f) ->
    let (lc, c', ca) = inferE ctx env c
        armEnv       = conditionEnv env c
        armCtx arm
          | fst (unwrapLambdas (icFC ctx) (icObs ctx)) == cnOf expr
          , gCap (outerI (lawMod lc)) == Exact = withObs ctx (cnOf arm)
          | otherwise = ctx
        (lt, t', ta) = inferE (armCtx t) armEnv t
        (lf, f', fa) = inferE (armCtx f) armEnv f
        m = mixOuterI (outerI (lawMod lc)) (meetI (lawMod lt) (lawMod lf))
        e' = Expr (setPType ti (projectI m)) (IfThenElse c' t' f')
    in doneL (pointOr m e') e' (ca ++ ta ++ fa)

  Expr ti (Lambda x body) ->
    let bodyTy = case rType ti of TArrow _ b -> b; _ -> TFloat
        pctx  = ctx { icPoint = \v -> v == x || icPoint ctx v }
        arr   = IArr gExact (\m -> let (bl,_,_) = inferE pctx (Map.insert x (bareLaw m) env) body in lawMod bl)
        (bodyRepLaw, body', ba) = inferE pctx (Map.insert x (bareLaw (lambdaParamMod ti)) env) body
        bodyRepMod = lawMod bodyRepLaw
        -- What the body's law says whatever the argument ('argumentFree'):
        -- a body that is a known point under the parameter's representative
        -- takes that value for every argument.
        lamJust = case lawJust bodyRepLaw of
          JReturns n r -> JReturns (n + 1) r
          r | Just r' <- argumentFree r -> JReturns 1 r'
            | otherwise -> JUnjustified
    -- The internal modality is the closure 'arr' (so application β-reduces), but
    -- the flat annotation @IRCompiler@ reads is the /body's/ pType, not the outer
    -- closure 'Deterministic' — IRCompiler selects prob/integrate codegen from the
    -- function node's pType (e.g. a top-level @distr x = 2*Uniform+x@ must read
    -- 'Integrate', not the lossy outer 'Deterministic'). Matches @PInfer2@.
    --
    -- Through 'projectNode', not 'projectI': for a curried @f x y = ...@ the
    -- body is itself a lambda, whose /outer/ ground is the Dirac closure, so
    -- 'projectI' read every two-or-more-parameter function as 'Deterministic'
    -- whatever its result was -- and IRCompiler's variant gate then compiled a
    -- probability function for a 'Bottom' body and crashed in it (the
    -- @sim_fpi speed thetas@ repro of task
    -- @continuous-recursive-gate-witness-failure@; the one-parameter twin was
    -- declined cleanly). 'projectNode' recurses down the arrow spine to the
    -- final result, the same way a 'Var' referencing the function is annotated.
    in doneL (Law arr lamJust) (Expr (setPType ti (projectNode bodyTy bodyRepMod)) (Lambda x body')) ba

  Expr ti (Apply f arg) ->
    let (argLaw, arg', aa) = inferE ctx env arg
    in case f of
         -- A directly-applied lambda is a @let@: bind the parameter to the
         -- argument's actual modality (β-reduction with the precise value).
         -- Milestone 2 of @modality-witnessed-inference@: when the binding is
         -- random AND forward chaining certifies the bound variable recoverable
         -- from the declaration's observed result, bind it /witnessed/ — the
         -- body then sees it as Exact-for-marginalization (free, family
         -- preserved) while its standalone law (and density, counted once at its
         -- own slot) is untouched. The capability gate (@gCap /= Exact@) skips
         -- the FC query for deterministic and function-valued bindings.
         -- No engine for a random binding the body reads (task
         -- engine-applicability-as-data): the variable is bound sample-only,
         -- so the body, and the declaration, project 'Bottom' and no
         -- inference variant is promised ('letBinding').
         Expr lti (Lambda x body) ->
           let (_, certs, (bodyLaw, body', ba)) = letBinding ctx env lti x body arg' argLaw
               bodyMod = lawMod bodyLaw
               -- The applied lambda node carries the body's pType (its result),
               -- matching @PInfer2@ and what @IRCompiler@ reads, not the outer
               -- closure 'Deterministic'.
               f' = Expr (setPType lti (projectI bodyMod)) (Lambda x body')
           in doneL bodyLaw (Expr (setPType ti (projectNode (rType ti) bodyMod)) (Apply f' arg'))
                   ((chainName lti, Law (IG gExact) (maybe JUnjustified JBinding certs)) : ba ++ aa)
         -- Any other head -- a named function, a function parameter, a
         -- partial application -- binds its parameter by the same rule: the
         -- witness question is asked of the lambda forward chaining resolves
         -- the head to, for this invocation (task
         -- binding-resolver-one-application-rule). The callee's closure then
         -- sees its parameter witnessed exactly as a literal lambda's body
         -- does. A head that resolves to no lambda is answered unwitnessed.
         --
         -- The engines of that binding are asked at the call too, over the
         -- resolved callee's body ('calleeBindingCerts'), and where none
         -- applies the argument is bound sample-only, as 'letBinding' binds a
         -- literal @draw@'s (task named-callee-binding-not-floored). The
         -- certificates are recorded under 'callBindingKey'. A call whose
         -- result is a known point even so needs no engine (@g z = 0.0 * z@),
         -- as in 'letBinding'.
         _ ->
           let (fLaw, f', fa) = inferE ctx env f
               bound = letBoundLaw ctx (cnOf f) argLaw
               certs0 = calleeBindingCerts ctx env ti f arg' argLaw
               m0 = applyI (lawMod fLaw) (lawMod bound)
               point = isJust (lawValue (applyLaw fLaw m0 (Expr (setPType ti (projectNode (rType ti) m0)) (Apply f' arg'))))
               floored = case certs0 of Just [] -> not point; _ -> False
               m | floored = sampleOnlyOf (rType ti)
                 | otherwise = m0
               e' = Expr (setPType ti (projectNode (rType ti) m)) (Apply f' arg')
               certs | point = Nothing
                     | otherwise = certs0
               certAcc = [ (callBindingKey (cnOf expr), Law (IG gExact) (JBinding cs)) | Just cs <- [certs] ]
           in doneL (applyLaw fLaw m e') e' (certAcc ++ fa ++ aa)

  where
    doneL l e acc = (l, e, (cnOf e, l) : acc)
    done' m = doneL (bareLaw m)

    compareNode ti fname a b =
      let (la, a', aacc) = inferE ctx env a
          (lb, b', bacc) = inferE ctx env b
          g = tagFin ti
                (compareGround (planDependent ctx env a && planDependent ctx env b)
                               (enumerableOperand a) (enumerableOperand b)
                               (independentOperands env a b)
                               (outerI (lawMod la)) (outerI (lawMod lb)))
          e' = Expr (setPType ti (projectGround g)) (InjF (Named fname) [a', b'])
      in doneL (pointOr (IG g) e') e' (aacc ++ bacc)

-- | Can 'collapse' read the mean and variance of this pType-annotated operand,
-- given the values of the local variables it reads? The static twin of
-- 'IRCompiler.momentsOf'; keep the two in step. A part drawing nothing of its
-- own is a point; a mixture needs a condition with a probability and
-- momentable arms; a sum, product or negation needs momentable operands
-- (independent: every draw in one is fresh); a Gaussian is read from its
-- (mu, sigma). @isTop@ names the top-level declarations, which are calls
-- (fresh draws), not given values.
collapseMomentable :: (String -> Bool) -> Expr -> Bool
collapseMomentable isTop e@(Expr ti nd)
  | collapsePoint isTop e = True
  | otherwise = case nd of
      IfThenElse c a b -> pType (getTypeInfo c) `elem` [Deterministic, Integrate] && go a && go b
      InjF (Named n) [a, b] | n `elem` ["plus", "mult"] -> go a && go b
      InjF (Named "neg") [a] -> go a
      _ -> pType ti == PNormal
  where go = collapseMomentable isTop

-- | A part of a 'collapse' operand that draws nothing itself, so is a point
-- given the variables it reads: Deterministic as annotated, or with no
-- primitive draw or neural read and no call to a top-level declaration.
collapsePoint :: (String -> Bool) -> Expr -> Bool
collapsePoint isTop e =
  pType (getTypeInfo e) == Deterministic
    || (not (hasRandomLeaf e) && not (any isTop (Set.toList (freeVarsExpr e))))

-- | The affine form of a scalar value of law @l@ at node @cn@ (design
-- affine-gaussian-forms §3): its certificate if it has one, a constant if it
-- is a point mass, and otherwise, for a Gaussian, one fresh latent keyed by
-- @cn@ -- a leaf, or a Gaussian no rule here sees into (a call, a neural
-- read, a tuple field), which the compiler's scalar extractor answers as a
-- leaf too. 'Nothing' for anything else.
affineOf :: ChainName -> Law -> Maybe AffineCert
affineOf cn (Law m j) = case projectI m of
  Deterministic -> Just constantCert
  PNormal -> Just (case j of
    JAffine c -> c
    _         -> AffineCert (Map.singleton cn Marginal) Map.empty)
  _ -> Nothing

-- | The affine algebra's rules (design affine-gaussian-forms §3): a sum adds
-- per latent, a product with a constant scales, a negation negates. Which
-- coefficients result is the compiler's concern; the latents are this.
-- A latent recovered on either side is recovered.
affineInjF :: String -> [Maybe AffineCert] -> Maybe AffineCert
affineInjF "plus" [Just a, Just b] =
  Just (AffineCert (Map.unionWith max (acLatents a) (acLatents b)) (Map.union (acFactors a) (acFactors b)))
affineInjF "mult" [Just a, Just b]
  | Map.null (acLatents a) = Just b
  | Map.null (acLatents b) = Just a
affineInjF "neg"  [Just a] = Just a
affineInjF _ _ = Nothing

-- | The law of a field constructor over its fields' laws. Its density is a
-- product of factors: each witnessed binding's own density, counted once
-- wherever it is read, and each field's residual density given those. A
-- product is only right when no two factors integrate the same 'Marginal'
-- latent; where two do, the joint law is a multivariate Gaussian, not the
-- product. The structure is then floored to sample-only, with the certificate
-- naming the shared latents ('JSharedLatent'), until affine-gaussian-forms M2
-- gives that joint law an engine.
structuredLaw :: String -> [Law] -> IMod -> Law
structuredLaw fname laws m = case sharedLatents of
  [] -> Law m (JStructured fname laws)
  ks -> Law (sampleOnlyI m) (JSharedLatent fname ks laws)
  where
    (residuals, bindings) = unzip (map densityFactors laws)
    factors = concat residuals ++ Map.elems (Map.unions bindings)
    sharedLatents = Map.keys (Map.filter (> (1 :: Int)) (Map.unionsWith (+)
      [ Map.fromSet (const 1) f | f <- factors ]))

-- | The density factors of a value's law, through structure: the 'Marginal'
-- latents of each scalar part's residual, and those of each witnessed binding
-- read (keyed by the binding, so one read twice is one factor).
densityFactors :: Law -> ([Set.Set ChainName], Map ChainName (Set.Set ChainName))
densityFactors (Law _ j) = case j of
  JAffine c             -> ([marginalsOf c], acFactors c)
  JStructured _ ls      -> fields ls
  JSharedLatent _ _ ls  -> fields ls
  _                     -> ([], Map.empty)
  where fields ls = let (rs, bs) = unzip (map densityFactors ls) in (concat rs, Map.unions bs)

-- | Floor every random part of a modality to (at most) sample-only, keeping
-- its shape so accessors and the fixpoint's comparison still line up.
sampleOnlyI :: IMod -> IMod
sampleOnlyI (IG g)
  | gCap g == Exact = IG g
  | otherwise       = IG (groundMod (meetCap SampleOnly (gCap g)) (gFin g) FamNone)
sampleOnlyI (IProd a b)  = IProd (sampleOnlyI a) (sampleOnlyI b)
sampleOnlyI (ISum t a b) = ISum t (sampleOnlyI a) (sampleOnlyI b)
sampleOnlyI (IRec s e)   = IRec s (sampleOnlyI e)
sampleOnlyI (IWit m)     = sampleOnlyI m
sampleOnlyI m@(IArr _ _) = m

-- | The law of a node no more specific rule justifies: a point mass, with
-- its value where the node's enumeration domain is a single value, or
-- unjustified.
pointOr :: IMod -> Expr -> Law
pointOr m e
  | isPointMass m = Law m (JDirac (staticValue e))
  | otherwise     = Law m JUnjustified

-- | The value of a node known statically: a constant, or a node whose
-- enumeration domain is one value.
staticValue :: Expr -> Maybe Value
staticValue (Expr _ (Constant v)) = Just v
staticValue (Expr ti _) = case [ mv | DiscreteValues mv <- tags ti ] of
  (MultiDiscretes [v] : _) -> Just v
  _ -> Nothing

-- | The law of a call of a head of law @fLaw@ whose result has modality @m@:
-- a callee whose result's justification does not depend on its arguments
-- ('JReturns') gives the call that justification, or, still awaiting
-- arguments, passes the fact on. Any other call is 'pointOr'.
applyLaw :: Law -> IMod -> Expr -> Law
applyLaw fLaw m e = case lawJust fLaw of
  JReturns 1 r@(JDirac _) | isPointMass m -> Law m r
  JReturns 1 r@(JStructured _ _) -> Law m r
  JReturns n r | n > 1, IArr _ _ <- m -> Law m (JReturns (n - 1) r)
  _ -> pointOr m e

-- | The part of a function body's justification, inferred under its
-- parameter's representative, that holds for every argument, where it says
-- anything a call can use ('applyLaw'): a point of known value, or a field
-- constructor. A known value never reads a variable bound at a bare law, so
-- it is the same for every argument. A field's other facts are dropped
-- ('JUnjustified'), which only forgoes them: an affine form or a plan read
-- names nodes of the callee's body, which every call would then share, and
-- the rest are inert at a field. So @h z = (0.0 * z, Normal + 0.0)@ returns a
-- pair whose @fst@ is the point 0.0 and whose @snd@ is unjustified.
argumentFree :: Justification -> Maybe Justification
argumentFree j = case j of
  JDirac (Just _)  -> Just j
  JStructured c ls -> Just (JStructured c (map field ls))
  _                -> Nothing
  where
    field (Law m fj) = Law m (case fj of
      JDirac (Just _)  -> fj
      JStructured c ls -> JStructured c (map field ls)
      _                -> JUnjustified)

-- | The law of a tuple accessor whose operand's law is a pair constructor
-- ('JStructured'), at modality @m0@: a projected field of known value is
-- that point, whatever the other field is (@fst (0.0 * z, Normal)@ is the
-- point 0.0), and a projected pair keeps its fields' laws. Any other field
-- is left to the generic rules ('Nothing').
projectedLaw :: String -> [Law] -> IMod -> Maybe Law
projectedLaw fname laws m0 = field >>= \l -> case l of
  _ | Just v <- lawValue l -> Just (Law (IG gExact) (JDirac (Just v)))
  Law _ j@(JStructured _ _) -> Just (Law m0 j)
  _ -> Nothing
  where
    field = case (fname, laws) of
      ("fst", [Law _ (JStructured "TCons" [a, _])]) -> Just a
      ("snd", [Law _ (JStructured "TCons" [_, b])]) -> Just b
      _ -> Nothing

-- | The value of an 'InjF' every operand of which is a point of known value
-- (@(0.0 * z) + 0.0@ is the point 0.0): its forward function evaluated on
-- those values, as 'SPLL.Analysis' lists a value set. 'Nothing' when an
-- operand's value is unknown or not first-order data, or the forward function
-- does not give exactly one value.
foldedValue :: [ADTDecl] -> String -> [Law] -> Maybe Value
foldedValue adtsDecl fname laws = do
  vs <- mapM lawValue laws
  guard (not (null vs) && all firstOrder vs)
  case propagateValuesLazily adtsDecl fname (map pure vs) of
    [Right v] -> Just v
    _ -> Nothing
  where
    firstOrder v = case v of
      VBool _    -> True
      VInt _     -> True
      VSymbol _  -> True
      VFloat _   -> True
      VUnit      -> True
      VTuple a b -> firstOrder a && firstOrder b
      VEither ab -> either firstOrder firstOrder ab
      VADT _ fs  -> all firstOrder fs
      VList l    -> listFirstOrder l
      _          -> False
    listFirstOrder l = case l of
      EmptyList     -> True
      ListCont x xs -> firstOrder x && listFirstOrder xs
      AnyList       -> False

-- | The value a law certifies its node to take, when it is a point mass whose
-- value is known statically ('JDirac').
lawValue :: Law -> Maybe Value
lawValue (Law _ (JDirac v)) = v
lawValue _ = Nothing

-- | The law an application binds its parameter to, given the argument's law
-- and the chain name of the head (a literal lambda, or a callee forward
-- chaining resolves to one): witnessed when the binding is random and forward
-- chaining certifies it recoverable from the observation (see the 'Apply' rule
-- of 'inferE'). The justification is the argument's. A head forward chaining
-- never saw -- a node 'reinferGiven' synthesized -- is not asked.
letBoundLaw :: ICtx -> ChainName -> Law -> Law
letBoundLaw ctx headCN argLaw@(Law argMod j)
  | gCap (outerI argMod) /= Exact
  , isJust (Map.lookup headCN (chainNameInfo (icFC ctx)))
  , icWitnessed ctx headCN = Law (iwit argMod) j
  | otherwise = argLaw

-- | The one binder-environment extension of an application: the parameter
-- @x@ of the lambda the head (chain name @headCN@) resolves to is bound to
-- the argument's law, witnessed where 'letBoundLaw' says so. 'inferE''s
-- @draw@/let rule, 'envAt' and the compiler's @lawEnv@ ('bindingLawEnv') all
-- extend through it, so the three cannot disagree on what a binder means.
--
-- A Gaussian argument binds at its affine certificate ('affineOf' at the
-- argument's chain name), so every read of @x@ carries the same latent keys.
-- A witnessed binding is instead one 'Recovered' latent keyed by the
-- argument: the observation determines @x@. Its density, which integrates
-- the argument's 'Marginal' latents, is recorded as its factor
-- ('acFactors'). Any other argument that projects from a plan read binds at
-- 'JPlan' ('planRoots').
bindParam :: ICtx -> ChainName -> String -> Expr -> Law -> Env -> Env
bindParam ctx headCN x arg argLaw env = Map.insert x (affineBound (letBoundLaw ctx headCN argLaw)) env
  where
    argCN = cnOf arg
    affineBound l@(Law m _) = case affineOf argCN argLaw of
      Just c | not (Map.null (acLatents c)) -> Law m (JAffine (if isWitI m then recovered c else c))
      _ | not (null roots) -> Law m (JPlan roots)
        | otherwise -> l
    recovered c = AffineCert (Map.singleton argCN Recovered) (Map.insert argCN (marginalsOf c) (acFactors c))
    roots = planRoots ctx env arg

-- | The plan reads a value projects from: itself, if it is one or a field
-- accessor chain over one ('SPLL.AutoNeural.planProjectedReadOf'), and those of every variable it reads that
-- is bound at 'JPlan', or at an affine form one of whose latents is a plan
-- read (a Float network's output). Empty for a value that reads no network's
-- output through a binding.
planRoots :: ICtx -> Env -> Expr -> [ChainName]
planRoots ctx env e = Set.toList (Set.fromList ([ cnOf r | Just (_, _, _, r) <- [planProjectedReadOf (icProg ctx) e] ] ++ boundPlanRoots ctx env e))

-- | The plan reads an expression projects from through the variables it
-- reads ('planRoots' without the expression itself).
boundPlanRoots :: ICtx -> Env -> Expr -> [ChainName]
boundPlanRoots ctx env e = concatMap fromVar (Set.toList (freeVarsExpr e))
  where
    fromVar v = case Map.lookup v env of
      Just (Law _ (JPlan rs))  -> rs
      Just (Law _ (JAffine c)) -> filter (`Set.member` icPlanReads ctx) (Map.keys (acLatents c))
      _                        -> []

-- | Does a comparison operand project from a plan read through a binding
-- ('boundPlanRoots')? A plan read in place, bound by nothing, does not count:
-- the plan-guided engine inverts a binding.
planDependent :: ICtx -> Env -> Expr -> Bool
planDependent ctx env = not . null . boundPlanRoots ctx env

-- | The chain names of a program's plan reads.
planReadCNs :: Program -> Set.Set ChainName
planReadCNs prog = Set.fromList [ cnOf e | (_, b) <- functions prog, e <- universe b
                                         , isJust (planReadOf prog e) ]
  where universe e = e : concatMap universe (getSubExprs e)

-- | The @let@ rule: bind @x@ (the parameter of the literal lambda @lti@) to
-- the argument, and infer the body under it. Answers the extended
-- environment, the engine certificates where the binding is random and its
-- value read ('bindingCerts'), and the body's inference.
--
-- A random binding the body reads that no engine handles is bound
-- sample-only instead (design law-carrying-modality §F): the body is
-- re-inferred under that, so it, and the declaration, project 'Bottom', and
-- the compiler promises no inference variant it cannot compile. The
-- predicates are the engines' own applicability, so the floor cannot
-- foreclose an engine; where an engine's applicability is fused with its IR
-- construction, the predicate is its necessary condition and the
-- compiler's refusal stays the net.
letBinding :: ICtx -> Env -> TypeInfo -> String -> Expr -> Expr -> Law -> (Env, Maybe [EngineCert], (Law, Expr, GAcc))
letBinding ctx env lti x body arg argLaw
  | needsEngine, null certs = (floored, Just certs, inferE bctx floored body)
  | needsEngine, (CertJointAffine _ : _) <- certs = (jointEnv, Just certs, inferE bctx jointEnv body)
  | needsEngine = (env1, Just certs, inferred)
  | otherwise = (env1, Nothing, inferred)
  where
    env1 = bindParam ctx (chainName lti) x arg argLaw env
    -- The joint affine engine answers the binding: the latents the argument
    -- draws itself are integrated by it ('Joint'). Those it reads through
    -- another variable keep their recovery, so a sharing outside this body
    -- is still seen.
    jointEnv = Map.adjust jointLatents x env1
    outerLatents = Set.unions [ Map.keysSet (acLatents c) | v <- Set.toList (freeVarsExpr arg)
                                                          , Just (Law _ (JAffine c)) <- [Map.lookup v env] ]
    jointLatents (Law m (JAffine c)) =
      Law m (JAffine c { acLatents = Map.mapWithKey (\k r -> if r == Marginal && not (k `Set.member` outerLatents) then Joint else r) (acLatents c) })
    jointLatents l = l
    inferred@(bodyLaw, body', _) = inferE bctx env1 body
    -- Read only by a call in the body, so solved only there. The engines'
    -- applicability, read before the body is annotated (the certificates
    -- read the annotated body), and loosely: an enumerable argument, not
    -- also a conditional body ('enumerableApplication' walks the body,
    -- which made a let chain's calls quadratic in its length).
    bctx = ctx { icPoint = \v -> if v == x then pointBound else icPoint ctx v }
    pointBound = isJust (enumerableDomain (tags (getTypeInfo arg)))
              || isJust (planProjectedReadOf (icProg ctx) arg)
              || isJust (toInvExprMaybeWith (const True) (const True) (icFC ctx) (icADTs ctx) (chainName lti))
    needsEngine = gCap (outerI (lawMod argLaw)) /= Exact
               && not (isArrow (rType (getTypeInfo arg)))
               && x `Set.member` freeVarsExpr body
               && not (determinedByWitnesses env arg)
               -- A body whose law is a known point (@0.0 * z@) takes that
               -- value whatever the variable draws: nothing reads the
               -- variable's value, so no engine needs to apply.
               && not (isJust (lawValue bodyLaw))
    lam' = Expr (setPType lti (projectI (lawMod bodyLaw))) (Lambda x body')
    certs = bindingCerts ctx lam' arg argLaw
    floored = Map.adjust (\(Law m _) -> Law (sampleOnlyI m) JUnjustified) x env1
    isArrow (TArrow _ _) = True
    isArrow _ = False

-- | The law of a call whose binding no engine applies to: sample-only in
-- every part. Not the callee's closure applied to a sample-only argument,
-- which would keep the parts that do not read it: inside a recursive
-- component that application reads the previous iterate's closures, so the
-- fixpoint, seeded at the top, took an iteration more to converge for every
-- floored call, and each iteration's closures apply the last one's, which is
-- exponential in their number (@canFinish@ in TestInternals'
-- @modalityThreadedBoolParamsGrowth@ went from 3s to over a minute).
sampleOnlyOf :: RType -> IMod
sampleOnlyOf rt = case rt of
  Tuple a b   -> IProd (sampleOnlyOf a) (sampleOnlyOf b)
  TEither a b -> ISum g (sampleOnlyOf a) (sampleOnlyOf b)
  ListOf a    -> IRec g (sampleOnlyOf a)
  TTensor _ a -> IRec topGround (sampleOnlyOf a)
  TArrow _ b  -> IArr topGround (const (sampleOnlyOf b))
  _           -> IG g
  where g = groundMod SampleOnly Infinite FamNone

-- | The key a named callee's binding records its engine certificates under
-- in the 'LawTable': the call's own chain name carries the call's law, so the
-- binding's ('JBinding') goes beside it.
callBindingKey :: ChainName -> ChainName
callBindingKey cn = cn ++ "#binding"

-- | The engine certificates of the binding a call of a named callee (any
-- head that is not a literal lambda) makes: forward chaining resolves the
-- head to a lambda, whose parameter the argument binds
-- ('IRCompiler.resolveBinding'). 'Nothing' where the binding needs no engine,
-- on the same conditions as 'letBinding' (a point argument, a function
-- value, a dead or witness-determined binding; the caller checks a result
-- that is a known point), and where the head resolves to no lambda; also for
-- a partial application, whose random leading argument the compiler binds by
-- its own rule ('IRCompiler.leadingArgBinding').
--
-- The callee's body is the one written, not the copy this call binds, and
-- is not re-inferred here: a recursive callee would re-enter itself, and its
-- law is answered by its greatest-fixpoint summary through the closure the
-- head evaluates to. So each predicate is the engine's necessary condition,
-- read permissively (every value the body reads may be a known point), and
-- the compiler's refusal stays the net where it holds and the construction
-- still fails. Where even that admits no engine, no construction can.
calleeBindingCerts :: ICtx -> Env -> TypeInfo -> Expr -> Expr -> Law -> Maybe [EngineCert]
calleeBindingCerts ctx env ti f arg argLaw
  -- Syntactic tests first: the argument's law is a thunk the callee's
  -- closure may never force, and forcing it at every call a closure
  -- re-evaluates cost the recursive canFinish of TestInternals'
  -- modalityThreadedBoolParamsGrowth a third of its compile time.
  | isArrow (rType ti) || isArrow (rType (getTypeInfo arg)) = Nothing
  -- An argument that draws nothing fresh: random only through variables
  -- the compiler holds at a point here ('icPoint'), or witnessed ones. A
  -- caller that passes a random argument to an enclosing closure has its own
  -- binding, at its own call, which floors where no engine applies, and
  -- where one does the compiler evaluates this body at the recovered value,
  -- through the callee's own inference function ('IRCompiler.namedCall'):
  -- @h (k - 0.25)@ in @h k = if k < 0.25 then Normal else 1.0 + h (k - 0.25)@,
  -- whose @k@ the @if@'s arm no longer reads witnessed ('conditionI'). Same
  -- for a @draw@'s variable that point inversion recovers from the body's
  -- value without the declaration's observation reaching it (@gen (snd e)@
  -- in data-structures/anyMarkPassedAsRecursiveState). A call in the argument
  -- draws whatever its callee draws, which 'hasRandomLeaf' does not see.
  | not (hasRandomLeaf arg)
  , all pinned (Set.toList (freeVarsExpr arg)) = Nothing
  | gCap (outerI (lawMod argLaw)) == Exact = Nothing
  | otherwise = do
      syn <- maybe (calleeSyntax ctx headCN) id (LMap.lookup headCN (icCallSyntax ctx))
      Just (mapMaybe (certOf syn) engineOrder)
  where
    headCN = cnOf f
    pinned v
      | icPoint ctx v = True
      | isJust (lookup v (functions (icProg ctx))) = False
      | otherwise = maybe True (inputIsPoint . lawMod) (Map.lookup v env)
    certOf syn k = case k of
      -- The compiler enumerates a call's argument on several paths (a
      -- conditional callee, a curried one, a leading argument), each over
      -- the argument's domain.
      EnumerationEngine    -> CertEnumerable <$> enumerableDomain (tags (getTypeInfo arg))
      PlanEngine           -> CertPlan <$> listToMaybe (planRoots ctx env arg)
      PointInversionEngine -> (\chain -> CertWitnessed (WitnessCert chain (icWitnessed ctx headCN))) <$> csPoint syn
      AffineEngine         -> CertAffine <$> (guard (csInline syn) >> latentForm)
      JointAffineEngine    -> CertJointAffine <$> (guard (csInline syn) >> latentForm)
      WorldsEngine         -> CertWorlds <$> csWorlds syn
      InPlaceEngine        -> if csInPlace syn then Just CertInPlace else Nothing
    latentForm = case affineOf (cnOf arg) argLaw of
      Just c | not (Map.null (acLatents c)) -> Just c
      _ -> Nothing
    isArrow (TArrow _ _) = True
    isArrow _ = False

-- | What a named callee's binding has for engines whatever its argument's
-- law ('calleeBindingCerts'), for the call whose head has chain name
-- @headCN@: 'Nothing' where the head resolves to no lambda, or to one whose
-- body does not read its parameter (a dead binding, which needs no engine).
data CallSyntax = CallSyntax
  { csPoint   :: Maybe InvChain
  , csWorlds  :: Maybe WorldsShape
    -- | The body is compiled inline at the call: not a copy made per
    -- invocation, and not a top-level function's, which may be recursive
    -- ('IRCompiler.bindInline'). The affine and in-place engines need it.
  , csInline  :: Bool
  , csInPlace :: Bool
  }

calleeSyntax :: ICtx -> ChainName -> Maybe CallSyntax
calleeSyntax ctx headCN
  | isNothing (Map.lookup headCN (chainNameInfo fc)) = Nothing
  | otherwise = case findEquivalentExpression fc headCN of
      Just (lamCN, LambdaInfo x _, tag)
        | Just (Expr _ (Lambda _ body)) <- Map.lookup (untag lamCN) (icNodes ctx)
        , occs@(_ : _) <- Map.findWithDefault [] (untag lamCN) (lambdaVarOccurrences fc)
        , let inline = null tag && not (onTopSpine (untag lamCN))
        -> Just CallSyntax
             { csPoint = toInvExprMaybeWith (const True) (const True) fc (icADTs ctx) headCN
             , csWorlds = worldsShape (WorldsCtx fc (icADTs ctx) (functions prog) (const True)) occs body
             , csInline = inline
             , csInPlace = inline && readOnceInPlace x body }
      _ -> Nothing
  where
    fc = icFC ctx
    prog = icProg ctx
    onTopSpine cn = any (spineHas cn . snd) (functions prog)
    spineHas cn e@(Expr _ (Lambda _ b)) = cnOf e == cn || spineHas cn b
    spineHas _ _ = False

-- | Is a value a function of witnessed variables alone: it draws nothing
-- fresh itself, and every variable it reads is a point or witnessed? The
-- compiler recovers a witnessed variable from the observation before it
-- reaches a binding of such a value, which is then deterministic there and
-- needs no engine of its own (@draw y = x in ...@ with @x@ witnessed).
determinedByWitnesses :: Env -> Expr -> Bool
determinedByWitnesses env arg = not (hasRandomLeaf arg) && all pinned (Set.toList (freeVarsExpr arg))
  where pinned v = case Map.lookup v env of
          Just (Law m _) -> inputIsPoint m
          Nothing -> True

-- | Is a value a point once every witnessed variable it reads is fixed at
-- its recovered value? 'IWit' marks only a deterministic image of /one/
-- witnessed operand, so a value that combines witnessed operands --
-- @head zs + head (tail zs)@, an @if@ whose condition reads them
-- (@if isNull (tail zs) then head zs else ...@), a recursive helper walking a
-- witnessed list (@lastOf zs@) -- is not marked witnessed, although the
-- observation determines it. A neural read's input asks the stronger
-- question: the value is re-inferred with each witnessed variable it reads
-- bound to a point, and a Deterministic result is a point given the
-- observation (task neural-read-at-recursive-walk-of-observed-list-no-code).
-- Calls go through the callees' own summaries, so a helper that draws fresh
-- randomness still answers random.
pointGivenWitnesses :: ICtx -> Env -> Expr -> Bool
pointGivenWitnesses ctx env e
  | null wits = False
  | otherwise = let (l, _, _) = inferE ctx pinnedEnv e in gCap (outerI (lawMod l)) == Exact
  where
    wits = [ v | v <- Set.toList (freeVarsExpr e)
               , Just (Law m _) <- [Map.lookup v env], isWitI m ]
    pinnedEnv = foldr (\v -> Map.insert v (bareLaw (IG gExact))) env wits

-- | The certificates of the engines that apply to a random binding: the
-- literal lambda @lam@ (its body annotated) applied to @arg@, of law
-- @argLaw@, in dispatch order ('engineOrder'). Lazy, so asking whether any applies evaluates the predicates
-- only up to the first that does.
bindingCerts :: ICtx -> Expr -> Expr -> Law -> [EngineCert]
bindingCerts ctx lam arg argLaw = mapMaybe certOf engineOrder
  where
    certOf k = case k of
      EnumerationEngine    -> CertEnumerable <$> enumerableApplication fc prog lam arg
      PlanEngine           -> (\(n, _, _, _) -> CertPlan n) <$> planProjectedReadOf prog arg
      PointInversionEngine -> CertWitnessed <$> pointWitnessCert pointValue fc (icADTs ctx) (icObs ctx) lamCN
      AffineEngine         -> CertAffine <$> affineBindingCert x arg argLaw body
      JointAffineEngine    -> CertJointAffine <$> jointAffineBindingCert x arg argLaw body
      WorldsEngine         -> CertWorlds <$> worldsShape (WorldsCtx fc (icADTs ctx) (functions prog) permissiveDet) occs body
      InPlaceEngine        -> if readOnceInPlace x body then Just CertInPlace else Nothing
    fc = icFC ctx
    prog = icProg ctx
    lamCN = cnOf lam
    (x, body) = case lam of
      Expr _ (Lambda v b) -> (v, b)
      _ -> error "bindingCerts: the head of a let is a lambda"
    occs = maybe [] id (Map.lookup lamCN (lambdaVarOccurrences fc))
    -- A let value inside the body is a known point where its law, inferred
    -- in the body, is Deterministic.
    pointValue cn = Map.lookup cn bodyPTypes == Just Deterministic
    bodyPTypes = Map.fromList [ (chainName ti, pType ti) | Expr ti _ <- universeE body ]
    universeE e = e : concatMap universeE (getSubExprs e)

-- | The affine collapse's certificate for binding @x@ to @arg@ over @body@:
-- the argument's affine form ('affineOf'), when it has latents and every
-- occurrence of @x@ flows into one affine consumer -- the value of a directly
-- nested binding, or the let spine's terminal expression. That is
-- @IRCompiler.affineMarginalisable@'s shape check, read syntactically: a part
-- @x@ does not reach is admitted when it is Gaussian, deterministic or draws
-- nothing fresh, and a call is admitted, since only the compile in scope can
-- enter it.
affineBindingCert :: String -> Expr -> Law -> Expr -> Maybe AffineCert
affineBindingCert x arg argLaw body = case affineOf (cnOf arg) argLaw of
  Just c | not (Map.null (acLatents c)), not (isArrow (rType (getTypeInfo body))), spineOK body -> Just c
  _ -> Nothing
  where
    vFree = freeVarsExpr arg
    readsX e = x `Set.member` freeVarsExpr e
    spineOK (Expr _ (Apply lam@(Expr _ (Lambda y inner)) val))
      | readsX val = not (readsX lam) && shaped val
      | y == x || y `Set.member` vFree = False
      | otherwise = spineOK inner
    spineOK t = readsX t && shaped t
    quiet e = pType (getTypeInfo e) `elem` [Deterministic, PNormal] || not (hasRandomLeaf e)
    constant e = not (readsX e) && (pType (getTypeInfo e) == Deterministic || not (hasRandomLeaf e))
    shaped e
      | not (readsX e) = quiet e
      | otherwise = case e of
          Expr _ (Var n) -> n == x
          Expr _ (Apply _ _) -> True
          Expr _ (InjF (Named "plus") [a, b]) -> shaped a && shaped b
          Expr _ (InjF (Named "mult") [a, b]) -> (constant a && shaped b) || (constant b && shaped a)
          Expr _ (InjF (Named "neg") [a]) -> shaped a
          _ -> False
    isArrow (TArrow _ _) = True
    isArrow _ = False

-- | The joint affine engine's certificate for binding @x@ to @arg@ over
-- @body@ (design affine-gaussian-forms M2): the argument's affine form, when
-- it has latents and the body is a let spine of affine bindings ending in a
-- field tree of tuples. Every binding on the spine whose value reads a
-- variable of the spine (@x@ included) must be affine over them, as must
-- every tuple field that reads one; at most 'jointAffineMaxSlots' fields do.
-- The fields that read none are independent factors, measured as usual. The
-- engine integrates the spine's latents once, as one multivariate Gaussian
-- over the affine fields, which is what makes two fields sharing a latent
-- correlated rather than a reason to floor: 'letBinding' rebinds the
-- argument's fresh latents 'Joint'. @IRCompiler.jointAffineApplicable@ is the
-- compiler's twin; keep the two in step.
jointAffineBindingCert :: String -> Expr -> Law -> Expr -> Maybe AffineCert
jointAffineBindingCert x arg argLaw body = case affineOf (cnOf arg) argLaw of
  Just c | not (Map.null (acLatents c)), not (isArrow (rType (getTypeInfo body)))
         , spine (Set.singleton x) (freeVarsExpr arg) body -> Just c
  _ -> Nothing
  where
    -- @bound@: the free variables of the values met so far, which a later
    -- binder must not shadow (their forms are read at the fields).
    spine names bound (Expr _ (Apply (Expr _ (Lambda y inner)) val))
      | y `Set.member` names || y `Set.member` bound = False
      | otherwise = shaped names val
          && spine (Set.insert y names) (bound `Set.union` freeVarsExpr val) inner
    spine names _ t =
      let affine = filter (readsAny names) (tupleFields t)
      in not (null affine) && length affine <= jointAffineMaxSlots && all (shaped names) affine
    tupleFields (Expr _ (InjF (Named "TCons") [a, b])) = tupleFields a ++ tupleFields b
    tupleFields t = [t]
    readsAny names e = not (Set.null (freeVarsExpr e `Set.intersection` names))
    constant names e = not (readsAny names e) && (pType (getTypeInfo e) == Deterministic || not (hasRandomLeaf e))
    shaped names e
      | not (readsAny names e) = pType (getTypeInfo e) `elem` [Deterministic, PNormal] || not (hasRandomLeaf e)
      | otherwise = case e of
          Expr _ (Var n) -> n `Set.member` names
          Expr _ (Apply _ _) -> isCall e
          Expr _ (InjF (Named "plus") [a, b]) -> shaped names a && shaped names b
          Expr _ (InjF (Named "mult") [a, b]) -> (constant names a && shaped names b) || (constant names b && shaped names a)
          Expr _ (InjF (Named "neg") [a]) -> shaped names a
          _ -> False
    isCall (Expr _ (Apply f _)) = isCall f
    isCall (Expr _ (Var _)) = True
    isCall _ = False
    isArrow (TArrow _ _) = True
    isArrow _ = False

-- | The most tuple fields the joint affine engine measures as one
-- multivariate Gaussian (design affine-gaussian-forms §6, "Rank"). Each
-- field may be observed or @ANY@, and the engine compiles one density per
-- observed subset, so the emitted code grows as @2^n@.
jointAffineMaxSlots :: Int
jointAffineMaxSlots = 3

-- | The law a free-standing lambda binds its parameter to: the representative
-- of the parameter's type. Shared with 'envAt'.
lambdaParamMod :: TypeInfo -> IMod
lambdaParamMod ti = repIMod (case rType ti of TArrow a _ -> a; _ -> TFloat)

-- | The law a free-standing lambda's parameter is bound to: the
-- representative of its type, as 'inferE''s 'Lambda' rule binds it.
lambdaParamLaw :: TypeInfo -> Law
lambdaParamLaw = bareLaw . lambdaParamMod

-- | 'bindParam' for a caller outside the walk -- the compiler, extending its
-- @lawEnv@ at a binding. The inference context is that of the declaration
-- holding the head, as in 'inferE'. A head in no declaration (a synthesized
-- node) is one forward chaining never saw, which 'letBoundLaw' does not ask
-- either, so the binding is unwitnessed.
bindingLawEnv :: ReinferCtx -> ChainName -> String -> Expr -> Law -> Env -> Env
bindingLawEnv rc headCN = bindParam ctx headCN
  where
    ctx = case find (containsCN . snd) (rcDecls rc) of
      Just (_, b) -> mkICtx (rcADTs rc) (rcFC rc) (cnOf b) (rcProg rc)
      Nothing     -> mkICtx (rcADTs rc) (rcFC rc) headCN (rcProg rc)
    containsCN e = cnOf e == headCN || any containsCN (getSubExprs e)

-- | The environment an @if@'s arms are inferred under: every let-bound random
-- variable the condition reads is rebound to its law /conditioned on the
-- condition's outcome/ ('conditionI').
--
-- Inside @let v = Normal in if v < b then x else y@, the @v@ that @x@ sees is
-- not a Normal: it is the Normal's negative part, a truncated distribution
-- (and @y@ sees the positive part). A truncation keeps every query
-- capability the standalone law had -- a density that is the original one
-- restricted and renormalised, a CDF that is the original one shifted and
-- rescaled -- but it is a different law, of no closed family. Binding the
-- arm occurrences at the standalone law instead let 'tryNormalClosure' type
-- @v + Normal@ inside the arm as 'PNormal' and admit a program no engine can
-- compile (the sum of a truncated Normal and a Normal is neither Gaussian nor
-- anything the set-witness engine can invert onto @v@): task
-- @continuous-recursive-gate-witness-failure@. The same holds for a
-- condition that constrains @v@ in any other way -- @f v@, @v * v < 1@,
-- @v < w@ -- which is why the refinement keys off the condition's free
-- variables rather than off the @v < bound@ spelling.
--
-- Only /random/ bindings are conditioned: a deterministic condition
-- partitions nothing (there is one value), and a Dirac law is unchanged by
-- restriction. Variables the condition does not read are untouched -- their
-- law is independent of the outcome. The condition itself is inferred under
-- the unrefined environment.
conditionEnv :: Env -> Expr -> Env
conditionEnv env c = foldr refine env (Set.toList (freeVarsOf c))
  where refine v e = case Map.lookup v e of
          Just l | gCap (outerI (lawMod l)) /= Exact -> Map.insert v (provenance l (bareLaw (conditionI (lawMod l)))) e
          _                                          -> e
        -- Which plan reads a value projects from survives conditioning: it is
        -- where the value comes from, not its law.
        provenance (Law _ (JPlan rs)) (Law m _) = Law m (JPlan rs)
        provenance _ l = l

-- | A law restricted to the event some condition on its value holds. The
-- capability set survives (restriction preserves having a density / CDF /
-- being samplable), and so does support finiteness (a subset of a finite
-- support is finite); what is lost is
--
--   * the distribution __family__ -- the restriction of a Normal to a
--     half-line is not a Normal, so the family closures must not fire on it;
--   * the __witness__ flag -- 'IWit' says the observation determines the value
--     on every path; inside one arm it does so only if /that arm/ recovers it,
--     and the free-Exact treatment a witnessed operand gets in 'floorCombine'
--     is exactly what admitted @v + Normal@ in an arm that does not.
--
-- Applied structurally: a conditioned tuple's fields are conditioned (the
-- event is on the whole value, so no field's family survives either).
conditionI :: IMod -> IMod
conditionI (IWit m)      = conditionI m
conditionI (IG g)        = IG g { gFam = FamNone }
conditionI (IProd a b)   = IProd (conditionI a) (conditionI b)
conditionI (ISum t a b)  = ISum t { gFam = FamNone } (conditionI a) (conditionI b)
conditionI (IRec s e)    = IRec s { gFam = FamNone } (conditionI e)
conditionI m@(IArr _ _)  = m   -- a function has no law to restrict

-- | The free variables of an expression: 'Var' occurrences not bound by an
-- enclosing 'Lambda' within it. ('containedVars' does not see binders.)
freeVarsOf :: Expr -> Set.Set String
freeVarsOf (Expr _ (Var v))       = Set.singleton v
freeVarsOf (Expr _ (Lambda x b))  = Set.delete x (freeVarsOf b)
freeVarsOf (Expr _ f)             = foldr (Set.union . freeVarsOf) Set.empty f

-- | Does this operand carry a domain the enumerate-both grid can loop over
-- ('SPLL.Analysis.enumerableDomain', the predicate @IRCompiler.isEnumerable@
-- also reads)? The same fact as @gFin == Finite@ on the operand's own tags,
-- asked of the operand directly because the operand's ground 'Fin' may have
-- come from a combination rule rather than its tag.
enumerableOperand :: Expr -> Bool
enumerableOperand = isJust . enumerableDomain . tags . getTypeInfo

-- | Do two comparison operands read no random local in common? Under SPLL's
-- eager @draw@ every fresh draw in one operand is independent of every draw in
-- the other, so a variable bound to a random law in the enclosing scope is the
-- only way the two can be correlated. Deterministic bindings (a parameter, a
-- recovered or enumerated variable re-inferred 'Exact') correlate nothing.
independentOperands :: Env -> Expr -> Expr -> Bool
independentOperands env a b = not (any randomLocal (Set.toList shared))
  where shared = Set.intersection (freeVarsOf a) (freeVarsOf b)
        randomLocal v = case Map.lookup v env of
          Just l -> gCap (outerI (lawMod l)) /= Exact
          Nothing -> False

-- | Comparison (@>@\/@<@): the Boolean result is a Bernoulli (finite support).
-- @plan@ says both operands project from plan reads through bindings
-- ('planDependent'); @enumA@\/@enumB@ say whether the left\/right operand is
-- enumerable ('enumerableOperand').
--
-- The capability rung is decided by whether a closed form for /this pair of
-- operands/ exists, not by whether each operand separately owns a CDF. Owning a
-- CDF each says nothing about the law of the difference: @Uniform > exp(Uniform)@
-- has two 'DensInt' operands and no closed-form answer at all. Claiming 'DensInt'
-- there typed the node 'Integrate', which sent 'toIRInference' looking for an
-- equation that does not exist and out the other side as the catch-all
-- @error "found no way to convert to IR"@ -- a compiler crash on a well-typed
-- program (task @ircompiler-integrate-comparison-no-conversion-crash@; the same
-- over-promise, one rung up, as the 'IntegralOnly' note below).
--
-- 'SampleOnly' is the honest answer for the rest: the program still compiles and
-- still gets its @generate@ function, and a probability query is declined with a
-- message naming the mode instead of taking the process down.
--
-- The closed forms admitted here each mirror one engine of @IRCompiler@, and
-- this list must not outrun those:
--
--   * __one side 'Exact'__ — the random side's own CDF evaluated at the fixed
--     bound (@fixed_bound@\/@rhs_integral@\/@lhs_integral@).
--   * __both sides Gaussian__ — the difference is Gaussian, so the answer is its
--     CDF at zero (@normalDiffCdfAtZero@). 'FamNormal' specifically, not merely
--     equal families: two 'FamLogNormal' operands enjoy no such closure and
--     IRCompiler has no equation for them.
--   * __both sides enumerable__ — the forward-only @|L|x|R|@ grid, which reads
--     the operands' 'DiscreteValues' tags, hence the flags.
--   * __one side enumerable, the operands independent__ — a Bernoulli whose
--     rate is itself random (@Uniform < (if b then 0.9 else 0.1)@): the sum
--     over the enumerable side's domain of its mass times the other side's
--     CDF at that value (@enumerated_bound@). Independence is what makes the
--     sum a product of the two operands' own laws: @indep@
--     ('independentOperands') says no random local is read by both. A shared
--     one (@draw t = .. in (Uniform + t) < t@) correlates them, and no
--     equation measures that (task uniform-below-random-threshold-no-forward).
--   * __both sides projecting from plan reads__ — the plan-guided engine
--     measures a pairwise comparison of two continuous leaves of a neural
--     plan by that same difference Gaussian (@planEnumContPair@), but the
--     leaves reach the comparison as @fst p@\/@snd p@ off a @let@-bound
--     neural read, and by then their Gaussian family is gone from the flat
--     ground. What the engine needs is the plan certificate of the binding
--     each operand projects from (a 'JPlan' binder, or an affine form over a
--     plan read: 'planDependent'), which is that engine's own predicate
--     ('SPLL.AutoNeural.planReadOf'). Its per-node support is fused with its
--     IR construction, so it is the necessary condition, and the compiler's
--     refusal stays the net (task engine-applicability-as-data, closing
--     @comparison-closed-form-verdict-for-plan-leaves@'s coarse
--     declaration-wide flag).
compareGround :: Bool -> Bool -> Bool -> Bool -> GroundMod -> GroundMod -> GroundMod
compareGround plan enumA enumB indep a b
  | gCap a == Exact && gCap b == Exact = groundMod Exact        Finite FamNone
  | closedForm                         = groundMod DensInt      Finite FamNone
  | canSample a && canSample b         = groundMod SampleOnly   Finite FamNone
  | otherwise                          = groundMod Opaque       Finite FamNone
  -- 'DensInt'/'Exact' are the only ground states with a real, usable CDF here.
  -- 'IntegralOnly' (bare {S,I}) was a degenerate byproduct of 'marginalize'
  -- combining two infinite-support operands (task
  -- marginalize-keepi-overclaims-integral-for-generic-mult removed that
  -- grant) -- it is NOT a genuine "integral without density" capability;
  -- 'projectGround' itself maps it to 'Bottom' for exactly this reason
  -- ("held unreachable, would overpromise"). A naive @leqCap IntegralOnly
  -- (gCap g)@ check is trivially true whenever @gCap g == IntegralOnly@
  -- (reflexivity of the subset order), so it wrongly accepted this degenerate
  -- state as CDF-ready and produced a spurious 'Integrate' comparison result
  -- for e.g. @Normal*c > Uniform+Normal@ instead of 'Bottom'.
  where okInt g     = gCap g == DensInt || gCap g == Exact
        canSample g = leqCap SampleOnly (gCap g)
        closedForm  = okInt a && okInt b
                   && (  plan
                      || gCap a == Exact || gCap b == Exact
                      || (gFam a == FamNormal && gFam b == FamNormal)
                      || (enumA && enumB)
                      || (indep && (enumA || enumB)) )

-- | Modality of an 'InjF' application. Resolution order:
--
--   1. the family-preserving operators keep 'PNormal'/'PLogNormal': an affine
--      operator with an affine form (@gaussian@, decided by 'affineInjF' in
--      'inferE') is 'PNormal', and 'tryNormalClosure' lists the log-normal
--      ones;
--   2. field constructors (tuples / @Cons@ / user-ADT, ≥2 fields) build a
--      structured 'IProd' so the projection is the meet of independent fields
--      and accessors can later recover a single field;
--   3. the tuple accessors @fst@/@snd@ project a component of an 'IProd';
--   4. everything else marginalises its operands (the generic combination
--      floor); a unary invertible map is the singleton case and passes its
--      operand through, family intact.
--
-- Witnessed operands (milestone 2 of @modality-witnessed-inference@) change the
-- floor's per-operand treatment — see 'floorCombine'. A closure/floor result is
-- itself witnessed exactly when it is a deterministic function of a /single/
-- witnessed operand (everything else Dirac): the once-counting ledger stays
-- positional (that one latent's density is the result's standalone law, counted
-- once). A combination of two or more witnessed operands keeps a random
-- capability but is NOT re-marked witnessed (the value is an image of several
-- latents, not one; the codegen let-fold pays each latent at its own binding,
-- which also covers the same-latent shape without a ledger identity). Any
-- fresh latent beyond one in the combination floors the result — that is what
-- keeps the two-residual guard at 'Bottom'.
injFMod :: [ADTDecl] -> String -> Bool -> [IMod] -> IMod
injFMod adtsDecl name gaussian mods =
  case (if gaussian then Just PNormal else tryNormalClosure name (map projectI mods)) of
    Just pt -> witWrap (IG (fromClosurePType pt))
    Nothing
      | isFieldConstructor adtsDecl name, (m0:rest) <- mods -> foldl IProd m0 rest
      | name == "fst", [m] <- mods -> projFst m
      | name == "snd", [m] <- mods -> projSnd m
      | otherwise -> keepFamilyIf familyPreserved floorCombine
  where projFst (IWit m)    = iwit (projFst m)   -- a witnessed pair's field is witnessed
        projFst (IProd a _) = a
        projFst m           = m
        projSnd (IWit m)    = iwit (projSnd m)
        projSnd (IProd _ b) = b
        projSnd m           = m

        entries = [ (isWitI m, outerI m) | m <- mods ]
        -- witnessed random operands / fresh (unwitnessed) random operands
        wits    = [ g | (True,  g) <- entries, gCap g /= Exact ]
        fresh   = [ g | (False, g) <- entries, gCap g /= Exact ]
        singleWitnessed = length wits == 1 && null fresh
        witWrap m | singleWitnessed = iwit m
                  | otherwise       = m

        -- The generic combination floor, witnessed-aware:
        --   * no witnessed operand: the plain marginalize fold (unchanged);
        --   * one witnessed operand, rest Dirac: a deterministic image of the
        --     witnessed latent — the standalone law passes through the plain
        --     fold (Diracs are free) and the result stays witnessed;
        --   * witnessed + fresh: recovering the witnessed side from the
        --     observation is free, so it enters the fold as Exact; only the
        --     fresh residual pays. One fresh latent survives with its density
        --     (the u2-recovery case); two fresh latents still floor to {S,I}.
        --   * ≥2 witnessed, no fresh: every random operand is individually
        --     recoverable from the observation, so this node's inference is
        --     free once those recoveries are in scope — the codegen let-fold
        --     (body-factor folding in IRCompiler's Apply arm) pays each
        --     latent's density once at its own binding and checks this node
        --     as an indicator, which also covers the same-latent shape
        --     (e.g. x+x) without a ledger identity. The node keeps an honest
        --     random capability: the meet of the witnessed grounds, family
        --     dropped (a genuine combination). Not re-marked witnessed: the
        --     value is an image of several latents, not one.
        floorCombine
          | null wits       = plainFold (map snd entries)
          | singleWitnessed = iwit (plainFold (map snd entries))
          | not (null fresh) =
              plainFold [ if w && gCap g /= Exact then topGround else g
                        | (w, g) <- entries ]
          | otherwise       =
              IG (groundMod (foldr1 meetCap (map gCap wits))
                            (foldr joinFin Finite (map gFin wits))
                            FamNone)

        plainFold []     = IG gExact
        plainFold (g:gs) = IG (foldl marginalize g gs)

        -- A unary map the closure table does not list passes its operand's
        -- ground through, family and all -- right for a map that leaves the
        -- value alone (an accessor) or maps the family onto itself, wrong for
        -- arithmetic that does not: @neg@ of a log-normal is supported on the
        -- negatives and has no (mu, sigma), yet stayed 'PLogNormal' and every
        -- variant, generate included, died extracting them
        -- (fuzz-admission-oracle-bugs item 4). An arithmetic map keeps the
        -- family only where 'IRCompiler.toIRLogNormalParams' has a rule for it.
        familyPreserved = name `notElem` arithmeticMaps
                       || (name, gFam (outerI floorCombine)) `elem`
                            [ ("sqrt", FamLogNormal), ("sq", FamLogNormal), ("recip", FamLogNormal) ]
        arithmeticMaps = ["exp", "log", "neg", "negI", "recip", "sqrt", "sq", "double",
                          "plus", "plusI", "mult", "multI", "max"]
        keepFamilyIf True  m = m
        keepFamilyIf False m = dropFamily m
        dropFamily (IG g)   = IG g { gFam = FamNone }
        dropFamily (IWit m) = IWit (dropFamily m)
        dropFamily m        = m

-- ---------------------------------------------------------------------------
-- tryNormalClosure (ported verbatim from PInfer2 — the family precision layer)
-- ---------------------------------------------------------------------------

-- | The family-preserving operator table (design §6 @primSem@/@shiftSem@): which
-- 'InjF's keep 'PNormal'/'PLogNormal' structure, and the result. Ported from
-- @PInfer2.tryNormalClosure@ so the analytic-kernel cases stay byte-for-byte.
--
-- The Gaussian rows (@plus@, @mult@ by a constant, @neg@) are no longer here:
-- an affine node is 'PNormal' exactly when its affine form can be built
-- ('affineInjF'; law-carrying-modality M4), which is also what the compiler
-- collapses.
tryNormalClosure :: String -> [PType] -> Maybe PType
tryNormalClosure "neg"  [Deterministic]          = Just Deterministic
tryNormalClosure "exp"  [PNormal]                = Just PLogNormal
tryNormalClosure "log"  [PLogNormal]             = Just PNormal
tryNormalClosure "mult" [PLogNormal, PLogNormal]    = Just PLogNormal
tryNormalClosure "mult" [PLogNormal, Deterministic] = Just PLogNormal
tryNormalClosure "mult" [Deterministic, PLogNormal] = Just PLogNormal
tryNormalClosure _      _                           = Nothing

-- ---------------------------------------------------------------------------
-- The vector fixpoint over top-level declarations
-- ---------------------------------------------------------------------------

-- | The /greatest/-fixpoint summaries of every top-level declaration.
--
-- The body operator is monotone-decreasing (every rule only loses capability),
-- so a recursive declaration's modality is a greatest fixpoint: seed at 'topI'
-- and let Kleene iteration descend to the stable value in the finite-height
-- lattice.
--
-- The iteration is staged over the /call graph's/ strongly-connected components
-- in dependency order (callees first) rather than run globally over every
-- declaration at once. Chaotic-iteration staging reaches the same greatest
-- fixpoint — a component's operator only reads components below it, which are
-- already at their fixpoint — but it means a declaration that is not part of a
-- cycle is inferred exactly /once/, with no convergence test at all.
--
-- That distinction is a performance cliff, not a micro-optimisation: the
-- convergence test 'eqI'/'subI' compares two 'IArr' transfers /pointwise over
-- the ground input lattice/, and for a curried n-ary function it recurses
-- down the whole arrow spine doing so — @|reprInputs|^n@ re-inferences of the
-- body. On @main s1 .. sn = readMNist(s1) ++ .. ++ readMNist(sn)@ the global
-- iteration therefore spent ~6x more time per added parameter (task
-- @modality-param-ptype-exponential@: 58s at n=8) for a program with no
-- recursion at all. Only a genuine cycle now pays a convergence test, and it
-- pays it over its own members only.
--
-- The call graph over-approximates: a body's referenced 'Var' names are taken
-- flat, so a lambda parameter that shadows a declaration name counts as a call.
-- Over-approximating merges components, which only costs iterations; it never
-- changes the fixpoint. (Pure non-terminating recursion would sit at the top —
-- the totality axis, design §10, is the principled handle and is deferred.)
summaries :: FCData -> Program -> Env
summaries fcData prog = foldl solve Map.empty components
  where
    decls      = functions prog
    declNames  = Set.fromList (map fst decls)
    components = stronglyConnComp
                   [ ((n, b), n, callees b) | (n, b) <- decls ]
    callees b  = Set.toList (Set.intersection declNames (containedVars varsOfExpr b))

    -- A declaration outside every cycle: one inference against the already
    -- solved components it depends on, no seed and no convergence test.
    solve env (AcyclicSCC (n, b)) = Map.insert n (inferDecl env b) env
    -- A cycle (including a self-recursive declaration): Kleene iteration over
    -- the component's members only, seeded at the top.
    solve env (CyclicSCC grp) = go (foldr seed env grp) (50 :: Int)
      where
        seed (n, b) e = Map.insert n (bareLaw (topI (rType (getTypeInfo b)))) e
        step e = foldr (\(n, b) e' -> Map.insert n (inferDecl e b) e') e grp
        go e 0 = e
        go e k = let e' = step e
                 in if converged e e' then e' else go e' (k - 1)
        converged a b = and [ eqI (lawMod (a Map.! n)) (lawMod (b Map.! n)) | (n, _) <- grp ]

    inferDecl env b = fst3 (inferE (declCtx b) env b)
    fst3 (x,_,_) = x
    declCtx b = mkICtx (adts prog) fcData (cnOf b) prog

-- ---------------------------------------------------------------------------
-- Public entry points
-- ---------------------------------------------------------------------------

-- | Annotate every node with its projected flat 'PType' (the replacement for
-- @PInfer2.addPTypeInfo@). Assumes RType inference has already run, and takes
-- the forward-chaining certificate (built between RInfer and this pass —
-- @progToFCData@ reads rType but no pType) whose witnessed-binding verdict the
-- let rule consults ('SPLL.Typing.Infer.addTypeInfo' does the sequencing).
addModalityPTypeInfo :: FCData -> Program -> Either CompilerError Program
addModalityPTypeInfo fcData prog = Right (fst (inferProgram fcData prog))

-- | The annotated program plus its per-node certificates ('LawTable').
inferProgram :: FCData -> Program -> (Program, LawTable)
inferProgram fcData prog = (prog', Map.fromList acc)
  where (prog', acc) = inferProgramAcc fcData prog

inferProgramAcc :: FCData -> Program -> (Program, GAcc)
inferProgramAcc fcData prog@(Program decls nns adtDecls enc sigs) =
  (Program decls' nns adtDecls enc sigs, concat accs)
  where
    env = summaries fcData prog
    results = [ (n, inferE (mkICtx adtDecls fcData (cnOf b) prog) env b)
              | (n, b) <- decls ]
    decls'  = [ (n, e) | (n, (_, e, _)) <- results ]
    accs    = [ a | (_, (_, _, a)) <- results ]

-- | The per-node outer 'GroundMod', keyed by chain name (diff harness §6).
perNodeOuterGrounds :: FCData -> Program -> [(ChainName, GroundMod)]
perNodeOuterGrounds fcData p = [ (cn, outerI (lawMod l)) | (cn, l) <- snd (inferProgramAcc fcData p) ]

-- ---------------------------------------------------------------------------
-- Re-inference under recovered bindings (law-carrying-modality M1, §D)
-- ---------------------------------------------------------------------------

-- | What re-inferring a sub-expression needs from the whole program, computed
-- once per compile: the declarations to locate it in, and the top-level
-- summaries its calls are resolved against.
data ReinferCtx = ReinferCtx
  { rcADTs      :: [ADTDecl]
  , rcFC        :: FCData
  , rcDecls     :: [FnDecl]
  , rcSummaries :: Env
  , rcProg      :: Program
  }

reinferCtx :: FCData -> Program -> ReinferCtx
reinferCtx fcData prog@(Program decls _ adtDecls _ _) =
  ReinferCtx adtDecls fcData decls (summaries fcData prog) prog

-- | Re-annotate @target@ as 'inferE' would, given that each of @pins@ names a
-- variable whose value is known -- recovered from the observation by an
-- enclosing inversion, or fixed by an enclosing enumeration loop -- and so is
-- 'Exact'. This is how a recovered variable's determinism reaches every node
-- that depends on it, through @draw@ binders included: after
-- @draw y = x * 2.0@ with @x@ pinned, @y@ is 'Exact' too, because the engine's
-- own let rule binds it.
--
-- The environment is the one 'inferE' had at the node carrying @target@'s
-- chain name, rebuilt by 'envAt' from its declaration's root, so enclosing
-- binders that were /not/ recovered keep their laws. A pin is honoured at
-- every binder of that name on the way down (an intermediate binding computed
-- from a pinned variable then gets the right law) and also bound outright, so
-- a variable with no source binder -- 'enumerateCurriedArgument''s loop
-- variable, or a parameter an enumeration renamed -- is 'Exact' too. Inside
-- @target@ an inner binder of a pinned name shadows the pin as usual.
--
-- @target@ may differ from the program's node under that chain name (a
-- renamed body, a synthesized application around a loop variable); only its
-- position is looked up. A chain name found in no declaration leaves the
-- non-pinned free variables at the law their existing annotation projects.
reinferGiven :: ReinferCtx -> [String] -> Expr -> Expr
reinferGiven rc pins target = e'
  where
    pinSet = Set.fromList pins
    pinMap = Map.fromList [ (n, bareLaw (IG gExact)) | n <- pins ]
    located = [ (b, env) | (_, b) <- rcDecls rc
                         , Just env <- [envAt (declCtx b) pinSet (rcSummaries rc) (cnOf target) b] ]
    (ctx, env0) = case located of
      (b, env) : _ -> (declCtx b, env)
      [] -> (declCtx target, Map.union (annotatedFreeLaws target) (rcSummaries rc))
    (_, e', _) = inferE ctx (Map.union pinMap env0) target
    declCtx b = mkICtx (rcADTs rc) (rcFC rc) (cnOf b) (rcProg rc)

-- | The free variables of an expression at the law their current annotation
-- projects: the fallback environment of 'reinferGiven' for a node it cannot
-- locate in the program.
annotatedFreeLaws :: Expr -> Env
annotatedFreeLaws = go Set.empty
  where
    go bound (Expr ti (Var n))
      | n `Set.member` bound = Map.empty
      | otherwise = Map.singleton n (bareLawOfPType (pType ti))
    go bound (Expr _ (Lambda x b)) = go (Set.insert x bound) b
    go bound e = Map.unions (map (go bound) (getSubExprs e))

-- | The environment 'inferE' extends to on its way from @e@ down to the node
-- with chain name @cn@, or 'Nothing' if @e@ does not contain it. It binds
-- exactly as 'inferE' does -- 'bindParam', 'lambdaParamMod', 'conditionEnv'
-- -- except that a binder of a pinned name binds 'Exact'.
envAt :: ICtx -> Set.Set String -> Env -> ChainName -> Expr -> Maybe Env
envAt ctx pins env cn e
  | cnOf e == cn = Just env
  | otherwise = case e of
      Expr _ (Apply f@(Expr _ (Lambda x body)) arg) ->
        firstJust
          [ envAt ctx pins env cn arg
          , if cnOf f == cn then Just env else Nothing
          , envAt ctx pins (pin x (letEnv arg)) cn body ]
      Expr ti (Lambda x body) ->
        envAt ctx pins (pin x (Map.insert x (bareLaw (lambdaParamMod ti)) env)) cn body
      Expr _ (IfThenElse c t f) ->
        let armEnv = conditionEnv env c
        in firstJust [envAt ctx pins env cn c, envAt ctx pins armEnv cn t, envAt ctx pins armEnv cn f]
      _ -> firstJust (map (envAt ctx pins env cn) (getSubExprs e))
  where
    pin x en = if x `Set.member` pins then Map.insert x (bareLaw (IG gExact)) en else en
    letEnv arg = case e of
      Expr _ (Apply (Expr lti (Lambda x body)) _) ->
        let (l, arg', _) = inferE ctx env arg
            (env', _, _) = letBinding ctx env lti x body arg' l
        in env'
      _ -> env
    firstJust = foldr (\m r -> maybe r Just m) Nothing
