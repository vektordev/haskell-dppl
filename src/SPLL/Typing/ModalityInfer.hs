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
--     one combinator behind application, @if@, and generic binary ops;
--   * a syntactic lambda is a /known/ closure (outer @rho = det@) whose transfer
--     is obtained by partial evaluation of the body — so application is resolved
--     by β-reduction at the call site, which is what preserves the distribution
--     family ('Family') through application (design §6 motivating program 2);
--   * recursion among top-level declarations is a least fixpoint computed by
--     Kleene iteration over the whole decl graph (covers mutual recursion).
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
  , perNodeOuterGrounds
  , IMod(..)
  , inferProgram
  , toMod
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import SPLL.Lang.Types
  ( Expr(..), Program(..), TypeInfo(..), InjFName(..), ChainName, ADTDecl, CompilerError, FnDecl )
import SPLL.Lang.Lang (getTypeInfo)
import SPLL.Typing.Typing (setPType)
import SPLL.Typing.PType (PType(..))
import SPLL.Typing.RType (RType(..))
import SPLL.Typing.Modality
import PredefinedFunctions (isFieldConstructor)

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
outerI (IProd a b) = (meetGround (outerI a) (outerI b))            { gFam = FamNone }
outerI (ISum t a b)= (meetGround t (meetGround (outerI a) (outerI b))) { gFam = FamNone }
outerI (IRec s e)  = (meetGround s (outerI e))                    { gFam = FamNone }

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

-- | The application rule @Mod(f e) = rho ▷ phi(e)@. For a syntactic function the
-- transfer is the body closure (β-reduction). A non-function head is applied
-- opaquely through its outer ground (a safe, never-failing fallback for the
-- ill-typed / unknown-head case).
applyI :: IMod -> IMod -> IMod
applyI (IArr rho phi) arg = applyOuterI rho (phi arg)
applyI other          arg = applyOuterI (outerI other) arg

-- | Pointwise /meet/ of two same-shape modalities — the combinator for @if@/case
-- branches. The result of a mixture is only as capable as the /weakest/ branch
-- (you need every branch's machinery to evaluate the mixture), so this is the
-- meet, not the join. (Using the join is the prototype's known "mixture join
-- optimism" unsoundness — design §9 — which would type a continuous mixture as
-- 'Deterministic'.) The shape-mismatch fallback meets the outer grounds.
meetI :: IMod -> IMod -> IMod
meetI (IG a)       (IG b)        = IG (meetGround a b)
meetI (IProd a1 a2)(IProd b1 b2) = IProd (meetI a1 b1) (meetI a2 b2)
meetI (IArr r1 p1) (IArr r2 p2)  = IArr (meetGround r1 r2) (\m -> meetI (p1 m) (p2 m))
meetI (ISum t1 a1 b1)(ISum t2 a2 b2) = ISum (meetGround t1 t2) (meetI a1 a2) (meetI b1 b2)
meetI (IRec s1 e1) (IRec s2 e2)  = IRec (meetGround s1 s2) (meetI e1 e2)
meetI a b = IG (meetGround (outerI a) (outerI b))

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
repIMod _             = IG topGround

-- | Subtyping over 'IMod' (transfers compared pointwise over the finite ground
-- input lattice). The convergence test for the fixpoint.
subI :: IMod -> IMod -> Bool
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

-- ---------------------------------------------------------------------------
-- Ground leaves
-- ---------------------------------------------------------------------------

-- | Decision C: a node tagged with @DiscreteValues@ has finite support, so its
-- ground modality is 'Finite' regardless of how the combination rule arrived at
-- its capability. Applied to the enumerable leaves and results (ReadNN of a
-- categorical net, integer @plusI@/equality, …) where it turns the
-- marginalization floor from @{S,I}@ (no closed density) into @{S,D,I}@ (a finite
-- mixture has a density).
tagFin :: TypeInfo -> GroundMod -> GroundMod
tagFin ti g
  | finFromTags (tags ti) == Finite = g { gFin = Finite }
  | otherwise                       = g

tagFinMod :: TypeInfo -> IMod -> IMod
tagFinMod ti (IG g) = IG (tagFin ti g)
tagFinMod _  m      = m

-- | A scalar distribution family ('FamNormal'/'FamLogNormal') only attaches to a
-- bare 'TFloat' value. A field constructor that builds a container/sum (e.g.
-- @left :: a -> Either a b@, @cons@) yields a value that is not itself Gaussian,
-- so drop the family there (mirrors @PInfer2.degradeNormal@ for containers). The
-- single-field 'IG' case — @left (Normal …)@, which the @injFMod@ floor passes
-- through unchanged — is the one this catches that 'outerI' alone cannot, since
-- no 'IProd'/'ISum' wrapper marks it as a container.
gateScalarFamily :: RType -> IMod -> IMod
gateScalarFamily TFloat m      = m
gateScalarFamily _      (IG g) = IG g { gFam = FamNone }
gateScalarFamily _      m      = m

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

type Env = Map String IMod

-- | Per-node outer ground accumulated for the diff harness's partial-set check
-- (design §6). Keyed by chain name (every node has one after @annotateProg@).
type GAcc = [(ChainName, GroundMod)]

cnOf :: Expr -> ChainName
cnOf = chainName . getTypeInfo

-- | Infer the modality of an expression, returning the modality, the
-- pType-annotated expression, and the per-node outer-ground accumulation.
inferE :: [ADTDecl] -> Env -> Expr -> (IMod, Expr, GAcc)
inferE adts env expr = case expr of

  -- The theta-tree source of ThetaI/Subtree is left untouched (PInfer2 does not
  -- annotate it either); only this node's own modality is recorded.
  ThetaI ti s i  -> done (IG gExact) (ThetaI (setPType ti Deterministic) s i) []
  Subtree ti s i -> done (IG gExact) (Subtree (setPType ti Deterministic) s i) []
  Constant ti v  -> done (IG gExact) (Constant (setPType ti Deterministic) v) []

  Var ti name ->
    let m = case Map.lookup name env of
              Just im            -> im
              Nothing
                | name == "Normal"  -> IG gNormal
                | name == "Uniform" -> IG gIntegrate
                | otherwise         -> IG gExact   -- unbound ⇒ Deterministic (PInfer2 default)
    in done m (Var (setPType ti (projectNode (rType ti) m)) name) []

  ReadNN ti name s ->
    let (_, s', sa) = inferE adts env s
        g = tagFin ti (if rType ti == TFloat then gNormal else gIntegrate)
    in done (IG g) (ReadNN (setPType ti (projectGround g)) name s') sa

  GreaterThan ti a b -> compareNode ti GreaterThan a b
  LessThan    ti a b -> compareNode ti LessThan a b

  InjF ti name@(Named fname) args ->
    let rs   = map (inferE adts env) args
        mods = [ m  | (m,_,_) <- rs ]
        es'  = [ e  | (_,e,_) <- rs ]
        acc  = concat [ a | (_,_,a) <- rs ]
        m    = gateScalarFamily (rType ti) (tagFinMod ti (injFMod adts fname mods))
    in done m (InjF (setPType ti (projectI m)) name es') acc

  IfThenElse ti c t f ->
    let (mc, c', ca) = inferE adts env c
        (mt, t', ta) = inferE adts env t
        (mf, f', fa) = inferE adts env f
        m = applyOuterI (outerI mc) (meetI mt mf)
    in done m (IfThenElse (setPType ti (projectI m)) c' t' f') (ca ++ ta ++ fa)

  Lambda ti x body ->
    let argTy = case rType ti of TArrow a _ -> a; _ -> TFloat
        arr   = IArr gExact (\m -> let (im,_,_) = inferE adts (Map.insert x m env) body in im)
        (bodyRepMod, body', ba) = inferE adts (Map.insert x (repIMod argTy) env) body
    -- The internal modality is the closure 'arr' (so application β-reduces), but
    -- the flat annotation @IRCompiler@ reads is the /body's/ pType, not the outer
    -- closure 'Deterministic' — IRCompiler selects prob/integrate codegen from the
    -- function node's pType (e.g. a top-level @distr x = 2*Uniform+x@ must read
    -- 'Integrate', not the lossy outer 'Deterministic'). Matches @PInfer2@.
    in done arr (Lambda (setPType ti (projectI bodyRepMod)) x body') ba

  Apply ti f arg ->
    let (argMod, arg', aa) = inferE adts env arg
    in case f of
         -- A directly-applied lambda is a @let@: bind the parameter to the
         -- argument's actual modality (β-reduction with the precise value).
         Lambda lti x body ->
           let (bodyMod, body', ba) = inferE adts (Map.insert x argMod env) body
               -- The applied lambda node carries the body's pType (its result),
               -- matching @PInfer2@ and what @IRCompiler@ reads, not the outer
               -- closure 'Deterministic'.
               f' = Lambda (setPType lti (projectI bodyMod)) x body'
           in done bodyMod (Apply (setPType ti (projectNode (rType ti) bodyMod)) f' arg')
                   (laccLambda lti ++ ba ++ aa)
         _ ->
           let (fMod, f', fa) = inferE adts env f
               m = applyI fMod argMod
           in done m (Apply (setPType ti (projectNode (rType ti) m)) f' arg') (fa ++ aa)

  where
    done m e acc = (m, e, (cnOf e, outerI m) : acc)
    -- a directly-applied lambda node still records its own (det) outer ground
    laccLambda lti = [(chainName lti, gExact)]

    compareNode ti ctor a b =
      let (ma, a', aacc) = inferE adts env a
          (mb, b', bacc) = inferE adts env b
          g = tagFin ti (compareGround (outerI ma) (outerI mb))
      in done (IG g) (ctor (setPType ti (projectGround g)) a' b') (aacc ++ bacc)

-- | Comparison (@>@/@<@): the Boolean result is a Bernoulli (finite support).
-- Both deterministic ⇒ a known Boolean; both integral-ready ⇒ exact tail
-- probability via the CDF; both samplable ⇒ Monte-Carlo only; else opaque.
compareGround :: GroundMod -> GroundMod -> GroundMod
compareGround a b
  | gCap a == Exact && gCap b == Exact = groundMod Exact        Finite FamNone
  | okInt a && okInt b                 = groundMod DensInt      Finite FamNone
  | canSample a && canSample b         = groundMod SampleOnly   Finite FamNone
  | otherwise                          = groundMod Opaque       Finite FamNone
  where okInt g     = leqCap IntegralOnly (gCap g) || gCap g == Exact
        canSample g = leqCap SampleOnly (gCap g)

-- | Modality of an 'InjF' application. Resolution order:
--
--   1. 'tryNormalClosure' — the distribution-family-preserving operators
--      (affine shift/scale, neg, exp/log) keep 'PNormal'/'PLogNormal';
--   2. field constructors (tuples / @Cons@ / user-ADT, ≥2 fields) build a
--      structured 'IProd' so the projection is the meet of independent fields
--      and accessors can later recover a single field;
--   3. the tuple accessors @fst@/@snd@ project a component of an 'IProd';
--   4. everything else marginalises its operands (the generic combination
--      floor); a unary invertible map is the singleton case and passes its
--      operand through, family intact.
injFMod :: [ADTDecl] -> String -> [IMod] -> IMod
injFMod adts name mods =
  case tryNormalClosure name (map projectI mods) of
    Just pt -> IG (fromClosurePType pt)
    Nothing
      | isFieldConstructor adts name, (m0:rest) <- mods -> foldl IProd m0 rest
      | name == "fst", [m] <- mods -> projFst m
      | name == "snd", [m] <- mods -> projSnd m
      | otherwise -> case map outerI mods of
          []     -> IG gExact
          (g:gs) -> IG (foldl marginalize g gs)
  where projFst (IProd a _) = a
        projFst m           = m
        projSnd (IProd _ b) = b
        projSnd m           = m

-- ---------------------------------------------------------------------------
-- tryNormalClosure (ported verbatim from PInfer2 — the family precision layer)
-- ---------------------------------------------------------------------------

-- | The family-preserving operator table (design §6 @primSem@/@shiftSem@): which
-- 'InjF's keep 'PNormal'/'PLogNormal' structure, and the result. Ported from
-- @PInfer2.tryNormalClosure@ so the analytic-kernel cases stay byte-for-byte.
tryNormalClosure :: String -> [PType] -> Maybe PType
tryNormalClosure "plus" [PNormal, PNormal]       = Just PNormal
tryNormalClosure "plus" [PNormal, Deterministic] = Just PNormal
tryNormalClosure "plus" [Deterministic, PNormal] = Just PNormal
tryNormalClosure "mult" [PNormal, Deterministic] = Just PNormal
tryNormalClosure "mult" [Deterministic, PNormal] = Just PNormal
tryNormalClosure "neg"  [PNormal]                = Just PNormal
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

-- | The /greatest/-fixpoint summaries of every top-level declaration, computed
-- by Kleene iteration seeded at 'topI'. The body operator is monotone-decreasing
-- (every rule only loses capability), so from the top seed the sequence descends
-- in the finite-height lattice and converges. Recursive and mutually-recursive
-- calls read the current approximation; non-recursive declarations reach their
-- value in one step regardless of the seed. (Pure non-terminating recursion would
-- sit at the top — the totality axis, design §10, is the principled handle and is
-- deferred.)
summaries :: [ADTDecl] -> [FnDecl] -> Env
summaries adts decls = go initial (50 :: Int)
  where
    initial = Map.fromList [ (n, topI (rType (getTypeInfo b))) | (n, b) <- decls ]
    step env = Map.fromList [ (n, fst3 (inferE adts env b)) | (n, b) <- decls ]
    go env 0 = env
    go env k = let env' = step env
               in if converged env env' then env' else go env' (k - 1)
    converged a b = and [ eqI (a Map.! n) (b Map.! n) | (n, _) <- decls ]
    fst3 (x,_,_) = x

-- ---------------------------------------------------------------------------
-- Public entry points
-- ---------------------------------------------------------------------------

-- | Annotate every node with its projected flat 'PType' (the replacement for
-- @PInfer2.addPTypeInfo@). Assumes RType inference has already run.
addModalityPTypeInfo :: Program -> Either CompilerError Program
addModalityPTypeInfo prog = Right (fst (inferProgram prog))

-- | The annotated program plus the per-node outer-ground list (for the diff
-- harness's partial-set invariant check).
inferProgram :: Program -> (Program, [(ChainName, GroundMod)])
inferProgram (Program decls nns adtDecls enc) =
  (Program decls' nns adtDecls enc, concat accs)
  where
    env = summaries adtDecls decls
    results = [ (n, inferE adtDecls env b) | (n, b) <- decls ]
    decls'  = [ (n, e) | (n, (_, e, _)) <- results ]
    accs    = [ a | (_, (_, _, a)) <- results ]

-- | The per-node outer 'GroundMod', keyed by chain name (diff harness §6).
perNodeOuterGrounds :: Program -> [(ChainName, GroundMod)]
perNodeOuterGrounds = snd . inferProgram
