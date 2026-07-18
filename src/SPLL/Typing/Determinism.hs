-- | Stage 1 of the modality pipeline (design @modality-typesystem-port@ §4,
-- milestone 2): a forward /determinism/ dataflow with a call-graph fixpoint.
--
-- == What it computes
--
-- For every node it answers a single question: is this value /known/ — i.e. a
-- deterministic function of the program's parameters (@theta@/@subtree@) and
-- constants, independent of any random draw? Determinism propagates strictly
-- /forward/ (deterministic inputs ⇒ deterministic output) through every
-- operation, regardless of invertibility, which is exactly what makes it
-- computable without ForwardChaining and breaks the apparent stage cycle (§4).
--
-- == Why it exists
--
-- ForwardChaining needs to know which sibling points are /known/ to seed its
-- inversion — never @dens@/@int@/@sample@. Today it under-approximates this with
-- @Constant@ alone: @ThetaI@ and @Subtree@ (both deterministic) emit no clause
-- and fall through. The 'knownAnchors' set produced here is the real
-- determinism field FC consumes in place of that @Constant@-only approximation
-- (the wiring is milestone 3, @modality-split-forwardchaining@).
--
-- == Soundness stance
--
-- The exposed anchor set is /sound/: a node is marked known only if it is
-- deterministic in every context it is evaluated in. Where determinism cannot
-- be established (genuinely higher-order applications, a recursive call still
-- being summarised) the answer is conservatively @False@. Under-approximating
-- only costs FC precision; over-approximating would be unsound, so the meet is
-- always taken ('Map.unionWith' '(&&)').
module SPLL.Typing.Determinism
  ( DetMap
  , determinismMap
  , knownAnchors
  , isKnownAnchor
  , functionSummaries
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import SPLL.Lang.Types (Expr(..), Program(..), TypeInfo(..), ChainName)
import SPLL.Lang.Lang (getTypeInfo, getSubExprs)

-- | Per-node determinism, keyed by the chain name assigned by
-- @ForwardChaining.annotateProg@ (so this pass must run after it).
type DetMap = Map ChainName Bool

-- | In-scope binding determinism: a bound variable name ↦ whether its value is
-- deterministic in the current context.
type VarEnv = Map String Bool

-- | Per-top-level-function summary: applied to deterministic arguments, is the
-- (fully applied) result deterministic? The least fixpoint of this is what the
-- call-graph iteration below computes.
type FnSummary = Map String Bool

-- | The reserved 'Var' names that introduce randomness (distribution
-- primitives, mirroring @PInfer2.distributionPrimitives@). Everything else
-- propagates determinism forward.
randomPrimitives :: Set String
randomPrimitives = Set.fromList ["Uniform", "Normal"]

-- ---------------------------------------------------------------------------
-- Public entry points
-- ---------------------------------------------------------------------------

-- | The per-node determinism field over the whole top-level function-decl
-- graph. Each function body is walked with its own parameters unknown (bound
-- 'False' — their determinism is context-dependent, so the universally-sound
-- answer is non-deterministic); @let@-style immediate applications and calls to
-- top-level functions are resolved precisely (the latter via 'functionSummaries').
determinismMap :: Program -> DetMap
determinismMap prog =
  Map.unionsWith (&&)
    [ snd (detExpr phi Map.empty body) | (_, body) <- functions prog ]
  where phi = functionSummaries prog

-- | The /known anchor/ set FC consumes: the chain names whose value is known
-- without observing the sample.
knownAnchors :: Program -> Set ChainName
knownAnchors = Map.keysSet . Map.filter id . determinismMap

-- | Query a 'DetMap'; an unrecorded node is treated as not-known (sound floor).
isKnownAnchor :: DetMap -> ChainName -> Bool
isKnownAnchor m cn = Map.findWithDefault False cn m

-- ---------------------------------------------------------------------------
-- The call-graph fixpoint
-- ---------------------------------------------------------------------------

-- | Least fixpoint of the function summaries. Determinism is monotone in the
-- callee summaries, so starting every function at 'True' and re-deriving until
-- stable converges (values only ever fall @True → False@; the domain is finite).
functionSummaries :: Program -> FnSummary
functionSummaries prog = iterate' initial
  where
    fs = functions prog
    initial = Map.fromList [ (n, True) | (n, _) <- fs ]
    step phi = Map.fromList [ (n, summaryOf phi body) | (n, body) <- fs ]
    iterate' phi = let phi' = step phi in if phi' == phi then phi else iterate' phi'

-- | A function's summary: peel its leading lambda parameters, bind them all
-- 'True' (the "applied to deterministic arguments" assumption), and ask whether
-- the body is deterministic under the current callee summaries.
summaryOf :: FnSummary -> Expr -> Bool
summaryOf phi expr =
  let (params, body) = peelParams expr
      env = Map.fromList [ (p, True) | p <- params ]
  in fst (detExpr phi env body)

-- | Strip leading lambdas, returning their bound names and the body beneath.
peelParams :: Expr -> ([String], Expr)
peelParams (Lambda _ x b) = let (ps, body) = peelParams b in (x : ps, body)
peelParams e              = ([], e)

-- ---------------------------------------------------------------------------
-- The forward dataflow
-- ---------------------------------------------------------------------------

-- | Determinism of an expression's value together with the per-node map for it
-- and all its descendants. Sub-maps are merged with '(&&)' so a node visited in
-- several contexts (e.g. a multiply-applied function body) takes the meet.
detExpr :: FnSummary -> VarEnv -> Expr -> (Bool, DetMap)
detExpr phi env e = case e of
  -- Self-sufficient known anchors: constants and parameter access. Their child
  -- (the theta-tree source of ThetaI/Subtree) is itself deterministic.
  Constant{}    -> here True Map.empty
  ThetaI _ s _  -> here True (snd (detExpr phi env s))
  Subtree _ s _ -> here True (snd (detExpr phi env s))

  -- Variables: bound ⇒ their context determinism; a distribution primitive ⇒
  -- random; otherwise (top-level function reference / free name) ⇒ known,
  -- matching PInfer2's default of Deterministic for an unbound Var.
  Var _ name
    | name `Map.member` env          -> here (env Map.! name) Map.empty
    | name `Set.member` randomPrimitives -> here False Map.empty
    | otherwise                      -> here True Map.empty

  -- Neural reads draw from a (categorical / Gaussian) law: never deterministic.
  ReadNN _ _ s  -> here False (snd (detExpr phi env s))

  -- Pure combinators: deterministic iff every operand is.
  GreaterThan _ a b -> binAnd a b
  LessThan _ a b    -> binAnd a b
  InjF _ _ args     -> let rs = map (detExpr phi env) args
                       in here (and (map fst rs)) (Map.unionsWith (&&) (map snd rs))
  IfThenElse _ c t f ->
    let rs = map (detExpr phi env) [c, t, f]
    in here (and (map fst rs)) (Map.unionsWith (&&) (map snd rs))

  -- A bare lambda (one not immediately applied — handled in Apply) is a function
  -- value, not a ground anchor: mark it False and walk its body with the
  -- parameter unknown.
  Lambda _ x body ->
    here False (snd (detExpr phi (Map.insert x False env) body))

  Apply _ f arg -> detApply phi env e f arg
  where
    cn = chainName (getTypeInfo e)
    -- record this node's determinism, merged (meet) with the descendants' map
    here b m = (b, Map.insertWith (&&) cn b m)
    binAnd a b =
      let (da, ma) = detExpr phi env a
          (db, mb) = detExpr phi env b
      in here (da && db) (Map.unionWith (&&) ma mb)

-- | Application. Two cases are resolved precisely:
--
--   * an immediate lambda @(\\x -> body) arg@ (which is how @let@ desugars) —
--     the binding is unique, so @x@'s determinism is exactly the argument's;
--   * a call whose head is a top-level function — its result determinism is the
--     function's summary conjoined with all the arguments being deterministic.
--
-- Anything else (a higher-order argument bound to a function, an @if@ returning
-- a lambda, …) is conservatively non-deterministic. In every case both
-- sub-expressions are still walked so all descendants are annotated.
detApply :: FnSummary -> VarEnv -> Expr -> Expr -> Expr -> (Bool, DetMap)
detApply phi env node f arg =
  let (da, ma)  = detExpr phi env arg
      (_,  mf)  = detExpr phi env f
      base      = Map.unionWith (&&) ma mf
      record b m = (b, Map.insertWith (&&) cn b m)
  in case f of
       Lambda _ x body ->
         let (db, mb) = detExpr phi (Map.insert x da env) body
         in record db (Map.unionWith (&&) base mb)
       _ -> case appSpine node of
              Just (g, args) | g `Map.member` phi ->
                let argsDet = and [ fst (detExpr phi env a) | a <- args ]
                in record (phi Map.! g && argsDet) base
              _ -> record False base
  where cn = chainName (getTypeInfo node)

-- | Collect an application spine @f a1 a2 …@ down to a 'Var' head, returning the
-- head name and the arguments left-to-right. 'Nothing' if the head is not a Var.
appSpine :: Expr -> Maybe (String, [Expr])
appSpine (Var _ n)     = Just (n, [])
appSpine (Apply _ g a) = do (n, as) <- appSpine g; Just (n, as ++ [a])
appSpine _             = Nothing
