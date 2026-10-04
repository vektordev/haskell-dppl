-- | Normalisation of the /callee/ position of an application (task
-- @modality-arrow-apply-crashes@).
--
-- Probability mode compiles @Apply l v@ by inverting the observation through
-- @l@'s body, which presupposes that @l@ names a lambda the compiler can see:
-- 'SPLL.Typing.ForwardChaining.findEquivalentExpression' must resolve @l@'s
-- chain name to a @LambdaInfo@. That holds for a literal lambda and for a
-- top-level function, and fails for every other way a program can produce a
-- function /value/ — a lambda projected out of a tuple, taken from a list, or
-- chosen by an @if@ — where the compiler crashed with an internal
-- "should resolve to a lambda" error, or (for a randomly chosen one) compiled a
-- mixture that multiplied a branch weight by a closure and died in the
-- interpreter.
--
-- This pass removes the selection instead of teaching the inference engines to
-- see through it. Two rewrites, both purely syntactic:
--
-- * __An @if@ in callee position is distributed into its arms__:
--   @(if c then f else g) v@ becomes @if c then f v else g v@. The arms are
--   alternatives, so no draw in @v@ is duplicated — only one arm is ever
--   realised — and the result is the ordinary mixture the 'IfThenElse' rules
--   already compile, with each arm now an applied lambda literal. This is what
--   makes a /probabilistic/ function value work end-to-end: the mixture is
--   taken over the two applications' probabilities, never over the closures.
--
-- * __A callee that denotes a lambda literal is replaced by it__: any accessor
--   applied to a literal application of the constructor it belongs to —
--   @fst@ \/ @snd@ of a tuple literal, @head@ \/ @tail@ of a list literal,
--   @fromLeftPartial@ \/ @fromRightPartial@ of a literal @left@ \/ @right@, a
--   user-ADT field accessor of a literal constructor application — and
--   @let@-bound names standing for any of those, are reduced until a @Lambda@
--   falls out ('reduceCallee'). Only a reduction that bottoms out at a lambda
--   literal is taken, so nothing else is ever moved.
--
-- Both rewrites reach a fixpoint at the application node, which matters for a
-- /curried/ spine: in @(if c then f else g) a b@ the outer application\'s callee
-- is itself an application, and only re-dispatching on it once rewritten keeps
-- an @if@ from being left in callee position.
--
-- What it deliberately does /not/ do: rewrite a callee that is already a bare
-- name. Forward chaining resolves a variable to the lambda it stands for by
-- itself, so a named callee — a top-level function, or a @let@-bound one — is
-- the one selection the existing engines see through; expanding it anyway
-- would move working programs onto a different path (and would not terminate
-- for a recursive function). Nor does it reach through a binding whose value is
-- itself randomly selected (@let p = if Uniform < 0.5 then f else g@), where
-- copying the selection to two use sites would turn one draw into two.
--
-- The pass runs on the freshly parsed program, before RType inference, so the
-- rewritten nodes need no annotations: every 'TypeInfo' is still @NotSetYet@
-- and the whole pipeline annotates the rewritten tree from scratch.
module SPLL.CalleeNormalize
  ( normalizeCallees
  ) where

import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Set as Set

import SPLL.Lang.Lang
import SPLL.Lang.Types

-- | The @let@-bound values in scope, innermost first. Only bindings introduced
-- by a directly-applied lambda go in here: a lambda parameter's value is not
-- known statically.
type Env = [(String, Expr)]

-- | One pass over every declaration body.
--
-- 'Nothing' when nothing was rewritten, which is the case for every program
-- that does not select a function value — the caller then has no new stage to
-- report.
normalizeCallees :: Program -> Maybe Program
normalizeCallees prog
  | rewritten == prog = Nothing
  | otherwise         = Just rewritten
  where
    rewritten = prog { functions = [ (n, rewrite (adts prog) [] body) | (n, body) <- functions prog ] }

-- | Rewrite one expression under the @let@-bindings enclosing it.
rewrite :: [ADTDecl] -> Env -> Expr -> Expr
rewrite decls env e = case node e of
  Apply l v            -> rewriteApply decls env (ann e) l v
  Lambda x lambdaBody  -> Expr (ann e) (Lambda x (rewrite decls (dropBinder x env) lambdaBody))
  -- An @if@ arm that projects a lambda literal out of a literal constructor
  -- is that lambda: the pointwise-lifted arrow mixture IRCompiler compiles
  -- for a randomly selected function value needs lambda arms, and an
  -- accessor on an arrow-typed tuple there compared closures and crashed
  -- (@draw f = (if Uniform < 0.5 then (\x -> 1.0) else snd (2.0, \y -> 3.0))
  -- in f True@, fuzz-admission-oracle-bugs item 3). The discarded components
  -- are unread, so dropping them changes no distribution. Only arms: a bare
  -- @draw f = snd (..)@ keeps its projection, which the callee rule below
  -- substitutes at the call instead.
  IfThenElse c t f -> Expr (ann e) (IfThenElse (rewrite decls env c) (arm t) (arm f))
    where arm a = rewrite decls env (fromMaybe a (reduceLiteralProjection decls a))
  other                -> Expr (ann e) (fmap (rewrite decls env) other)

-- | The application cases. @ti@ is the application node's own annotation, which
-- every node this builds inherits: they all stand for the same value, and at
-- this point in the pipeline it is @NotSetYet@ anyway.
rewriteApply :: [ADTDecl] -> Env -> TypeInfo -> Expr -> Expr -> Expr
rewriteApply decls env ti l v = case node l of
  -- `let x = v in body`. The callee is already a lambda literal; what this case
  -- is here for is to record the binding, so a use of `x` further in can be
  -- reduced by 'reduceCallee'.
  Lambda x lambdaBody ->
    let v' = rewrite decls env v
        bodyEnv = (x, v') : dropBinder x env
    in Expr ti (Apply (Expr (ann l) (Lambda x (rewrite decls bodyEnv lambdaBody))) v')
  -- An `if` choosing between function values: push the application into both
  -- arms. Re-walked, so a nested selection (`(if a then (if b then f else g)
  -- else h) x`) collapses in the same pass.
  IfThenElse c t f ->
    rewrite decls env (Expr ti (IfThenElse c (Expr ti (Apply t v)) (Expr ti (Apply f v))))
  -- A redex in callee position -- a @draw@, or a literal beta-redex -- has the
  -- outer application pushed into its body, the way an @if@ is pushed into its
  -- arms: @((\x -> body) a) v@ becomes @(\x -> body v) a@. The binder stays
  -- bound (a @draw@ is a sampling site and is not moved or duplicated), it is
  -- renamed first if @v@ reads a variable of the same name, and the body's
  -- application is then re-dispatched with @x@ in the environment, so a
  -- projection or an @if@ the body selects reaches the cases above. Left as it
  -- was, forward chaining met a callee that is neither a lambda nor a name
  -- (task callee-normalize-misses-redex-in-callee-position), and IRCompiler
  -- compiled the lambda the redex returns outside the scope binding its free
  -- variables (fuzz-admission-oracle-bugs item 7,
  -- @(\a -> \b -> a) 0.0 (if Uniform < 0.5 then 2 else 1)@).
  Apply (Expr lamTi (Lambda x0 body0)) a ->
    let (x, body) = freshBinder x0 body0
    in rewrite decls env (Expr ti (Apply (Expr lamTi (Lambda x (Expr ti (Apply body v)))) a))
  -- A *named* callee is left alone: forward chaining resolves a variable to the
  -- lambda it stands for by itself (that is what its equivalence classes are
  -- for), so this is the one selection the existing engines already see
  -- through. Substituting it anyway would rewrite working programs onto a
  -- different path -- `testCases/hoProbValueLambda` and `twiceApplication`
  -- both changed answer when an earlier draft did.
  -- A bare name is left alone (forward chaining resolves it), except when it
  -- stands for a lambda only through a projection -- @draw f = snd (Normal,
  -- \x -> Uniform) in f c@. Forward chaining cannot see through @snd@ of a
  -- tuple with a random sibling, and the compile died resolving @f@
  -- (fuzz-admission-oracle-bugs item 2). The lambda literal the projection
  -- selects is a value, so substituting it duplicates no draw.
  Var n
    | Just bound <- lookup n env
    , not (isLambdaLiteral bound)
    , Just lam <- reduceCallee decls env l -> Expr ti (Apply (rewrite decls env lam) (rewrite decls env v))
    | otherwise -> Expr ti (Apply l (rewrite decls env v))
  -- A callee that denotes a lambda literal: use the lambda. Only taken when the
  -- reduction really bottoms out at a `Lambda`, so a callee that stays a
  -- projection or a selection is left exactly as it was.
  _ | Just lam <- reduceCallee decls env l -> Expr ti (Apply (rewrite decls env lam) (rewrite decls env v))
  -- Fallthrough. The callee is some other expression -- most importantly an
  -- `Apply`, which is what the outer node of a *curried* spine
  -- `Apply (Apply (if ...) a) b` sees below it. Rewriting that callee turns it
  -- into an `IfThenElse` (the inner node distributes its own application into
  -- the arms), so rebuilding around the result would leave an `if` sitting in
  -- callee position at this node -- exactly the crash this pass exists to
  -- prevent, and why the one-argument twin worked while this one did not.
  --
  -- So dispatch again on the *rewritten* callee. `IfThenElse` is the only shape
  -- rewriting can newly expose: `rewrite` preserves the head constructor of
  -- every node except `Apply`, which it may turn into `IfThenElse`. That also
  -- bounds the recursion at one extra step, since the `IfThenElse` case
  -- consumes it rather than returning here.
  _ ->
    let l' = rewrite decls env l
    in case node l' of
         IfThenElse{} -> rewriteApply decls env ti l' v
         _            -> Expr ti (Apply l' (rewrite decls env v))

-- | The lambda literal a callee expression denotes, if that is statically
-- decidable: a literal lambda, a field of a tuple literal, an element of a list
-- literal, or a @let@-bound name standing for one of those, in any combination.
--
-- 'Nothing' for everything else — including a name bound to a randomly selected
-- function, whose selection must stay at its binding site.
  where
    freshBinder x0 body0
      | x0 `Set.member` freeVarsExpr v =
          let taken = Set.unions [freeVarsExpr v, varsOfExpr body0]
              x = head [ c | k <- [(1 :: Int) ..], let c = x0 ++ "_" ++ show k, not (Set.member c taken) ]
          in (x, renameFreeVar x0 x body0)
      | otherwise = (x0, body0)

-- | 'reduceCallee' without the environment: only literal constructor
-- applications are looked through, so no binding is ever copied.
reduceLiteralProjection :: [ADTDecl] -> Expr -> Maybe Expr
reduceLiteralProjection decls = reduceCallee decls []

isLambdaLiteral :: Expr -> Bool
isLambdaLiteral (Expr _ Lambda{}) = True
isLambdaLiteral _                 = False

reduceCallee :: [ADTDecl] -> Env -> Expr -> Maybe Expr
reduceCallee decls env l = case reduce [] l of
  lam@(Expr _ Lambda{}) -> Just lam
  _                     -> Nothing
  where
    -- Structural projection/lookup reduction. Returns the argument unchanged
    -- when there is nothing to reduce. @seen@ bounds the variable expansions by
    -- the size of the environment, so a malformed self-referential binding
    -- cannot loop.
    reduce seen e = case node e of
      Var n | n `notElem` seen, Just bound <- lookup n env -> reduce (n : seen) bound
      -- One projection step, stated once for every constructor rather than per
      -- accessor: an accessor applied to a literal application of the
      -- constructor it belongs to is that constructor's corresponding field.
      -- Both the built-in shapes (@fst@\/@snd@, @head@\/@tail@,
      -- @fromLeftPartial@\/@fromRightPartial@) and user-ADT field accessors are
      -- the same step, so they share the same case; 'accessorField' is the only
      -- thing that knows which is which.
      InjF (Named accessor) [p]
        | Expr _ (InjF (Named ctor) fields) <- reduce seen p
        , Just i <- accessorField decls ctor accessor
        , i < length fields -> reduce seen (fields !! i)
      _ -> e

-- | Which field of @ctor@ the accessor named @accessor@ projects out, if it is
-- an accessor of that constructor at all.
--
-- The built-in constructors are listed explicitly because their accessors are
-- not named after fields; a user ADT's are read off its declaration, where the
-- field name /is/ the accessor name ('SPLL.PredefinedFunctions.fPairsFromADT'
-- registers one @InjF@ per field under exactly that name).
--
-- Only the /partial/ Either extractors appear here. @fromLeft@ is the total,
-- @Maybe@-returning one — @fromLeft (left x)@ is @Right x@, not @x@ — so it is
-- not a projection and must not reduce like one.
--
-- A field name shared by sibling constructors is not ambiguous here, because
-- the constructor is already known: the lookup is keyed on the pair.
accessorField :: [ADTDecl] -> String -> String -> Maybe Int
accessorField decls ctor accessor = case (ctor, accessor) of
  ("TCons", "fst")               -> Just 0
  ("TCons", "snd")               -> Just 1
  ("Cons",  "head")              -> Just 0
  ("Cons",  "tail")              -> Just 1
  ("left",  "fromLeftPartial")   -> Just 0
  ("right", "fromRightPartial")  -> Just 0
  _ -> listToMaybe
         [ i
         | decl <- decls
         , (cName, fields) <- constructors decl
         , cName == ctor
         , (i, (fName, _)) <- zip [0 ..] fields
         , fName == accessor
         ]

-- | Names a binder shadows: drop its own entry, and any entry whose value
-- mentions it. Moving such a value inwards would rebind it to the wrong
-- binder. ('containedVars' over-approximates the free variables, which is the
-- safe direction.)
dropBinder :: String -> Env -> Env
dropBinder x env = [ (n, v) | (n, v) <- env, n /= x, not (Set.member x (containedVars varsOfExpr v)) ]
