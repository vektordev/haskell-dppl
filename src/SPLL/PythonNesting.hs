{-# LANGUAGE FlexibleContexts #-}
-- | CPython's two per-line limits, and the spill that keeps an emitted line
-- inside the bracket one -- shared by the scalar ('SPLL.CodeGenPyTorch') and
-- batched ('SPLL.CodeGenPyTorchBatched') Python backends
-- (tasks python-codegen-exceeds-parser-nesting-limit, and for the batched
-- backend batched-enum-comprehension-exceeds-parser-nesting).
module SPLL.PythonNesting
  ( pythonMaxNesting
  , pythonNestingDepth
  , tooDeepForPython
  , spillable
  , spillDeep
  , renameFree
  , pythonMaxIndent
  , blockIndent
  ) where

import SPLL.IntermediateRepresentation
import Data.List (isSuffixOf)
import Utils (Supply, demandUniqueNumber)

-- CPython's tokenizer refuses to open a 201st bracket level in one logical
-- line (@MAXLEVEL@, "too many nested parentheses"). That is a constant of the
-- interpreter, not a recursion limit a caller can raise, so a module whose
-- deepest line goes past it can never be imported -- @forward@ and @generate@
-- go down with it. The IR builds long sums right-nested (a plan route's world
-- sum, 'SPLL.Semiring.mixP' folded over hundreds of worlds), and every level
-- of an 'IROp' is parenthesised, so ~190 worlds are enough.
--
-- The fix is local to the two Python backends, because the limit is: each
-- emitted line is rendered as before and measured ('pythonNestingDepth'); only
-- a line past 'pythonMaxNesting' ('tooDeepForPython') is regenerated with its
-- deep subterms let-bound into temporaries first ('spillDeep'). Every module
-- that parsed before is therefore byte-identical. The walk and its admission
-- rules live here; each backend drives them from its own line renderer
-- ('SPLL.CodeGenPyTorch.liftedLine', 'SPLL.CodeGenPyTorchBatched.batchedLine')
-- and emits the bindings, a spilled comprehension as a loop, itself.
--
-- Hoisting a subterm into a preceding statement evaluates it earlier and
-- unconditionally, so only two kinds of subterm move:
--
-- * one in a /strict/ position -- a position Python evaluates whenever the
--   line runs: an operand of an arithmetic/comparison operator, the condition
--   of a conditional expression, a constructor or accessor argument, ...
--   Never an arm of a conditional expression, the right operand of the
--   short-circuiting @and@/@or@, or anything under a binder (a lambda or a
--   comprehension body), since the guard is what protects it and the binder
--   is not in scope before the line. (A pure comprehension can still move
--   /whole/, becoming a statement-level loop: see 'spillable'.);
-- * one that is /pure arithmetic/ ('spillable'): no random draw, no call
--   other than of an inference method ('inferenceMethodCall'). Any other call
--   may be a generator or may not terminate, and moving it ahead of a sibling
--   could change which draw or which failure is observed. A spilled
--   subterm may itself contain a whole conditional expression -- it is moved
--   intact, with its guard.
--
-- Every free name of a spilled subterm is already bound before the line,
-- because the only binders the walk crosses are 'IRLetIn's, which it turns
-- into statements ahead of the spills they scope over (the same thing the
-- scalar backend's 'generateExpressionLifted' does to them anyway).
--
-- The Julia backend is a separate emitter and is not covered by this; it has
-- not been checked against a deep line.

-- | CPython's @MAXLEVEL@: the deepest bracket nesting one line may reach.
pythonMaxNesting :: Int
pythonMaxNesting = 200

-- | The estimated nesting at which 'spillDeep' cuts a subterm out. Well below
-- 'pythonMaxNesting', since the estimate is structural and the line keeps
-- whatever cannot be spilled.
spillNestingThreshold :: Int
spillNestingThreshold = 64

-- | Whether a rendered line opens more brackets than CPython accepts.
tooDeepForPython :: String -> Bool
tooDeepForPython line = pythonNestingDepth line > pythonMaxNesting

-- | The deepest bracket nesting (@(@, @[@, @{@) of a rendered Python line,
-- ignoring brackets inside string literals.
pythonNestingDepth :: String -> Int
pythonNestingDepth = go 0 0
  where
    go _ m [] = m
    go d m (c:cs)
      | c == '"' || c == '\'' = go d m (skipString c cs)
      | c `elem` "([{"       = let d' = d + 1 in go d' (max m d') cs
      | c `elem` ")]}"       = go (d - 1) m cs
      | otherwise            = go d m cs
    skipString _ [] = []
    skipString q ('\\':_:cs) = skipString q cs
    skipString q (c:cs)
      | c == q    = cs
      | otherwise = skipString q cs

-- | A subterm that may be evaluated ahead of its line: pure arithmetic over
-- names -- no random draw, no generator reference, no call, no lambda. (Tensor
-- and list builtins such as an index are pure; one carrying a lambda is ruled
-- out by the lambda.)
--
-- An 'IRLetIn' is admitted when its value and body are: its binder scopes
-- only over its own body, which moves with it, so every free name of the
-- subterm is still bound before the line. The let stays where it was inside
-- the subterm -- one under a conditional's arm is still guarded by it, since
-- the conditional moves whole ('generateLetInStatement' emits it as an
-- @if@/@else@ statement with the let inside the arm). Refusing lets made a
-- sum's spine unspillable above any summand that carries a CSE let in an arm,
-- which is what a plan-path fold's enumerated mass looks like (task
-- plan-fold-enum-mass-sum-exceeds-parser-nesting): the summands were cut out
-- one by one and the ~200-deep chain of @+@ over them stayed on the line.
--
-- One kind of call is admitted: a call of a function group's own inference
-- method ('inferenceMethodCall'), with spillable arguments. That is what a
-- function's writeLogits is made of -- one @main.forward(v, x)[0]@ cell per
-- slot of its output plan, consed right-nested, so a V-valued @main@ is a
-- V-deep line (task writelogits-cons-chain-nests-v-deep). The objection to
-- hoisting a call does not apply to these: a probability or cumulative method
-- draws nothing a generator would (it may read a network, which is the same
-- read wherever it happens), and it only ever moves out of a strict position,
-- so the line evaluated it unconditionally anyway. The one thing a reorder can
-- change is which of several failing cells raises first -- the line fails
-- either way.
spillable :: [String] -> IRExpr -> Bool
spillable callables = go
  where
    go (IRSample _)   = False
    go e@(IRApply _ _) =
      let (f, args) = collectApplyChain e
      in inferenceMethodCall f && all go args
    -- A comprehension whose body and list are pure. A bare lambda is
    -- refused below, which is right for one that stays a value, but a 'BMap'
    -- applies its lambda on the spot to every element, so moving the whole
    -- comprehension is the same move as moving any other pure subterm. It is
    -- emitted as a statement-level loop ('generateSpillStatement').
    --
    -- This is what reaches a line whose depth is /inside/ a comprehension
    -- body (task python-emitted-expression-exceeds-parser-nesting): an
    -- enumerated 'draw' sums @[body for b in xs]@, and the body -- a chain of
    -- CSE lets and conditionals rendered as walrus tuples -- is ~10 levels
    -- per nested @if@, with nothing on the strict spine outside it to cut.
    -- Purity is checked recursively, so a comprehension whose body holds
    -- another enumerated draw's comprehension moves too (task
    -- chained-answers-exceed-python-paren-depth); the inner one, out of
    -- reach under the outer binder before, then sits on a line of its own.
    go (IRBuiltin BMap [IRLambda _ body, t]) = go body && go t
    go (IRLambda _ _) = False
    go (IRVar n)      = not (n `elem` callables || isEffectfulVar n
                             || ".generate" `isSuffixOf` n)
    go e              = all go (getIRSubExprs e)

-- | The callee of a call 'spillable' admits: a function group's probability
-- or cumulative method, as 'envToLUT' renamed it (@n.forward@ for @n_prob@,
-- @n.integrate@ for @n_integ@). A generator (@n.generate@), a normal-params
-- method and a bare network or lambda are not admitted.
inferenceMethodCall :: IRExpr -> Bool
inferenceMethodCall (IRVar n) = ".forward" `isSuffixOf` n || ".integrate" `isSuffixOf` n
inferenceMethodCall _ = False

-- | Rename the free occurrences of one variable, stopping under a binder that
-- shadows it.
renameFree :: String -> String -> IRExpr -> IRExpr
renameFree old new = go
  where
    go e = case e of
      IRVar v | v == old -> IRVar new
      IRLetIn n val b | n == old -> IRLetIn n (go val) b
      IRLambda n _ | n == old -> e
      _ -> irDescend go e

-- | The children of a node Python evaluates whenever the node is evaluated,
-- with a function rebuilding the node from replacements for them. 'Nothing'
-- for a leaf, a binder, or a node whose operands are not all strict in a way
-- this can express.
strictChildren :: IRExpr -> Maybe ([IRExpr], [IRExpr] -> IRExpr)
strictChildren expr = case expr of
  IRIf c l r -> Just ([c], \cs -> IRIf (one cs) l r)
  -- A select is the batched backend's @torch.where@ (the scalar backend
  -- desugars every one back to an 'IRIf' first): a call, so all three
  -- operands are evaluated whenever it is.
  IRSelect c t f -> Just ([c, t, f], \cs -> case cs of
                                             [c', t', f'] -> IRSelect c' t' f'
                                             _ -> arityError)
  IROp OpAnd l r -> Just ([l], \cs -> IROp OpAnd (one cs) r)
  IROp OpOr l r -> Just ([l], \cs -> IROp OpOr (one cs) r)
  IROp op l r -> Just ([l, r], \cs -> case cs of
                                        [l', r'] -> IROp op l' r'
                                        _ -> arityError)
  IRUnaryOp op x -> Just ([x], IRUnaryOp op . one)
  IRDensity d ls x -> Just ([x], IRDensity d ls . one)
  IRCumulative d ls x -> Just ([x], IRCumulative d ls . one)
  IRDestruct a x -> Just ([x], IRDestruct a . one)
  IRConstruct t xs -> Just (xs, IRConstruct t)
  IRConformsTo t x -> Just ([x], IRConformsTo t . one)
  IRIsPossible mv x -> Just ([x], IRIsPossible mv . one)
  -- A lambda argument (a 'BMap' body) is a leaf to the walk and never
  -- spillable, so only the builtin's value operands can move.
  IRBuiltin b xs -> Just (xs, IRBuiltin b)
  -- Python evaluates the callee and every argument before the call. The spine
  -- is taken whole, since this backend uncurries it into one call.
  IRApply _ _ -> let (f, args) = collectApplyChain expr
                 in Just (f : args, \cs -> case cs of
                                             (f' : args') -> foldl IRApply f' args'
                                             [] -> arityError)
  _ -> Nothing
  where
    one [x] = x
    one _ = arityError
    arityError = error "strictChildren: rebuilt with the wrong number of children"

-- | The structural nesting estimate of a subterm: one level per node. An
-- over-estimate of the rendered bracket depth is harmless (it only spills a
-- little early, on a line that has to change anyway).
nestingEstimate :: IRExpr -> Int
nestingEstimate e = case getIRSubExprs e of
  [] -> 0
  cs -> 1 + maximum (map nestingEstimate cs)

-- | Cut the deep strict subterms of a line into let-bindings, returning the
-- bindings in evaluation order and the residual expression. The walk is
-- bottom-up: at a node whose estimated nesting passes
-- 'spillNestingThreshold', every compound, 'spillable' strict child is
-- replaced by a fresh variable, so the node's depth starts over from one.
spillDeep :: [String] -> IRExpr -> Supply ([(String, IRExpr)], IRExpr)
spillDeep callables e0 = do
  (binds, e', _) <- go e0
  return (binds, e')
  where
    go (IRLetIn n v b) = do
      (bb, b', d) <- go b
      return ((n, v) : bb, b', d)
    go expr = case strictChildren expr of
      Nothing -> return ([], expr, nestingEstimate expr)
      Just (kids, rebuild) -> do
        results <- mapM go kids
        let lazyDepth = maximum (0 : map nestingEstimate (lazyChildren expr))
            depth = 1 + maximum (lazyDepth : [d | (_, _, d) <- results])
        if depth <= spillNestingThreshold
          then return (concat [b | (b, _, _) <- results], rebuild [k | (_, k, _) <- results], depth)
          else do
            cut <- mapM spillOne results
            let binds = concat [b | (b, _, _) <- cut]
                kids' = [k | (_, k, _) <- cut]
            return (binds, rebuild kids', 1 + maximum (lazyDepth : [d | (_, _, d) <- cut]))
    spillOne (b, k, d)
      | compound k && spillable callables k = do
          n <- demandUniqueNumber
          let tmp = "_s" ++ show n
          return (b ++ [(tmp, k)], IRVar tmp, 0)
      | otherwise = return (b, k, d)
    compound (IRVar _) = False
    compound (IRConst _) = False
    -- A literal of constants -- an enumeration domain, what every 'BMap' the
    -- compiler builds maps over -- is one bracket level, so cutting it gains
    -- nothing. Kept in place it stays visible as constants to the batched
    -- backend, which binds a map variable over one as structure
    -- ('SPLL.CodeGenPyTorchBatched.bindMap').
    compound (IRBuiltin (BTensor _) xs) = not (all isConst xs)
    compound _ = True
    isConst (IRConst _) = True
    isConst _ = False
    -- The children 'strictChildren' leaves in place: they still count towards
    -- the node's depth.
    lazyChildren expr = case expr of
      IRIf _ l r -> [l, r]
      IROp OpAnd _ r -> [r]
      IROp OpOr _ r -> [r]
      _ -> []

-- ---------------------------------------------------------------------------
-- Indentation. The scalar backend hoists a method's deep blocks into local
-- functions past this ('SPLL.CodeGenPyTorch.generateMethodBody'); the batched
-- one has no statement nesting that deep.
-- ---------------------------------------------------------------------------

-- | CPython's @MAXINDENT@ less one: the deepest indentation level a line may
-- have.
pythonMaxIndent :: Int
pythonMaxIndent = 99

-- | The deepest indentation level among some emitted lines, relative to them.
blockIndent :: [String] -> Int
blockIndent ls = maximum (0 : map ((`div` 4) . length . takeWhile (== ' ')) ls)
