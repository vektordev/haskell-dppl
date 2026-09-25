-- | Sinking an enumerable @draw@ into the one operand that reads it (task
-- @shared-enumerated-latent-loses-per-slot-factorization@).
--
-- IRCompiler enumerates a @draw@-bound discrete variable over the /whole/ body
-- of its binding. When several such draws are stacked, each over the next, the
-- enumeration is their joint, even where the body would let it factorize:
--
-- > draw c  = readQ q in
-- > draw o1 = readAttrs s1 in
-- > draw o2 = readAttrs s2 in
-- > (match c o1) ++ (match c o2)
--
-- nests the loops over @c@, @o1@ and @o2@ -- @8 * 97^2@ terms, @8 * 97^N@ at
-- @N@ slots -- although given @c@ the two summands are independent. Moving each
-- @o_i@ binding down to the summand that reads it,
--
-- > draw c = readQ q in
-- > (draw o1 = readAttrs s1 in match c o1) ++ (draw o2 = readAttrs s2 in match c o2)
--
-- leaves only @c@ shared, and the enumerable-'InjF' rules then convolve the
-- summands one at a time inside the loop over @c@: @8 * N * 97@ terms.
--
-- __Why this is sound.__ A @draw@ is one eager sample shared by every use of
-- the name (@designs/let-binding-semantics.md@). Every rewrite here keeps the
-- binding evaluated at most once and keeps every use of the name under it:
--
-- * commuting two directly nested bindings, @draw x = e in draw y = e2 in b@
--   to @draw y = e2 in draw x = e in b@, when @e2@ does not read @x@ and @e@
--   does not read @y@ -- two independent draws in either order;
-- * moving a binding into the single operand of an 'InjF' that reads it. An
--   operand is evaluated at most once per evaluation of the 'InjF', never under
--   a binder of its own, so the draw is still made once and its value is still
--   shared by every use. This is only done when some /other/ operand may be
--   random: separating the binding from literal siblings (@x == Red@) takes
--   nothing out of its enumeration, and would only move a working program onto
--   a different path.
--
-- It never moves a binding under a 'Lambda' that is not itself a binding (a
-- closure may be applied many times, and each application would draw again),
-- nor into an @if@ arm or a function argument, where it would buy nothing.
--
-- __Scope.__ Only bindings whose value carries a 'DiscreteValues' tag and may
-- be random are moved -- the ones IRCompiler enumerates as a latent -- which is
-- why this runs after enum annotation, and why the rewritten program is
-- annotated again. A binding is
-- moved only when it reaches an 'InjF' operand; a rewrite that would only
-- commute it past other bindings is not taken, so a program with nothing to
-- factorize is returned unchanged. A binding whose body is exactly its own
-- variable after sinking (@draw x = e in x@) is replaced by @e@.
module SPLL.DrawSinking
  ( sinkEnumerableDraws
  ) where

import qualified Data.Set as Set

import SPLL.Lang.Lang (freeVarsExpr, getSubExprs, getTypeInfo, setSubExprs)
import SPLL.Lang.Types
import SPLL.Typing.RType (RType (TArrow))

-- | Sink every enumerable binding in every declaration body. 'Nothing' when
-- nothing moved, so the caller has no new stage to report.
sinkEnumerableDraws :: Program -> Maybe Program
sinkEnumerableDraws prog
  | rewritten == prog = Nothing
  | otherwise         = Just rewritten
  where
    rewritten = prog { functions = [ (n, sinkIn body) | (n, body) <- functions prog ] }

sinkIn :: Expr -> Expr
sinkIn e = case e of
  Expr ti (Apply (Expr _ (Lambda x b)) v)
    | isEnumerableValue v
    , Just moved <- sinkDraw x v ti b -> sinkIn moved
  _ -> setSubExprs e (map sinkIn (getSubExprs e))

-- | A binding worth moving: its value is enumerable (IRCompiler would loop
-- over it) and may be random. The second half is syntactic, because this runs
-- before ModalityInfer: a value built from literals alone (@draw a = 1.0@) is
-- deterministic, so moving it could buy nothing, and it would only move the
-- corpus programs that exist to exercise a deterministic binding off the path
-- they test. Anything that reads a variable or a network may be random.
isEnumerableValue :: Expr -> Bool
isEnumerableValue v =
     not (null [() | DiscreteValues _ <- tags (getTypeInfo v)])
  && mayBeRandom v

-- | Syntactically, may this expression be random? Anything reading a variable
-- (a distribution, a random binding or parameter, a random top-level function)
-- or a network may be; literals alone are not.
mayBeRandom :: Expr -> Bool
mayBeRandom (Expr _ (Var _)) = True
mayBeRandom (Expr _ (ReadNN _ _)) = True
mayBeRandom e = any mayBeRandom (getSubExprs e)

-- | @draw x = v in b@ with the binding moved as far down @b@ as it can go, or
-- 'Nothing' if it cannot reach an 'InjF' operand. @letTi@ is the original
-- binding's annotation, whose source span the moved binding keeps.
sinkDraw :: String -> Expr -> TypeInfo -> Expr -> Maybe Expr
sinkDraw x v letTi b = case b of
  Expr ti (Apply (Expr lti (Lambda y inner)) v2)
    | y /= x
    , not (x `Set.member` freeVarsExpr v2)
    , not (y `Set.member` freeVarsExpr v) -> do
        inner' <- sinkDraw x v letTi inner
        return (Expr ti (Apply (Expr lti (Lambda y inner')) v2))
  Expr ti (InjF f ps)
    | length ps >= 2
    , [i] <- [i | (i, p) <- zip [0 :: Int ..] ps, x `Set.member` freeVarsExpr p]
    , any mayBeRandom [p | (j, p) <- zip [0 ..] ps, j /= i] ->
        let place p = case sinkDraw x v letTi p of
              Just moved -> moved
              Nothing -> bindAt p
        in Just (Expr ti (InjF f [if j == i then place p else p | (j, p) <- zip [0 ..] ps]))
  _ -> Nothing
  where
    bindAt (Expr _ (Var y)) | y == x = v
    bindAt p =
      let pTy = rType (getTypeInfo p)
          lamTi = makeTypeInfo { rType = TArrow (rType (getTypeInfo v)) pTy }
          appTi = makeTypeInfo { rType = pTy, srcPos = srcPos letTi }
      in Expr appTi (Apply (Expr lamTi (Lambda x p)) v)
