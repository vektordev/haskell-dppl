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
-- * moving a binding into the value of a directly nested binding, @draw x = e
--   in draw y = v2 in b@ to @draw y = (draw x = e in v2) in b@, when only @v2@
--   reads @x@ -- @v2@ is itself evaluated exactly once, so @x@ still is;
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

import Data.Maybe (isJust)
import qualified Data.Set as Set

import SPLL.Lang.Lang (freeVarsExpr, getSubExprs, getTypeInfo, multiValueContainsContinuous, setSubExprs)
import SPLL.Lang.Types
import SPLL.Typing.RType (RType (TADT, TArrow))

-- | Sink every enumerable binding in every declaration body. 'Nothing' when
-- nothing moved, so the caller has no new stage to report.
sinkEnumerableDraws :: Program -> Maybe Program
sinkEnumerableDraws prog
  | rewritten == prog = Nothing
  | otherwise         = Just rewritten
  where
    rewritten = prog { functions = [ (n, sinkIn (adts prog) (namesIn body) body) | (n, body) <- functions prog ] }

-- | @adtDecls@ to recognise a product read, @taken@ every name the declaration
-- body already uses, so the per-field names 'splitProductDraw' invents are fresh.
sinkIn :: [ADTDecl] -> Set.Set String -> Expr -> Expr
sinkIn adtDecls taken e = case e of
  Expr ti (Apply (Expr _ (Lambda x b)) v)
    | Just split <- splitProductDraw adtDecls taken x v ti b ->
        sinkIn adtDecls (taken `Set.union` namesIn split) split
    | isEnumerableValue v
    , Just moved <- sinkDraw x v ti b -> sinkIn adtDecls taken moved
  _ -> setSubExprs e (map (sinkIn adtDecls taken) (getSubExprs e))

-- | A binding worth moving: its value is enumerable (IRCompiler would loop
-- over it) and may be random. The second half is syntactic, because this runs
-- before ModalityInfer: a value built from literals alone (@draw a = 1.0@) is
-- deterministic, so moving it could buy nothing, and it would only move the
-- corpus programs that exist to exercise a deterministic binding off the path
-- they test. Anything that reads a variable or a network may be random.
isEnumerableValue :: Expr -> Bool
isEnumerableValue v =
     not (null [() | DiscreteValues mv <- tags (getTypeInfo v), not (multiValueContainsContinuous mv)])
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
  Expr ti (Apply (Expr lti (Lambda y inner)) v2)
    | y /= x
    , x `Set.member` freeVarsExpr v2
    , not (x `Set.member` freeVarsExpr inner) -> do
        v2' <- sinkDraw x v letTi v2
        return (Expr ti (Apply (Expr lti (Lambda y inner)) v2'))
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

-- | Every name an expression mentions, bound or free.
namesIn :: Expr -> Set.Set String
namesIn (Expr _ (Var y)) = Set.singleton y
namesIn (Expr _ (Lambda y b)) = Set.insert y (namesIn b)
namesIn e = Set.unions (map namesIn (getSubExprs e))

-- | Split one draw of a product-distributed read into one draw per field read
-- (task @draw-product-read-enumerated-jointly@):
--
-- > draw t = see img in Face (tells .. (x0 t)) .. (tells .. (xJ t))
--
-- becomes
--
-- > draw t_x0 = x0 (see img) in .. draw t_xJ = xJ (see img) in
-- > Face (tells .. t_x0) .. (tells .. t_xJ)
--
-- after which 'sinkDraw' moves each per-field draw into the operand that reads
-- it, so the fields are enumerated one at a time (@2J@ terms) instead of
-- jointly (@2^J@).
--
-- __Why this is sound.__ Two conditions, both checked here:
--
-- * /The drawn value is a product over its fields./ It is a neural read
--   ('ReadNN') of an ADT with a single constructor. AutoNeural lays such a read
--   out as an 'ADTPlan' with no constructor flag and one independent block of
--   logits per field (@makePartitionPlan@ builds an 'ADTPlan' for every 'TADT'
--   output, whatever the @of@ clause), so its law is the product of the field
--   marginals. A multi-constructor ADT is not a product -- the constructor
--   choice couples the fields -- and is left alone, as is any other source.
-- * /The body reads the value only through field accessors./ Then the body is a
--   function of the read fields alone, and drawing each field from its own read
--   gives the fields the same joint law as drawing the whole value once: the
--   product of the same marginals. Each field is still drawn once, and every
--   use of it shares that draw, so a field read by several operands keeps its
--   readers together under one binding (and 'sinkDraw' leaves that binding
--   above them). A body that uses the value whole (@isFace t@, or @t@ passed
--   on) is not split.
--
-- __Scope.__ Like the moves below, the split is taken only when it pays: when
-- at least one per-field draw then reaches an 'InjF' operand of its own. Reads
-- whose fields all meet in one @if@ or one operand gain nothing from it and
-- keep their single draw, so the plan engine's accessor descent still sees
-- them (@planEnumInlineADT@ at budget 0 is one).
--
-- The read's argument is evaluated once in the original, so unless it is a
-- variable or a constant it is bound first (@draw a = arg in .. see a ..@)
-- rather than copied into every field's read, which would draw it again per
-- field if it is random. Only fields whose own domain is wholly discrete are
-- split (an accessor of a continuous field would turn into a continuous
-- @draw@); one such field anywhere leaves the whole binding alone.
splitProductDraw :: [ADTDecl] -> Set.Set String -> String -> Expr -> TypeInfo -> Expr -> Maybe Expr
splitProductDraw adtDecls taken x v letTi b = do
  Expr readTi (ReadNN net arg) <- Just v
  TADT tyName <- Just (rType readTi)
  [ADTDecl { constructors = [(_, fieldDecls)] }] <- Just [d | d <- adtDecls, dataName d == tyName]
  let fieldNames = map fst fieldDecls
  uses <- accessorReads fieldNames x b
  let fieldsRead = [ f | f <- fieldNames, f `elem` map fst uses ]
  if null fieldsRead || not (all (hasEnumerableTag . snd) uses) then Nothing else do
    let fresh used base = head [ n | n <- base : [base ++ "_" ++ show i | i <- [(1 :: Int) ..]]
                                   , not (n `Set.member` used) ]
        -- one fresh name per field read, then one for the argument, each
        -- avoiding the names already handed out
        (names, used') = foldl (\(acc, used) f -> let n = fresh used (x ++ "_" ++ f)
                                                   in (acc ++ [(f, n)], Set.insert n used))
                               ([], taken) fieldsRead
        argName = fresh used' (x ++ "_arg")
        argIsAtomic = case arg of
          Expr _ (Var _) -> True
          Expr _ (Constant _) -> True
          _ -> False
        argRef = if argIsAtomic then arg else Expr (getTypeInfo arg) (Var argName)
        readOf f = let ti = head [ ati | (g, ati) <- uses, g == f ]
                   in Expr ti (InjF (Named f) [Expr readTi (ReadNN net argRef)])
        body' = substAccessors x names b
        bindings = [ (n, readOf f) | (f, n) <- names ]
        withFields = foldr (\(n, rhs) inner -> bindAs letTi n rhs inner) body' bindings
        sinks (n, rhs) = isJust (sinkDraw n rhs letTi body')
    if not (any sinks bindings) then Nothing else
      return (if argIsAtomic then withFields else bindAs letTi argName arg withFields)
  where
    hasEnumerableTag ti =
      not (null [() | DiscreteValues mv <- tags ti, not (multiValueContainsContinuous mv)])

-- | @draw n = rhs in body@, built with the same span as the binding it came
-- from and the arrow type the later stages expect of a binding's lambda.
bindAs :: TypeInfo -> String -> Expr -> Expr -> Expr
bindAs letTi n rhs body =
  let bodyTy = rType (getTypeInfo body)
      lamTi = makeTypeInfo { rType = TArrow (rType (getTypeInfo rhs)) bodyTy }
      appTi = makeTypeInfo { rType = bodyTy, srcPos = srcPos letTi }
  in Expr appTi (Apply (Expr lamTi (Lambda n body)) rhs)

-- | Every free use of @x@ in an expression, as the field it reads and the
-- accessor node's annotation, or 'Nothing' if some use is not a field accessor
-- of one of @fields@ applied directly to @x@.
accessorReads :: [String] -> String -> Expr -> Maybe [(String, TypeInfo)]
accessorReads fields x = go
  where
    go (Expr ti (InjF (Named f) [Expr _ (Var y)]))
      | y == x = if f `elem` fields then Just [(f, ti)] else Nothing
    go (Expr _ (Var y)) | y == x = Nothing
    go (Expr _ (Lambda y _)) | y == x = Just []
    go e = concat <$> mapM go (getSubExprs e)

-- | Replace each free @f x@ by the variable standing for field @f@.
substAccessors :: String -> [(String, String)] -> Expr -> Expr
substAccessors x names = go
  where
    go e@(Expr ti (InjF (Named f) [Expr _ (Var y)]))
      | y == x, Just n <- lookup f names = Expr ti (Var n)
      | otherwise = e
    go e@(Expr _ (Lambda y _)) | y == x = e
    go e = setSubExprs e (map go (getSubExprs e))
