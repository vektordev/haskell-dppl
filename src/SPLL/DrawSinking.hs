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

import Data.List (partition)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Set as Set

import SPLL.Analysis (enumerableDomain)
import SPLL.Lang.Lang (freeVarsExpr, getSubExprs, getTypeInfo, setSubExprs)
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
     isJust (enumerableDomain (tags (getTypeInfo v)))
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
    , [i] <- [i | (i, p) <- zip [0 :: Int ..] ps, x `Set.member` freeVarsExpr p] ->
        let reader = ps !! i
            rebuild p' = Expr ti (InjF f [if j == i then p' else p | (j, p) <- zip [0 ..] ps])
        in if any mayBeRandom [p | (j, p) <- zip [0 ..] ps, j /= i]
             then Just (rebuild (fromMaybe (bindAt reader) (sinkDraw x v letTi reader)))
             -- Literal siblings only: stopping here buys nothing, but the
             -- binding may still reach an operand further down that does pay
             -- (@[True, (draw .. in ..), ..]@, which is also what a masked
             -- slot leaves behind).
             else rebuild <$> sinkDraw x v letTi reader
  _ -> Nothing
  where
    bindAt (Expr _ (Var y)) | y == x = v
    bindAt p =
      let pTy = rType (getTypeInfo p)
          lamTi = makeTypeInfo { rType = TArrow (rType (getTypeInfo v)) pTy }
          -- the binding's value is the operand's, so it keeps the operand's
          -- tags: a later split or sink asks whether it is enumerable
          appTi = makeTypeInfo { rType = pTy, tags = tags (getTypeInfo p), srcPos = srcPos letTi }
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
  source <- productSource adtDecls v
  let fieldNames = map fst (sourceFields source)
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
        accessorTi f = head [ ati | (g, ati) <- uses, g == f ]
        (fieldValue, wrapArg) = case source of
          ProductRead readTi net arg _ ->
            let argIsAtomic = case arg of
                  Expr _ (Var _) -> True
                  Expr _ (Constant _) -> True
                  _ -> False
                argRef = if argIsAtomic then arg else Expr (getTypeInfo arg) (Var argName)
            in ( \f -> Expr (accessorTi f) (InjF (Named f) [Expr readTi (ReadNN net argRef)])
               , if argIsAtomic then id else bindAs letTi argName arg )
          ProductCtor fieldArgs _ ->
            (\f -> head [ a | (g, a) <- fieldArgs, g == f ], id)
        body' = substAccessors x names b
        bindings = [ (n, fieldValue f) | (f, n) <- names ]
        withFields = foldr (\(n, rhs) inner -> bindAs letTi n rhs inner) body' bindings
        sinks (n, rhs) = sourceSinksAny source rhs && isJust (sinkDraw n rhs letTi body')
        fieldVars = Set.fromList [ n | (n, rhs) <- bindings, sourceSinksAny source rhs ]
    if not (any sinks bindings || splitsIntoGroups adtDecls fieldVars body') then Nothing else
      return (wrapArg withFields)
  where
    hasEnumerableTag ti = isJust (enumerableDomain (tags ti))

-- | Does a split pay because the body is a constructor whose operands read the
-- per-field draws in two independent groups or more (task
-- answer-record-shared-fields-enumerated-jointly)? Such a draw is read by
-- several operands and so sinks nowhere, but IRCompiler's @drawStack@ takes
-- the product over the groups of a constructor under a stack of draws, which
-- only per-field draws expose:
--
-- > draw f = see img in Ans (a1 f) (b1 f) (a1 f && b1 f) (a2 f) (b2 f) (a2 f && b2 f)
--
-- enumerates all of @f@ unsplit, and split, the groups @{a1, b1}@ and
-- @{a2, b2}@ apart. The body is looked at through the bindings above the
-- constructor, as the stack IRCompiler walks would be, and an operand reading
-- one of those bindings reads what its value reads. This only estimates
-- IRCompiler's grouping (which also links through random enclosing locals);
-- an over-estimate only splits a draw IRCompiler then enumerates as before.
splitsIntoGroups :: [ADTDecl] -> Set.Set String -> Expr -> Bool
splitsIntoGroups adtDecls fieldVars = go []
  where
    go stack (Expr _ (Apply (Expr _ (Lambda y b)) v)) = go ((y, freeVarsExpr v) : stack) b
    go stack (Expr _ (InjF (Named c) ops))
      | [n] <- [ length fs | d <- adtDecls, (c', fs) <- constructors d, c' == c ], n >= 2 =
          countGroups [ r | op <- ops, let r = closure stack (freeVarsExpr op)
                          , not (Set.null (r `Set.intersection` fieldVars)) ] >= 2
    go _ _ = False
    -- what an operand reads, through the bindings between the split and the
    -- constructor: a binding read brings in what its value reads
    closure stack rs =
      let step r = Set.unions (r : [ vs | (y, vs) <- stack, y `Set.member` r ])
          r' = step rs
      in if r' == rs then rs else closure stack r'
    -- connected components of the operands, two linked when they read a
    -- common field or binding
    countGroups [] = 0 :: Int
    countGroups (s : rest) =
      let grow acc pending =
            let (touch, others) = partition (not . Set.null . Set.intersection acc) pending
            in if null touch then (acc, others) else grow (Set.unions (acc : touch)) others
          (_, remaining) = grow s rest
      in 1 + countGroups remaining

-- | Where the fields of a split draw come from.
data ProductSource
  = -- | A neural read of a single-constructor ADT: its type, network, argument
    -- and fields.
    ProductRead TypeInfo String Expr [(String, RType)]
    -- | A constructor application, @C a1 .. an@ (task
    -- @draw-bound-scene-intermediate-loses-probability@): each field paired
    -- with its argument, plus the declaration's fields.
  | ProductCtor [(String, Expr)] [(String, RType)]

sourceFields :: ProductSource -> [(String, RType)]
sourceFields (ProductRead _ _ _ fs) = fs
sourceFields (ProductCtor _ fs) = fs

-- | Is moving this per-field draw worth a split? For a read, every field is a
-- random enumerable draw. For a constructor application, only a field whose
-- argument 'mayBeRandom', as 'sinkIn' asks of any draw it moves (the field's
-- enumerability is its accessor's tag, checked by the caller): a literal argument (@C 1 x@) is not drawn, and splitting it out could
-- only move a program off the path it exercises.
sourceSinksAny :: ProductSource -> Expr -> Bool
sourceSinksAny ProductRead {} _ = True
sourceSinksAny ProductCtor {} rhs = mayBeRandom rhs

-- | A drawn value whose law is the product of its fields' laws, given the
-- values its parts read.
--
-- * A neural read of a single-constructor ADT (see 'splitProductDraw').
-- * An application of a constructor to all its fields, @C a1 .. an@, of any
--   ADT. The constructor is fixed, so the fields do not couple through it; each
--   @a_i@ is evaluated once, in the original and as its own draw alike, and the
--   fields' joint law is whatever the @a_i@ share through the variables they
--   read, which the per-field draws read too. That is the edit-chain shape,
--   @draw s1 = Scene (edit (o1 s0)) .. (edit (oN s0)) in .. (o1 s1) ..@, which
--   otherwise enumerates @s1@ over its joint domain (@3^N@ values for a
--   two-colour object) and is refused past the materialization budget.
productSource :: [ADTDecl] -> Expr -> Maybe ProductSource
productSource adtDecls v = case v of
  Expr readTi (ReadNN net arg) -> do
    TADT tyName <- Just (rType readTi)
    [ADTDecl { constructors = [(_, fieldDecls)] }] <- Just [d | d <- adtDecls, dataName d == tyName]
    return (ProductRead readTi net arg fieldDecls)
  Expr ti (InjF (Named c) args) -> do
    TADT tyName <- Just (rType ti)
    [fieldDecls] <- Just [ fs | d <- adtDecls, dataName d == tyName, (c', fs) <- constructors d, c' == c ]
    if null fieldDecls || length fieldDecls /= length args then Nothing else
      return (ProductCtor (zip (map fst fieldDecls) args) fieldDecls)
  _ -> Nothing

-- | @draw n = rhs in body@, built with the same span as the binding it came
-- from and the arrow type the later stages expect of a binding's lambda.
bindAs :: TypeInfo -> String -> Expr -> Expr -> Expr
bindAs letTi n rhs body =
  let bodyTy = rType (getTypeInfo body)
      lamTi = makeTypeInfo { rType = TArrow (rType (getTypeInfo rhs)) bodyTy }
      appTi = makeTypeInfo { rType = bodyTy, tags = tags (getTypeInfo body), srcPos = srcPos letTi }
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
