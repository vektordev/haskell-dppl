-- | Semantics-preserving source rewrites over parsed programs: the rewrite
-- families of the invariance net (task
-- rewrite-invariance-net-draw-apply-helper-alias, milestone M0 of design
-- law-carrying-modality, M2 of transformation-differential-testing).
--
-- Every rewrite here must denote the same distribution as its input, and the
-- argument for that is written next to each one. A rewrite that changed the
-- semantics would turn every downstream divergence into a false alarm, so
-- each precondition is deliberately narrower than it could be.
--
-- The four families:
--
-- * 'DrawIntro': @C[e]@ becomes @draw z = e in C[z]@, where @C@ is the one
--   node directly above @e@ and evaluates @e@ exactly once, unconditionally.
--   The task spells this family as "@draw x = e in b@ ⇄ @(\\x -> b) e@". Those
--   two spellings parse to the *same* AST (@SPLL.Prelude.letIn@ is 'Apply' of a
--   'Lambda'; see 'drawAndLiteralApplicationCoincide' in "TestRewrites"), so at
--   the 'Expr' level that rewrite is the identity and would test nothing. What
--   the family needs in order to produce the design's probe rows 7, 9 and 10 is
--   the introduction of the binding itself, which is this rewrite.
-- * 'LinearInline': @draw x = e in b@ becomes @b[x := e]@, when @x@ occurs
--   exactly once in @b@ and not under a function body ('linearOccurrence').
--   The inverse of 'DrawIntro'.
-- * 'HelperExtract': a subterm @t@ with free local variables @v̄@ becomes a
--   call @h v̄@ of a new top-level @h v̄ = t@. Call-by-value is @draw@
--   semantics, so this is always sound.
-- * 'AliasIntro': a binder's body @b@ becomes @draw y = x in b[x := y]@.
--
-- Milestone M3 of transformation-differential-testing (task
-- transformation-differential-testing-m3-catalog-expansion) adds the rest of
-- that design's starter catalog:
--
-- * 'IfFlip': @if c then a else b@ becomes @if not c then b else a@.
-- * 'CompareFlip': @a < b@ becomes @b > a@ (and @a > b@ becomes @b < a@);
--   where both operands are a variable or a constant, @a < b@ also becomes
--   @not (b < a || b == a)@, which is @not (b <= a)@ spelled in the
--   language's operators (it has no @<=@).
-- * 'InjFIdentity': a Float- or Int-valued subterm @e@ becomes @e + 0@,
--   @1 * e@ or @0 - (0 - e)@, and a @+@/@*@ call's operands are swapped.
-- * 'AlphaRename': a binder is renamed, either to a fresh name or to the
--   name of a binder of another declaration, which its body does not mention.
-- * 'TupleLaw': @fst (a, b)@ becomes @a@ (and @snd (a, b)@ becomes @b@) when
--   @b@ makes no call, and a first-order value @e@ becomes @fst (e, 0.0)@.
--
-- The catalog's fifth M3 entry, @of@-clause toggling, rewrites a neural
-- declaration rather than an expression, so it is not a 'Family':
-- 'ofToggles'.
module Rewrites
  ( Family(..)
  , allFamilies
  , familyName
  , Variant(..)
  , variants
  , linearOccurrence
  , linearInline
  , aliasIntro
  , drawIntroAt
  , extractHelper
  , freshName
  , programNames
  , commutativeInjFs
  , commuteSites
  , ofToggles
  ) where

import Data.Foldable (toList)
import Data.List (delete, isPrefixOf, nub)
import qualified Data.Map as Map
import qualified Data.Set as Set

import SPLL.Lang.Types
import SPLL.Lang.Lang (freeVarsExpr, substituteVar, renameFreeVar, getSubExprs, setSubExprs, resolveNeuralAnnotation, neuralValueType)
import SPLL.Typing.RType (RType(..))
import SPLL.Typing.RInfer (tryAddRTypeInfo)
import SPLL.ReservedNames (destructBinderPrefix, observeBinderPrefix, etaBinderPrefix)

data Family = DrawIntro | LinearInline | HelperExtract | AliasIntro
            | IfFlip | CompareFlip | InjFIdentity | AlphaRename | TupleLaw
  deriving (Show, Eq, Ord, Enum, Bounded)

allFamilies :: [Family]
allFamilies = [minBound .. maxBound]

familyName :: Family -> String
familyName DrawIntro = "draw-intro"
familyName LinearInline = "linear-inline"
familyName HelperExtract = "helper-extract"
familyName AliasIntro = "alias-intro"
familyName IfFlip = "if-flip"
familyName CompareFlip = "compare-flip"
familyName InjFIdentity = "injf-identity"
familyName AlphaRename = "alpha-rename"
familyName TupleLaw = "tuple-law"

-- | One rewritten program, with a label naming the site so a divergence can
-- be read back to the subterm that caused it.
data Variant = Variant
  { variantFamily :: Family
  , variantSite :: String
  , variantProgram :: Program
  }

-- | What a site knows about where it sits: the local binders in scope,
-- outermost first, whether the node is the callee of an 'Apply', and the
-- node's twin in the RType-annotated program, where inference typed the
-- program and the twin has the node's shape ('typedTwin').
data Ctx = Ctx { ctxScope :: [String], ctxCallee :: Bool, ctxTyped :: Maybe Expr, ctxDecl :: String }

-- | The 'RType' inference gave a node, if the program typed.
ctxRType :: Ctx -> Maybe RType
ctxRType = fmap (rType . ann) . ctxTyped

-- | Every name the program mentions, which a fresh name must avoid.
programNames :: Program -> Set.Set String
programNames p = Set.unions
  (Set.fromList (map fst (functions p)) : Set.fromList [n | (n, _, _) <- neurals p]
   : map (allNamesExpr . snd) (functions p))

-- | Every name an expression mentions, free or bound.
allNamesExpr :: Expr -> Set.Set String
allNamesExpr (Expr _ (Var v)) = Set.singleton v
allNamesExpr (Expr _ (Lambda x b)) = Set.insert x (allNamesExpr b)
allNamesExpr (Expr _ f) = foldr (Set.union . allNamesExpr) Set.empty f

-- | The first @prefix<k>@ not in the avoid set.
freshName :: String -> Set.Set String -> String
freshName prefix avoid = head [n | k <- [0 :: Int ..], let n = prefix ++ show k, not (n `Set.member` avoid)]

-- | Every single-site application of a family, in traversal order.
variants :: Family -> Program -> [Variant]
variants fam p =
  [ Variant fam (declName ++ ": " ++ siteLbl) (p { functions = replaceDecl declName e' (functions p) ++ extra })
  | (declName, body) <- functions p
  , (siteLbl, e', extra) <- everySite (site fam) (Ctx [] False (typedTwin body =<< lookup declName typedDecls) declName) body ]
  where
    avoid = programNames p
    var' = freshName "rwv" avoid
    helper = freshName "rwh" avoid
    renamed = freshName "rwa" avoid
    -- The validator refuses a name bound twice in one declaration, even in
    -- sibling scopes, so a reused name comes from another declaration.
    bindersElsewhere d = nub [ x | (n, b) <- functions p, n /= d, x <- lambdaBinders b ]
    arity = [(n, lambdaArity b) | (n, b) <- functions p]
    -- Only the type-directed families read it, so a program inference
    -- refuses costs the others nothing.
    typedDecls = either (const []) functions (tryAddRTypeInfo p)
    replaceDecl n e ds = [(m, if m == n then e else b) | (m, b) <- ds]
    site DrawIntro ctx e
      | ctxCallee ctx = []
      | otherwise = [ (lbl "draw-intro" c, e', []) | (c, e') <- drawIntroSites ctx var' arity e ]
    site LinearInline _ e = [ (lbl "inline" e, e', []) | Just e' <- [linearInline e] ]
    site HelperExtract ctx e
      | ctxCallee ctx || not (extractable e) = []
      | otherwise = let (call, decl) = extractHelper (ctxScope ctx) helper e
                    in [(lbl "extract" e, call, [(helper, decl)])]
    site AliasIntro _ e = [ (lbl "alias" e, e', []) | Just e' <- [aliasIntro var' e] ]
    site IfFlip _ e = [ (lbl "if-flip" e, e', []) | Just e' <- [ifFlip e] ]
    site CompareFlip ctx e = [ (lbl what e, e', []) | (what, e') <- compareFlips (ctxScope ctx) e ]
    site InjFIdentity ctx e
      | ctxCallee ctx = []
      | otherwise = [ (lbl what e, e', []) | (what, e') <- injFIdentities (ctxRType ctx) e ]
    site AlphaRename ctx e = [ (lbl what e, e', []) | (what, e') <- alphaRenames (bindersElsewhere (ctxDecl ctx)) (ctxScope ctx) renamed e ]
    site TupleLaw ctx e
      | ctxCallee ctx = []
      | otherwise = [ (what, e', []) | (what, e') <- tupleLaws ctx arity e ]
    lbl what e = what ++ " " ++ renderShort e

-- | Apply a site function once at every node, rebuilding the path above it.
everySite :: (Ctx -> Expr -> [(String, Expr, [FnDecl])]) -> Ctx -> Expr -> [(String, Expr, [FnDecl])]
everySite f ctx e = f ctx e ++
  [ (lbl, setSubExprs e (replaceAt i c' cs), extra)
  | (i, c) <- zip [0 ..] cs
  , (lbl, c', extra) <- everySite f (childCtx i c) c ]
  where
    cs = getSubExprs e
    twinChild i c = ctxTyped ctx >>= \t -> let tcs = getSubExprs t
                                           in if i < length tcs then typedTwin c (tcs !! i) else Nothing
    childCtx :: Int -> Expr -> Ctx
    childCtx i c = case node e of
      Lambda x _ -> ctx { ctxScope = ctxScope ctx ++ [x], ctxCallee = False, ctxTyped = twinChild i c }
      Apply _ _ | i == 0 -> ctx { ctxCallee = True, ctxTyped = twinChild i c }
      _ -> ctx { ctxCallee = False, ctxTyped = twinChild i c }

-- | @typedTwin e t@: @t@, the node inference annotated, if it has @e@'s shape
-- at the root (the same constructor, variable, function name and arity).
-- Inference does not rebuild the tree, but a monomorphized retry clones
-- declarations; a mismatch drops the types below that point, so a
-- type-directed rewrite only ever reads the type of the node it rewrites.
typedTwin :: Expr -> Expr -> Maybe Expr
typedTwin e t
  | sameShape (node e) (node t) = Just t
  | otherwise = Nothing
  where
    sameShape (Var a) (Var b) = a == b
    sameShape (InjF a xs) (InjF b ys) = a == b && length xs == length ys
    sameShape (Lambda a _) (Lambda b _) = a == b
    sameShape (Constant a) (Constant b) = a == b
    sameShape (ReadNN a _) (ReadNN b _) = a == b
    sameShape (ThetaI _ i) (ThetaI _ j) = i == j
    sameShape (Subtree _ i) (Subtree _ j) = i == j
    sameShape IfThenElse{} IfThenElse{} = True
    sameShape Apply{} Apply{} = True
    sameShape _ _ = False

-- | The binary built-in functions whose operands commute: @f a b@ and
-- @f b a@ denote the same value for every @a@, @b@, so swapping the operands
-- of one call is semantics-preserving whatever they are -- random, shared
-- with other subterms, or recursive (both operands are evaluated either way,
-- and an independent draw does not care which is evaluated first).
commutativeInjFs :: [String]
commutativeInjFs = ["plus", "plusI", "mult", "multI", "and", "or", "max", "eq"]

-- | Every program obtained from @p@ by swapping the operands of exactly one
-- call of a 'commutativeInjFs' function, labelled by its site. A call whose
-- two operands are the same expression has no site (the swap is the
-- identity). Not a 'Family': the rewrite-invariance sweep compares at the
-- default config, while operand order is the axis topK pruning is known to
-- depend on (task transformation-differential-testing-m1-config-differencing,
-- "Corpus.TopKOperandOrder").
commuteSites :: Program -> [(String, Program)]
commuteSites p =
  [ (declName ++ ": " ++ lbl, p { functions = [ (m, if m == declName then e' else b) | (m, b) <- functions p ] })
  | (declName, body) <- functions p
  , (lbl, e', _) <- everySite site (Ctx [] False Nothing declName) body ]
  where
    site _ e = case node e of
      InjF (Named f) [a, b] | f `elem` commutativeInjFs, a /= b ->
        [("commute " ++ render e, e { node = InjF (Named f) [b, a] }, [])]
      _ -> []

-- | 'render', cut to a label's length.
renderShort :: Expr -> String
renderShort e = let s = render e in if length s > 80 then take 80 s ++ "..." else s

-- | An unannotated node, as the parser would build it.
mkExpr :: ExprF Expr -> Expr
mkExpr = Expr makeTypeInfo

-- | A compact, source-like rendering for site labels. Not a round-trippable
-- printer: labels only have to let a reader find the subterm.
render :: Expr -> String
render e = case node e of
  Var v -> v
  Constant c -> showConst c
  Lambda x b -> "(\\" ++ x ++ " -> " ++ render b ++ ")"
  Apply (Expr _ (Lambda x b)) v -> "(draw " ++ x ++ " = " ++ render v ++ " in " ++ render b ++ ")"
  Apply f a -> "(" ++ render f ++ " " ++ render a ++ ")"
  IfThenElse c t f -> "(if " ++ render c ++ " then " ++ render t ++ " else " ++ render f ++ ")"
  InjF (Named n) args -> "(" ++ unwords (n : map render args) ++ ")"
  ThetaI a i -> "(theta " ++ render a ++ " " ++ show i ++ ")"
  Subtree a i -> "(subtree " ++ render a ++ " " ++ show i ++ ")"
  ReadNN n a -> "(" ++ n ++ " " ++ render a ++ ")"
  where
    showConst (VFloat d) = show d
    showConst (VInt i) = show i
    showConst (VBool b) = show b
    showConst c = show c

replaceAt :: Int -> a -> [a] -> [a]
replaceAt i x xs = take i xs ++ [x] ++ drop (i + 1) xs

lambdaArity :: Expr -> Int
lambdaArity (Expr _ (Lambda _ b)) = 1 + lambdaArity b
lambdaArity _ = 0

-- ---------------------------------------------------------------------------
-- Draw introduction
-- ---------------------------------------------------------------------------

-- | The draw introductions at node @p@: one per child position @p@ evaluates
-- exactly once and unconditionally, each binding that child to @z@ around
-- @p@. Returns (the child, the rewritten node).
--
-- The strict positions: every operand of an 'InjF', an @if@'s condition (never
-- an arm: hoisting a recursive call out of an arm can make the program
-- diverge), every argument of an application spine whose head is not a lambda,
-- the bound value of a @draw@, and the argument of 'ReadNN', 'ThetaI',
-- 'Subtree'. A lambda body is never one, since the lambda may run many times.
--
-- The child must be a value the new binding can hold without changing what
-- it means: not a lambda, not a local variable (that is 'AliasIntro'), and
-- not the name of a top-level function taking arguments.
drawIntroSites :: Ctx -> String -> [(String, Int)] -> Expr -> [(Expr, Expr)]
drawIntroSites ctx z arity p =
  [ (c, e') | i <- strictPositions p, let c = getSubExprs p !! i, eligible c
            , Just e' <- [drawIntroAt z i p] ]
  where
    eligible (Expr _ (Lambda _ _)) = False
    eligible (Expr _ (Var v)) = v `notElem` ctxScope ctx && maybe True (== 0) (lookup v arity)
    eligible _ = True

strictPositions :: Expr -> [Int]
strictPositions p = case node p of
  InjF _ args -> [0 .. length args - 1]
  IfThenElse {} -> [0]
  Apply _ _ -> [1]
  ReadNN _ _ -> [0]
  ThetaI _ _ -> [0]
  Subtree _ _ -> [0]
  _ -> []

-- | @drawIntroAt z i p@: bind the @i@-th child of @p@ to @z@ around @p@.
-- For an application spine the argument positions are those of the
-- outermost 'Apply' only; the callee side is its own spine and is reached by
-- the traversal only in callee position, where 'DrawIntro' does nothing.
drawIntroAt :: String -> Int -> Expr -> Maybe Expr
drawIntroAt z i p
  | i `notElem` strictPositions p = Nothing
  | otherwise =
      let c = getSubExprs p !! i
          p' = setSubExprs p (replaceAt i (mkExpr (Var z)) (getSubExprs p))
      in Just (mkExpr (Apply (mkExpr (Lambda z p')) c))

-- ---------------------------------------------------------------------------
-- Linear inlining
-- ---------------------------------------------------------------------------

-- | Does @x@ occur free in @b@ exactly once, and not inside the body of a
-- lambda that is not itself immediately applied? That is the linearity
-- precondition: a use under a function body may run many times, and
-- substituting a random @e@ there would give each run its own draw where the
-- binding shared one. A use inside a @draw@ body or value runs once. A use in
-- one arm of an @if@ runs at most once, which is fine: an independent draw
-- that is never read has no effect on the distribution.
linearOccurrence :: String -> Expr -> Bool
linearOccurrence x b = occurrences False b == [False]
  where
    -- One entry per free occurrence: is it under a non-redex lambda?
    occurrences under (Expr _ (Var v)) = [under | v == x]
    occurrences _ (Expr _ (Lambda y body))
      | y == x = []
      | otherwise = occurrences True body
    occurrences under (Expr _ (Apply (Expr _ (Lambda y body)) arg)) =
      (if y == x then [] else occurrences under body) ++ occurrences under arg
    occurrences under e = concatMap (occurrences under) (getSubExprs e)

-- | @draw x = e in b@ to @b[x := e]@, where 'linearOccurrence' holds.
linearInline :: Expr -> Maybe Expr
linearInline (Expr _ (Apply (Expr _ (Lambda x b)) e))
  | linearOccurrence x b = Just (substituteVar x e b)
linearInline _ = Nothing

-- ---------------------------------------------------------------------------
-- Helper extraction
-- ---------------------------------------------------------------------------

-- | Worth extracting: anything that computes. A bare variable or constant
-- would only add a call, and a lambda would make the helper return a function.
extractable :: Expr -> Bool
extractable e = case node e of
  Var _ -> False
  Constant _ -> False
  Lambda _ _ -> False
  _ -> True

-- | @extractHelper scope h t@: the call @h v̄@ replacing @t@, and the helper's
-- body @\\v̄ -> t@, where @v̄@ are the local binders of @scope@ that occur free
-- in @t@, outermost first. A binder shadowed in @scope@ appears once, and the
-- innermost binding is the one @t@ sees, both at the call site and (as the
-- helper's parameter) inside the helper. No capture is possible: the
-- helper's only binders are @v̄@, and @t@'s other free names are top-level.
extractHelper :: [String] -> String -> Expr -> (Expr, Expr)
extractHelper scope h t = (call, decl)
  where
    fv = freeVarsExpr t
    params = nub [v | v <- scope, v `Set.member` fv]
    call = foldl (\f v -> mkExpr (Apply f (mkExpr (Var v)))) (mkExpr (Var h)) params
    decl = foldr (\v b -> mkExpr (Lambda v b)) t params

-- ---------------------------------------------------------------------------
-- Alias introduction
-- ---------------------------------------------------------------------------

-- | At a binder @\\x -> b@ (a parameter or a @draw@) with @x@ free in @b@:
-- @\\x -> draw y = x in b[x := y]@. @y@ is fresh for the whole program, so
-- nothing in @b@ can capture it.
aliasIntro :: String -> Expr -> Maybe Expr
aliasIntro y (Expr t (Lambda x b))
  | x `Set.member` freeVarsExpr b =
      Just (Expr t (Lambda x (mkExpr (Apply (mkExpr (Lambda y (substituteVar x (mkExpr (Var y)) b))) (mkExpr (Var x))))))
aliasIntro _ _ = Nothing

-- ---------------------------------------------------------------------------
-- If-flips and comparison rewrites
-- ---------------------------------------------------------------------------

-- | @if c then a else b@ to @if not c then b else a@. @not@ is total on
-- Bool, and each arm still runs exactly when it did.
ifFlip :: Expr -> Maybe Expr
ifFlip (Expr t (IfThenElse c a b)) = Just (Expr t (IfThenElse (injF' "not" [c]) b a))
ifFlip _ = Nothing

-- | The comparison rewrites at one node. @a < b@ and @b > a@ are the same
-- relation, so the operand swap is always sound. The negated spelling
-- @not (b < a || b == a)@ reads each operand twice, so it applies only where
-- a second read is the same value: a local variable (a binding is one value,
-- however often it is read) or a constant. Not a top-level name: a nullary
-- definition is re-run at every read (@coin ++ coin@ sums two coins).
compareFlips :: [String] -> Expr -> [(String, Expr)]
compareFlips scope (Expr t (InjF (Named f) [a, b]))
  | f == "lt" = swapped "gt" ++ negated a b
  | f == "gt" = swapped "lt" ++ negated b a
  where
    swapped g = [("compare-swap", Expr t (InjF (Named g) [b, a]))]
    -- lo < hi as not (hi < lo || hi == lo)
    negated lo hi
      | duplicable lo && duplicable hi =
          [("compare-negate", Expr t (InjF (Named "not")
              [injF' "or" [injF' "lt" [hi, lo], injF' "eq" [hi, lo]]]))]
      | otherwise = []
    duplicable (Expr _ (Var v)) = v `elem` scope
    duplicable (Expr _ (Constant _)) = True
    duplicable _ = False
compareFlips _ _ = []

-- ---------------------------------------------------------------------------
-- InjF identities
-- ---------------------------------------------------------------------------

-- | The arithmetic identities at a node inference typed @Float@ or @Int@:
-- @e + 0@, @1 * e@ and @0 - (0 - e)@ (exact in IEEE arithmetic as in the
-- integers, and each evaluates @e@ once), plus swapping the operands of a
-- @+@/@*@ call ('commutativeInjFs' minus the Boolean and comparison ones,
-- which the task does not name). A constant is not rewritten: the optimizer
-- folds it straight back.
injFIdentities :: Maybe RType -> Expr -> [(String, Expr)]
injFIdentities ty e = case node e of
  Constant _ -> commuted
  Lambda _ _ -> []
  _ -> identities ++ commuted
  where
    identities = case ty of
      Just TFloat -> wrap "plus" "neg" (VFloat 0) (VFloat 1) "mult"
      Just TInt -> wrap "plusI" "negI" (VInt 0) (VInt 1) "multI"
      _ -> []
    wrap plus neg zero one mult =
      [ ("plus-zero", injF' plus [e, c zero])
      , ("one-times", injF' mult [c one, e])
      , ("double-negate", injF' plus [c zero, injF' neg [injF' plus [c zero, injF' neg [e]]]]) ]
    c = mkExpr . Constant
    commuted = case node e of
      InjF (Named f) [a, b] | f `elem` ["plus", "plusI", "mult", "multI"], a /= b ->
        [("commute", e { node = InjF (Named f) [b, a] })]
      _ -> []

injF' :: String -> [Expr] -> Expr
injF' f = mkExpr . InjF (Named f)

-- ---------------------------------------------------------------------------
-- Alpha renaming
-- ---------------------------------------------------------------------------

-- | At a binder @\\x -> b@ with @x@ free in @b@: @\\y -> b[x := y]@, for
-- @y@ a name fresh for the program, and for @y@ the first binder name of
-- another declaration (@binders@, in program order) that is not in scope here
-- and that @b@ neither reads nor binds. The second is the capture check: it
-- gives a caller's and a callee's variables one name, which is how helper
-- extraction found the @enumerateAppliedLambda@ capture. A name from the same
-- declaration is not an option: the validator refuses a name bound twice in
-- one declaration, shadowing or not. Desugaring
-- binders (patterns, @observe@, eta expansion) keep their names: their prefix
-- is part of what the parser emitted, and renaming one tests the
-- reserved-name scheme, not the compiler.
alphaRenames :: [String] -> [String] -> String -> Expr -> [(String, Expr)]
alphaRenames binders scope fresh (Expr t (Lambda x b))
  | x `Set.member` freeVarsExpr b, not (desugared x) =
      [ ("alpha-fresh", rename fresh) ] ++
      [ ("alpha-reuse " ++ y, rename y) | y <- take 1 reusable ]
  where
    names = allNamesInExpr b
    rename y = Expr t (Lambda y (renameFreeVar x y b))
    reusable = [ y | y <- binders, y /= x, y `notElem` scope, not (desugared y), not (y `Set.member` names) ]
    desugared n = any (`isPrefixOf` n) [destructBinderPrefix, observeBinderPrefix, etaBinderPrefix]
alphaRenames _ _ _ _ = []

-- | Every binder of an expression, in traversal order.
lambdaBinders :: Expr -> [String]
lambdaBinders (Expr _ (Lambda x b)) = x : lambdaBinders b
lambdaBinders (Expr _ f) = concatMap lambdaBinders (toList f)

-- | Every name an expression mentions, free or bound ('allNamesExpr' of
-- "SPLL.Lang.Lang", which it does not export).
allNamesInExpr :: Expr -> Set.Set String
allNamesInExpr (Expr _ (Var v)) = Set.singleton v
allNamesInExpr (Expr _ (Lambda x b)) = Set.insert x (allNamesInExpr b)
allNamesInExpr (Expr _ f) = foldr (Set.union . allNamesInExpr) Set.empty f

-- ---------------------------------------------------------------------------
-- Tuple laws
-- ---------------------------------------------------------------------------

-- | The tuple laws at one node. Projection of a pair: @fst (a, b)@ is @a@,
-- and dropping the unread @b@ is sound because the language has no effects;
-- the one way @b@ could still matter is by failing to terminate or raising,
-- so @b@ must make no call (no 'Apply', no network read). Pairing: at each
-- position the node evaluates once ('strictPositions'), a first-order child
-- @e@ becomes @fst (e, 0.0)@. A higher-order built-in's operands are left
-- alone (they may be functions), as is a child inference typed as a function.
tupleLaws :: Ctx -> [(String, Int)] -> Expr -> [(String, Expr)]
tupleLaws ctx arity p = projections ++ pairings
  where
    projections = case node p of
      InjF (Named "fst") [Expr _ (InjF (Named "TCons") [a, b])] | callFree b -> [("fst-pair " ++ renderShort p, a)]
      InjF (Named "snd") [Expr _ (InjF (Named "TCons") [a, b])] | callFree a -> [("snd-pair " ++ renderShort p, b)]
      _ -> []
    pairings = case node p of
      InjF (Named f) _ | f `elem` higherOrderInjFs -> []
      _ -> [ ("pair-fst " ++ renderShort c, setSubExprs p (replaceAt i (injF' "fst" [injF' "TCons" [c, mkExpr (Constant (VFloat 0))]]) cs))
           | i <- strictPositions p, let c = cs !! i, firstOrder i c ]
    cs = getSubExprs p
    twins = maybe [] getSubExprs (ctxTyped ctx)
    firstOrder i c = case node c of
      Lambda _ _ -> False
      Constant _ -> False
      Var v | Just n <- lookup v arity, n > 0 -> False
      _ -> case (if i < length twins then Just (rType (ann (twins !! i))) else Nothing) of
             Just (TArrow _ _) -> False
             _ -> True
    callFree e = case node e of
      Apply _ _ -> False
      ReadNN _ _ -> False
      _ -> all callFree (getSubExprs e)

-- | The built-ins whose operands may be functions.
higherOrderInjFs :: [String]
higherOrderInjFs = ["apply", "map", "mapLeft", "mapEither"]

-- ---------------------------------------------------------------------------
-- of-clause toggling
-- ---------------------------------------------------------------------------

-- | Every program obtained from @p@ by toggling one neural declaration's @of@
-- clause: a written clause is removed (with the registry entry the parser
-- made of it), and a declaration with none gets the clause its annotation
-- resolves to written out. Only where the toggled declaration round-trips --
-- it resolves to the same 'MultiValue' afterwards ('resolveNeuralAnnotation')
-- -- and so does every other declaration: then the two programs denote the
-- same networks with the same output annotation, so the compiler owes them
-- the same module. (A written clause that pins a value set narrower than its
-- type's auto-derivation does not round-trip and has no toggle.)
ofToggles :: Program -> [(String, Program)]
ofToggles p =
  [ (name ++ (if hasClause then ": of removed" else ": of written"), p')
  | (i, decl@(name, ty, tag)) <- zip [0 :: Int ..] (neurals p)
  , name /= "writeLogits"
  , Right mv <- [resolveNeuralAnnotation (adts p) (writeLogitsDecls p) decl]
  , let hasClause = tag /= Nothing
        sugar = case (tag, neuralValueType ty) of
          (Just m, Just target) -> [(target, m)]
          _ -> []
        p' = p { neurals = replaceAt i (name, ty, if hasClause then Nothing else Just mv) (neurals p)
               , writeLogitsDecls = if hasClause then foldr delete (writeLogitsDecls p) sugar
                                    else [ (target, mv) | Just target <- [neuralValueType ty] ] ++ writeLogitsDecls p }
  , resolvedAll p' == resolvedAll p ]
  where
    resolvedAll q = Map.fromList [ (n, resolveNeuralAnnotation (adts q) (writeLogitsDecls q) d) | d@(n, _, _) <- neurals q ]
