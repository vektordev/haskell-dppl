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
  ) where

import Data.List (nub)
import qualified Data.Set as Set

import SPLL.Lang.Types
import SPLL.Lang.Lang (freeVarsExpr, substituteVar, getSubExprs, setSubExprs)

data Family = DrawIntro | LinearInline | HelperExtract | AliasIntro
  deriving (Show, Eq, Ord, Enum, Bounded)

allFamilies :: [Family]
allFamilies = [minBound .. maxBound]

familyName :: Family -> String
familyName DrawIntro = "draw-intro"
familyName LinearInline = "linear-inline"
familyName HelperExtract = "helper-extract"
familyName AliasIntro = "alias-intro"

-- | One rewritten program, with a label naming the site so a divergence can
-- be read back to the subterm that caused it.
data Variant = Variant
  { variantFamily :: Family
  , variantSite :: String
  , variantProgram :: Program
  }

-- | What a site knows about where it sits: the local binders in scope,
-- outermost first, and whether the node is the callee of an 'Apply'.
data Ctx = Ctx { ctxScope :: [String], ctxCallee :: Bool }

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
  , (siteLbl, e', extra) <- everySite (site fam) (Ctx [] False) body ]
  where
    avoid = programNames p
    var' = freshName "rwv" avoid
    helper = freshName "rwh" avoid
    arity = [(n, lambdaArity b) | (n, b) <- functions p]
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
    lbl what e = what ++ " " ++ truncateTo 80 (render e)
    truncateTo n s = if length s > n then take n s ++ "..." else s

-- | Apply a site function once at every node, rebuilding the path above it.
everySite :: (Ctx -> Expr -> [(String, Expr, [FnDecl])]) -> Ctx -> Expr -> [(String, Expr, [FnDecl])]
everySite f ctx e = f ctx e ++
  [ (lbl, setSubExprs e (replaceAt i c' cs), extra)
  | (i, c) <- zip [0 ..] cs
  , (lbl, c', extra) <- everySite f (childCtx i) c ]
  where
    cs = getSubExprs e
    childCtx :: Int -> Ctx
    childCtx i = case node e of
      Lambda x _ -> Ctx (ctxScope ctx ++ [x]) False
      Apply _ _ | i == 0 -> ctx { ctxCallee = True }
      _ -> ctx { ctxCallee = False }

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
