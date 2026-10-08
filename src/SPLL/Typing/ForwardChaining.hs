{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module SPLL.Typing.ForwardChaining
  ( FCData(..)
  , ExprInfo(..)
  , annotateProg
  , progToFCData
  , InvChain(..)
  , toInvExpr
  , toInvExprMaybe
  , toSeededInvExpr
  , toSeededMonotoneInvExpr
  , Monotonicity(..)
  , Image(..)
  , fullImage
  , injFImage
  , clampToImage
  , imageGuards
  , isInvertibleLambda
  , isWitnessedLambda
  , findEquivalentExpression
  , findExprWithCN
  , unwrapLambdas
  , untag
  , getTag
  , showClause
  , showClauseGroup
  , showClauseGroups
  ) where
import SPLL.Lang.Types
import SPLL.IntermediateRepresentation
import Data.Functor ((<&>))
import SPLL.Lang.Lang
import PredefinedFunctions
import Data.List (nub, intercalate)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import SPLL.Typing.Typing (setChainName)
import Data.Foldable
import Data.Char (isUpper)
import Utils
import SPLL.Typing.RType



data FCData = FCData
  { hornClauses :: [[HornClause]]
  , chainNameInfo :: [(ChainName, ExprInfo)]
  -- | The determinism field's known-anchor set seeded into 'hornClauses'. Kept
  -- around so codegen (IRCompiler) can materialise the value of any non-constant
  -- anchor a forward-chaining inverse path lands on.
  , fcAnchors :: Set ChainName
  -- | For every Lambda node (keyed by its chain name): the occurrences of ITS
  -- bound variable inside its own body, shadowing-aware. Occurrence lookup must
  -- be scoped like this: a global by-name search would pick up same-named
  -- variables bound by unrelated lambdas elsewhere in the program, and anchor
  -- seeding can make those foreign occurrences solvable, yielding an inverse
  -- built from another function's material.
  , lambdaVarOccurrences :: [(ChainName, [ChainName])]
  }

-- Information on what type of expression a HornClause originated from
data ExprInfo = StubInfo ExprStub   -- Generic Expression without additional Info
              | InjFInfo String     -- InjF with the name of the InjF
              | LambdaInfo String ChainName  -- Lambda with the name of the bound variable and the ChainName of the body
              | IfInfo ChainName ChainName ChainName
              | ConstantInfo Value  -- Contant with the value
              | VarInfo String
              | ApplyInfo ChainName ChainName -- Chain name of the left parameter of the Apply
              | AppliedInfo         -- Does not directly correlate to an expression. Via application a value is assigned to a bound variable
              deriving (Eq, Show)

data EquivalenceType = VariableEquivalence String
                     | AppliedEquivalence
                     deriving (Eq, Show)

-- Horn clauses state: When all premises are known, we can derive the conclusion. Expression info holds information about the original expression.
-- inversion represents which direction the HornClause represents. E.g.
-- Original: a = b + c
-- Inversion 0: b, c -> a
-- Inversion 1: a, c -> b
-- Inversion 2: a, b -> c
-- Parameter HornClauses define a ChainName to be known. This could represent the sample passed to the top-level expression, or the parameter passed to an inverse expression
data HornClause = ExprHornClause {premises' :: [ChainName], conclusion :: ChainName, exprInfo :: ExprInfo, inversion :: Int}
                | EquivalenceHornClause {premises' :: [ChainName], conclusion :: ChainName, equivalenceType :: EquivalenceType, inversion :: Int}
                | ParameterHornClause {conclusion :: ChainName} deriving (Eq, Show)

-- Wraps the premises field, because ParameterHornClauses have an empty set of premises by definition
premises :: HornClause -> [ChainName]
premises ParameterHornClause {} = []
premises ExprHornClause {premises'=p} = p
premises EquivalenceHornClause {premises'=p} = p

-- | An expression the chaining reached by following equivalences to a lambda.
-- Which expressions those are is decided by the clause set, so a non-lambda
-- here means the clauses and the AST disagree.
asLambda :: String -> Expr -> (String, Expr)
asLambda _ (Expr _ (Lambda n bodyExpr)) = (n, bodyExpr)
asLambda ctx e = error (ctx ++ ": expected chain name " ++ getChainName e ++ " to be a Lambda")

getChainName :: Expr -> ChainName
getChainName = chainName . getTypeInfo


isEquivalenceHornClause :: HornClause -> Bool
isEquivalenceHornClause (EquivalenceHornClause {}) = True
isEquivalenceHornClause _ = False

isExprHornClause :: HornClause -> Bool
isExprHornClause (ExprHornClause {}) = True
isExprHornClause _ = False


-- The forward-chaining setup shared by the invertibility certificate
-- ('isInvertibleLambda') and the inverse codegen ('toInvExpr'), so the two can
-- never disagree about which lambdas invert. For the lambda resolved from a
-- chain name it returns: the bound variable's name, the chain names of every
-- occurrence of that variable inside the body (the points we try to solve for),
-- and the ParameterHornClause declaring the observed body known. 'Nothing' when
-- the chain name does not resolve to a lambda.
inversionSetup :: FCData -> ChainName -> Maybe (String, [ChainName], HornClause)
inversionSetup fcData lambdaCN = do
  (resolvedCN, info, tag) <- findEquivalentExpression fcData lambdaCN
  case info of
    -- If the lambda is applied multiple times, @tag@ uniquely identifies our
    -- application; it suffixes both the occurrences and the observed body.
    LambdaInfo toInvVarName lambdaBodyCN ->
      case fromMaybe [] (lookup resolvedCN (lambdaVarOccurrences fcData)) of
        -- A dead binding (no occurrence of the bound variable) has nothing to
        -- invert through: not an invertible/witnessable lambda.
        []   -> Nothing
        occs ->
          let toInvCNs = map (++ tag) occs
              -- If the function being inverted is itself a function, strip the
              -- additional lambdas; those are re-added by the caller around the
              -- whole inference function (the inverse is only a part of it).
              (unwrappedChainName, _) = unwrapLambdas fcData lambdaBodyCN
              paramClause = ParameterHornClause (unwrappedChainName ++ tag)
          in Just (toInvVarName, toInvCNs, paramClause)
    _ -> Nothing

-- | Invertibility certificate (modality stage 2): is the variable bound by the
-- lambda at this chain name algebraically recoverable from the known anchors and
-- the observed body? The IR realisation that shares the very same 'FCData' is
-- 'toInvExpr', so the certificate and the codegen can never disagree.
-- (Finiteness/preimage of the recovered value is the orthogonal DiscreteValues
-- axis — Fin in the design — not a FC concern.)
--
-- NOTE: the modality engine does not consult this verdict today — the shipped
-- engine's marginalize+Fin lattice reproduces it on the current corpus, so the
-- only consumers are the tests (investigation
-- fc-recovers-capability-marginalize-floors scoped that finding to the corpus).
-- The engine-facing variant that the witnessed-inference feature wires in is
-- 'isWitnessedLambda' (design modality-witnessed-inference, milestone 2).
isInvertibleLambda :: FCData -> [ADTDecl] -> ChainName -> Bool
isInvertibleLambda fcData adtsDecls lambdaCN = case inversionSetup fcData lambdaCN of
  Just (_, toInvCNs, paramClause) ->
    any (isJust . toValueExpr (hornClauses fcData) [paramClause] adtsDecls) toInvCNs
  Nothing -> False

-- | Witnessed-binding query (design modality-witnessed-inference, milestone 1):
-- is the variable bound by the lambda at @lambdaCN@ algebraically recoverable
-- when @obsCN@ — not the lambda's own body — is the observed value?
--
-- This differs from 'isInvertibleLambda' only in the seed of the chaining: the
-- certificate observes the binding's own body, which for a let nested under a
-- non-invertible context over-claims (the body is not actually observed there).
-- Seeding at the declaration's observed result instead makes the verdict honest
-- for the let-chains-feeding-output shape: the observation reaches the let body
-- through Apply/variable equivalences exactly when the surrounding context
-- preserves it. Pass the declaration root's chain name as @obsCN@; wrapping
-- lambdas (a function declaration's parameters) are stripped, mirroring
-- 'inversionSetup', because the observation is the applied function's result.
--
-- The verdict is per-binding: a True here says only that THIS bound variable is
-- recoverable from the observation. Whether the residual fresh latents of the
-- body are also single-witnessable is the modality engine's marginalize floor's
-- concern (milestone 2), not this query's.
isWitnessedLambda :: FCData -> [ADTDecl] -> ChainName -> ChainName -> Bool
isWitnessedLambda fcData adtsDecls obsCN lambdaCN = case inversionSetup fcData lambdaCN of
  Just (_, toInvCNs, _) ->
    let (unwrappedObsCN, _) = unwrapLambdas fcData obsCN
        obsClause = ParameterHornClause unwrappedObsCN
    in any (isJust . toValueExpr (hornClauses fcData) [obsClause] adtsDecls) toInvCNs
  Nothing -> False

-- | One inversion chain, as codegen consumes it. The three IR expressions past
-- 'invValue' are all tests or corrections *about* that value, and every one of
-- them is only meaningful together with it, which is why they travel as a
-- record rather than as separate builders that could drift apart: they are all
-- derived from the same clause path.
data InvChain = InvChain
  { invValue :: IRExpr
    -- ^ The recovered value of the witnessed variable, free in the seed.
  , invCoV :: IRExpr
    -- ^ The derivative of that inverse, for the change of variables.
  , invGuard :: IRExpr
    -- ^ See 'guardChain': False exactly when a step is out of its domain, in
    -- which case 'invValue' must not be evaluated at all.
  , invReadsAny :: IRExpr
    -- ^ See 'readsAnyChain': True exactly when a step would read a marginal
    -- wildcard, in which case 'invValue' must not be evaluated at all either.
  , invCumValue :: IRExpr
    -- ^ The bound a CUMULATIVE query transports to the witnessed variable:
    -- 'invValue' with every exact integer-quotient step rounded in the
    -- direction its bound points ('cumulativeStep'). Identical to 'invValue'
    -- on a chain with no such step.
  , invCumGuard :: IRExpr
    -- ^ 'invGuard' for 'invCumValue': a rounded step is applicable at every
    -- non-zero divisor, not only an exact one.
  }

-- | A chain whose cumulative form is its point form -- a merge of several
-- occurrences (see 'mergeExpr'), which keeps the point inverse it always had.
pointChain :: IRExpr -> IRExpr -> IRExpr -> IRExpr -> InvChain
pointChain v cov g ra = InvChain v cov g ra v g

-- Takes the chainName of a function (May be a lambda, a variable, an Apply ...) and returns the inverse function of that lambda together with the derivative of the inverse
toInvExpr :: FCData -> [ADTDecl] -> ChainName -> InvChain
toInvExpr fcData adtsDecls lambdaCN = merged
  where
    clauseSet = hornClauses fcData
    (toInvVarName, toInvCNs, paramClause) = case inversionSetup fcData lambdaCN of
      Just x  -> x
      Nothing -> error $ "toInvExpr: chain name does not resolve to an invertible lambda: " ++ lambdaCN
    -- Create the expression that calculates each occurrence; merge those that
    -- carry complementary information.
    valueExprs = informative (mapMaybe (toValueExpr clauseSet [paramClause] adtsDecls) toInvCNs)
    merged = mergeExpr toInvVarName lambdaCN toInvCNs valueExprs

-- | 'toInvExpr' with a recoverable outcome: Nothing when no occurrence of the
-- bound variable yields an inversion path (where 'toInvExpr' dies in
-- 'mergeExpr'). The set-valued witness fallback in IRCompiler dispatches on
-- this instead of the hard error.
toInvExprMaybe :: FCData -> [ADTDecl] -> ChainName -> Maybe InvChain
toInvExprMaybe fcData adtsDecls lambdaCN = do
  (toInvVarName, toInvCNs, paramClause) <- inversionSetup fcData lambdaCN
  case informative (mapMaybe (toPointValueExpr (hornClauses fcData) [paramClause] adtsDecls) toInvCNs) of
    []  -> Nothing
    ves -> Just (mergeExpr toInvVarName lambdaCN toInvCNs ves)

-- | The occurrences' chains with those that certainly recover nothing left
-- out, where any other remains. An occurrence reached through a hole another
-- inverse made up (the other slot of @fst@'s @(s, ANY)@, see
-- 'injectedWildcards') recovers the variable as that hole whatever the
-- observation: it carries no information, and merging it would only add its
-- "read a wildcard" verdict to an occurrence that does constrain the
-- variable. Where every occurrence is such, the witness is genuinely the
-- hole, and they stay.
informative :: [InvChain] -> [InvChain]
informative chains = case filter (not . certainHole . invValue) chains of
  [] -> chains
  cs -> cs
  where
    certainHole (IRLetIn _ _ e) = certainHole e
    certainHole e = isHoleConst e

-- | Point-inversion of the chain from an arbitrary observed node (@seedCN@)
-- down to one occurrence of a witnessed variable (@occCN@). The returned
-- expressions have @seedCN@ as their free variable. This is the machinery of
-- 'isWitnessedLambda' exposed for codegen: the set-valued witness fallback
-- inverts if-branches and comparison operands from their own roots rather than
-- from the lambda body.
toSeededInvExpr :: FCData -> [ADTDecl] -> ChainName -> ChainName -> Maybe InvChain
toSeededInvExpr fcData adtsDecls seedCN occCN =
  toValueExpr (hornClauses fcData) [ParameterHornClause seedCN] adtsDecls occCN

-- Performs forward chaining to create an expression, which calculates the value of a specific point in the AST given a set of parameter points in the AST.
-- Also returns the derivative of that expression, and a guard: a Bool IRExpr that
-- is False exactly when some step of the chain is a deconstructing inverse (e.g.
-- fromLeft/fromRight's applicability = isLeft/isRight) applied outside its domain
-- -- see 'guardChain'. Callers must skip evaluating the returned value/deriv
-- entirely when the guard is False (wrap with IRIf guard ... , not just zero the
-- result afterward): the value expression itself crashes on out-of-domain input
-- (observe-partials-umbrella N1b).
toValueExpr :: [[HornClause]] -> [HornClause] -> [ADTDecl] -> ChainName -> Maybe InvChain
toValueExpr = toValueExprWith (const id)

-- | 'toValueExpr' for the lambda-witness point inversion ('toInvExprMaybe'),
-- whose caller measures the recovered value as a point. An '==' step
-- observed False recovers the set "any value but this one" ('VAnyExcept')
-- instead, and every reader of it there -- a density, an enumerated
-- comparison, the body factor's own '==' -- died on it in the interpreter with
-- a type error, while no text backend could render it at all, so
-- 'anyExceptCodegenRefusal' refused the whole module, every other query
-- included (task fuzz-unconsumed-vanyexcept-reaches-codegen, second seed).
-- That arm is a runtime refusal here instead, the same in every engine; the
-- True arm is untouched. The cumulative value keeps the sentinel, which
-- IRCompiler refuses statically (no bound crosses an '=='), and so does a
-- constructor test's: the interpreter answers some of those through it
-- (task point-inversion-vanyexcept-witness-crashes).
toPointValueExpr :: [[HornClause]] -> [HornClause] -> [ADTDecl] -> ChainName -> Maybe InvChain
toPointValueExpr = toValueExprWith refuseEqSet
  where
    refuseEqSet (ExprHornClause _ _ (InjFInfo "eq") inv) | inv > 0 = irMap $ \e -> case e of
      IRConst (VAnyExcept _) -> IRError
        ("cannot compute marginal: an == observed False recovers its operand only as the set"
         ++ " 'any value but one', which this engine cannot measure as a point"
         ++ " (task point-inversion-vanyexcept-witness-crashes)")
      _ -> e
    refuseEqSet _ = id

toValueExprWith :: (HornClause -> IRExpr -> IRExpr) -> [[HornClause]] -> [HornClause] -> [ADTDecl] -> ChainName -> Maybe InvChain
toValueExprWith pointStep clauses paramClauses adtsDecls startCN = do
  relevantSortedClauses <- toValuePath clauses paramClauses startCN
  -- Calculate the symbolic derivative
  let deriv = derivativeOfPath adtsDecls relevantSortedClauses
  let cumStep = cumulativeStep adtsDecls relevantSortedClauses
  -- A wildcard a step of the chain itself introduces is passed on, not read
  -- ('injectedWildcards').
  let wild = injectedWildcards adtsDecls relevantSortedClauses
  let passWild = passInjectedWildcard adtsDecls wild
  let pointWild c = passWild c . pointStep c
  -- Generate code
  Just InvChain
    { invValue    = toLetInBlockWith pointWild clauses adtsDecls relevantSortedClauses
    , invCoV    = wrapInLetInBlockWith pointWild clauses adtsDecls relevantSortedClauses deriv
    , invGuard    = guardChain pointStep wild clauses adtsDecls relevantSortedClauses
    , invReadsAny = if any (computesOnCertainWildcard adtsDecls wild) (neededClauses relevantSortedClauses)
                      then IRConst (VBool True)
                      else readsAnyChain clauses adtsDecls relevantSortedClauses
    , invCumValue = toLetInBlockWith (\c e -> passWild c (maybe e fst (cumStep c))) clauses adtsDecls relevantSortedClauses
    , invCumGuard = guardChainWith cumStep wild clauses adtsDecls relevantSortedClauses
    }

-- | The chain names of a path whose runtime value may BE a wildcard that the
-- chain itself introduced, with whether it certainly is one.
--
-- 'readsAnyChain' tracks the wildcard a marginal query puts into the seed. A
-- step can also make one up: an inverse that only knows part of its result
-- fills the rest with a hole -- @fst@'s inverse answers @(s, ANY)@, a field
-- accessor's the constructor with every other field @ANY@, @isLeft@'s
-- @Left ANY@. A later step that deconstructs the hole back out hands the
-- next one a bare @ANY@: in @fst (0, h == 1.0)@ the observation says nothing
-- about @h == 1.0@, so @=='s@ inverse got @ANY@ as its condition and its
-- @VAnyExcept@ arm survived into the emitted code (task
-- fuzz-unconsumed-vanyexcept-reaches-codegen), and @fst (0, h + 1.0)@ took a
-- density at @ANY@. Both are an unconstrained witness, not an error: a step
-- whose input is a wildcard recovers a wildcard ('passInjectedWildcard'), and
-- the caller's existing wildcard-witness handling (a sink's body factor, a
-- single-use binding's open body, else a refusal) answers it.
--
-- A value that merely HOLDS a hole (@(s, ANY)@) is read safely by a
-- deconstruction, so only a step reading a possibly-bare wildcard is touched.
-- Where the deconstruction provably extracts the hole itself (@snd (s, ANY)@,
-- folded statically by 'foldHoleAccess'), the next step's result is the hole
-- outright, with no runtime test and no trace of the step's own inverse: the
-- @VAnyExcept@ arm of an @==@ handed a certain wildcard is never emitted, at
-- any optimisation level. Chains that introduce no hole are left exactly as
-- they were.
injectedWildcards :: [ADTDecl] -> [HornClause] -> [(ChainName, Bool)]
injectedWildcards adtsDecls = mapMaybe bare . foldl' step []
  where
    bare (n, WildBare certain) = Just (n, certain)
    bare _ = Nothing
    step st c = case c of
      ParameterHornClause _ -> st
      EquivalenceHornClause [p] conc _ _ | Just w <- lookup p st -> (conc, w) : st
      ExprHornClause pre conc info inv ->
        let ins = mapMaybe (`lookup` st) pre
            decl = case info of
              InjFInfo name -> let FPair fwd invs = lookupFPair adtsDecls name
                                   d = if inv == 0 then fwd else invs !! (inv - 1)
                               in Just (foldr (\(old, new) dd -> renameDecl old new dd) d (zip (inputVars d) pre))
              _ -> Nothing
            hole = inv > 0 && maybe False (holdsWildcardConst . body) decl
            holds = [ (p, sh) | p <- pre, Just (WildHolds sh) <- [lookup p st] ]
            out | WildBare True `elem` ins = Just (WildBare True)
                | WildBare False `elem` ins = Just (WildBare False)
                | not (null holds), Just d <- decl, deconstructing d =
                    case foldHoleAccess adtsDecls (substVars holds (body d)) of
                      [Just x] -> classify st x
                      outs | js@(_:_) <- catMaybes outs, all isHoleConst js -> Just (WildBare True)
                           | otherwise -> Just (WildBare False)
                | not (null holds) = Just (WildHolds (maybe (IRVar conc) (substVars holds . body) decl))
                | hole, Just d <- decl = Just (WildHolds (body d))
                | otherwise = Nothing
        in maybe st (\w -> (conc, w) : st) out
      _ -> st
    -- What a deconstruction of a hole-holding value extracted, statically.
    classify st x
      | isHoleConst x = Just (WildBare True)
      | IRVar n <- x = lookup n st
      | unfolded x = Just (WildBare False)
      | holdsWildcardConst x || any (`elem` map fst st) (irVars x) = Just (WildHolds x)
      | otherwise = Nothing
    unfolded x = case x of
      IRDestruct _ _ -> True
      IRApply _ _ -> True
      _ -> False
    irVars x = case x of
      IRVar n -> [n]
      _ -> concatMap irVars (getIRSubExprs x)
    substVars binds = irMap (\e -> case e of IRVar n | Just v <- lookup n binds -> v; _ -> e)
    holdsWildcardConst e = case e of
      IRConst v -> valueHoldsWildcard v
      _ -> any holdsWildcardConst (getIRSubExprs e)
    valueHoldsWildcard v = case v of
      VAny -> True
      VList AnyList -> True
      VList (ListCont x xs) -> valueHoldsWildcard x || valueHoldsWildcard (VList xs)
      VTuple x y -> valueHoldsWildcard x || valueHoldsWildcard y
      VEither (Left x) -> valueHoldsWildcard x
      VEither (Right y) -> valueHoldsWildcard y
      VADT _ fs -> any valueHoldsWildcard fs
      _ -> False

-- | See 'injectedWildcards': a value holding a hole somewhere, with its
-- static shape, or one that may be a bare hole -- certainly so when True.
data WildState = WildHolds IRExpr | WildBare Bool deriving (Eq)

isHoleConst :: IRExpr -> Bool
isHoleConst (IRConst VAny) = True
isHoleConst (IRConst (VList AnyList)) = True
isHoleConst _ = False

-- | Statically fold a deconstruction of a value whose constructor is known
-- (a tuple, cons cell, @Either@ or ADT constructor application, as an
-- injecting inverse builds it) into the extracted component: one outcome per
-- arm of a value an inverse selects by the observation (@isLeft@'s
-- @if b then Left ANY else Right ANY@), Nothing for an arm the deconstruction
-- is not applicable to (its domain guard zeroes that case, so its value is
-- never read). Anything it does not recognise is left as it is.
foldHoleAccess :: [ADTDecl] -> IRExpr -> [Maybe IRExpr]
foldHoleAccess adtsDecls = go
  where
    go e = case e of
      IRDestruct acc x -> concatMap (maybe [Nothing] (destruct acc)) (go x)
      IRApply (IRVar f) x | isField f -> concatMap (maybe [Nothing] (field f)) (go x)
      IRIf _ a b -> go a ++ go b
      _ -> [Just e]
    destruct AcFst (IRConstruct TgTuple [a, _]) = [Just a]
    destruct AcSnd (IRConstruct TgTuple [_, b]) = [Just b]
    destruct AcFst (IRConst (VTuple a _)) = [Just (IRConst a)]
    destruct AcSnd (IRConst (VTuple _ b)) = [Just (IRConst b)]
    destruct AcHead (IRConstruct TgCons [h, _]) = [Just h]
    destruct AcTail (IRConstruct TgCons [_, t]) = [Just t]
    destruct AcFromLeft (IRConst (VEither (Left v))) = [Just (IRConst v)]
    destruct AcFromRight (IRConst (VEither (Right v))) = [Just (IRConst v)]
    destruct AcFromLeft (IRConst (VEither (Right _))) = [Nothing]
    destruct AcFromRight (IRConst (VEither (Left _))) = [Nothing]
    destruct AcFromLeft (IRConstruct TgLeft [v]) = [Just v]
    destruct AcFromRight (IRConstruct TgRight [v]) = [Just v]
    destruct AcFromLeft (IRConstruct TgRight _) = [Nothing]
    destruct AcFromRight (IRConstruct TgLeft _) = [Nothing]
    destruct acc x = [Just (IRDestruct acc x)]
    ctors = [ c | d <- adtsDecls, c <- constructors d ]
    isField f = any (elem f . map fst . snd) ctors
    field f x = case ctorSpine x [] of
      Just (ctor, args)
        | Just fields <- lookup ctor ctors, length args == length fields ->
            case lookup f (zip (map fst fields) [0 ..]) of
              Just i -> [Just (args !! i)]
              Nothing -> [Nothing]
      _ -> [Just (IRApply (IRVar f) x)]
    ctorSpine (IRApply g a) acc = ctorSpine g (a : acc)
    ctorSpine (IRVar c@(h:_)) acc | isUpper h = Just (c, acc)
    ctorSpine _ _ = Nothing

-- | The test that one of a step's inputs is a chain-introduced wildcard
-- ('injectedWildcards'): Nothing for a step that reads none, @Just Nothing@
-- for one that certainly reads one, else the runtime test. A copy (an
-- equivalence) passes the wildcard on by itself and needs no test.
injectedWildcardTest :: [(ChainName, Bool)] -> HornClause -> Maybe (Maybe IRExpr)
injectedWildcardTest wild c = case c of
  ExprHornClause pre _ _ _ -> case [ (p, certain) | p <- pre, Just certain <- [lookup p wild] ] of
    [] -> Nothing
    ps | any snd ps -> Just Nothing
       | otherwise -> Just (Just (foldr1 (IROp OpOr) [IRUnaryOp OpIsAny (IRVar p) | (p, _) <- ps]))
  _ -> Nothing

-- | A step's value with a chain-introduced wildcard input passed on as a
-- wildcard result: the input is unconstrained, so the recovered value is too.
-- The hole is list-shaped where the step's declared result is a list, as
-- 'anyOfType' places it.
passInjectedWildcard :: [ADTDecl] -> [(ChainName, Bool)] -> HornClause -> IRExpr -> IRExpr
passInjectedWildcard adtsDecls wild c e = case injectedWildcardTest wild c of
  Nothing -> e
  Just Nothing -> IRConst hole
  Just (Just t) -> IRIf t (IRConst hole) e
  where
    hole = case c of
      ExprHornClause _ _ (InjFInfo name) inv ->
        let FPair fwd invs = lookupFPair adtsDecls name
            Forall _ _ sig = contract (if inv == 0 then fwd else invs !! (inv - 1))
        in anyOfType (resultType sig)
      _ -> VAny
    resultType (TArrow _ r) = resultType r
    resultType r = r

-- | The clauses of a sorted path the last one's value depends on. A path may
-- hold steps toward other occurrences ('toValuePath' keeps superfluous
-- clauses for the optimizer to drop), which a test about what the value reads
-- must not count.
neededClauses :: [HornClause] -> [HornClause]
neededClauses [] = []
neededClauses cs = filter ((`Set.member` needed) . conclusion) cs
  where
    needed = foldr step (Set.singleton (conclusion (last cs))) cs
    step c acc
      | conclusion c `Set.member` acc = foldr Set.insert acc (premises c)
      | otherwise = acc

-- | Whether a step COMPUTES with a wildcard the chain certainly made up (an
-- arithmetic inverse, say, as against a deconstruction or an @==@ /
-- constructor-test inverse). Its result passes the wildcard on
-- ('passInjectedWildcard'), but the operation it inverts runs forward in the
-- body, on the witness, wherever the caller evaluates the body at it: @h +
-- 1.0@ at @h = ANY@ is a type error at @-O0@, where nothing folds the unread
-- body away. That is exactly a chain reading a wildcard, so the chain says so
-- ('invReadsAny'), and the caller takes its unevaluable-witness route (a
-- single-use binding's open body, else a refusal). Only the certain case is
-- static; a runtime test would have to re-emit the chain, which
-- 'readsAnyChain' exists to avoid.
computesOnCertainWildcard :: [ADTDecl] -> [(ChainName, Bool)] -> HornClause -> Bool
computesOnCertainWildcard adtsDecls wild c = case c of
  ExprHornClause _ _ (InjFInfo name) inv
    | Just Nothing <- injectedWildcardTest wild c ->
        let FPair fwd invs = lookupFPair adtsDecls name
            d = if inv == 0 then fwd else invs !! (inv - 1)
        in not (deconstructing d) && not (hasAnyExceptExpr (body d))
  _ -> False

-- | A step's applicability at a chain-introduced wildcard input: it holds, as
-- it does for a marginal wildcard ('isConstrGuard'). The domain is the
-- concrete value's to be outside of.
passWildApp :: [(ChainName, Bool)] -> HornClause -> IRExpr -> IRExpr
passWildApp _ _ app@(IRConst (VBool True)) = app
passWildApp wild c app = case injectedWildcardTest wild c of
  Nothing -> app
  Just Nothing -> IRConst (VBool True)
  Just (Just t) -> IRIf t (IRConst (VBool True)) app

-- | The rounded value and applicability of each exact integer-quotient step
-- of a chain, for a cumulative query (task cdf-through-discrete-inverse-wrong).
--
-- A CDF query transports a bound, not a point: @seed <= s@. Each step hands
-- the next a bound on its own result, pointing up or down. An integer step
-- @y * a = t@ given @t <= s@ needs @y <= floor(s/a)@ for @a > 0@ and
-- @y >= ceil(s/a)@ for @a < 0@ ('roundedQuotientInverse'); given @t >= s@ it
-- is the other way round. So the rounding is the floor exactly when the bound
-- coming OUT of the step points down, i.e. when the inverse from the seed
-- through this step is increasing -- the sign of the running product of the
-- step derivatives, the prefix of 'derivativeOfPath' ending here. Each factor
-- refers only to names bound earlier in the chain, so the prefix is in scope
-- where the step is bound. The witnessed variable's bound then points the way
-- the whole product does, which is the sign the caller's CDF flip reads.
cumulativeStep :: [ADTDecl] -> [HornClause] -> HornClause -> Maybe (IRExpr, IRExpr)
cumulativeStep adtsDecls path c = do
  (floorB, ceilB, app) <- roundedClause
  sign <- lookup (conclusion c) running
  return (IRIf (IROp OpGreaterThan sign (IRConst (VFloat 0))) floorB ceilB, app)
  where
    running = zip (map conclusion path) (scanl1 (IROp OpMult) (map (derivativeOfHornClause adtsDecls) path))
    roundedClause = case c of
      ExprHornClause preVars _ (InjFInfo name) inv | inv > 0 ->
        let FPair _ invInjF = lookupFPair adtsDecls name
            correctInv = invInjF !! (inv - 1)
        in roundedQuotientInverse (foldr (\(old, new) decl -> renameDecl old new decl) correctInv (zip (inputVars correctInv) preVars))
      _ -> Nothing

-- | A Bool IRExpr, safe to evaluate unconditionally, that is True iff every step
-- of the chain is within its inverse FDecl's applicability domain -- i.e. the
-- chain's value expression ('toLetInBlockWith') would not crash. Mirrors
-- 'wrapInLetInBlockWith's LetIn nesting so that a later step's applicability test
-- (which may reference an earlier step's bound value) is only evaluated once the
-- earlier step is known to be in-domain; a failing step short-circuits to False
-- without ever forcing the unsafe binding that follows it.
--
-- A step reading a chain-introduced wildcard is within its domain
-- ('passWildApp').
-- A hook rewrites each step's value first ('toPointValueExpr').
guardChain :: (HornClause -> IRExpr -> IRExpr) -> [(ChainName, Bool)] -> [[HornClause]] -> [ADTDecl] -> [HornClause] -> IRExpr
guardChain post wild clauses adtsDecls =
  guardChainWith (\c -> Just (post c (hornClauseToIRExpr clauses adtsDecls c), clauseApplicability adtsDecls c)) wild clauses adtsDecls

-- | 'guardChain' with some steps' value and applicability replaced (Just), as
-- 'cumulativeStep' replaces the rounded ones.
guardChainWith :: (HornClause -> Maybe (IRExpr, IRExpr)) -> [(ChainName, Bool)] -> [[HornClause]] -> [ADTDecl] -> [HornClause] -> IRExpr
guardChainWith _ _ _ _ [] = IRConst (VBool True)
guardChainWith override wild clauses adtsDecls (ParameterHornClause _:cs) = guardChainWith override wild clauses adtsDecls cs
guardChainWith override wild clauses adtsDecls (c:cs) =
  let (val0, app0) = fromMaybe (hornClauseToIRExpr clauses adtsDecls c, clauseApplicability adtsDecls c) (override c)
      val = passInjectedWildcard adtsDecls wild c val0
      app = passWildApp wild c app0
      rest = IRLetIn (conclusion c) val (guardChainWith override wild clauses adtsDecls cs)
  in case app of
    IRConst (VBool True) -> rest
    appTest -> IRIf appTest rest (IRConst (VBool False))

-- | A Bool IRExpr, safe to evaluate unconditionally, that is True iff some step
-- of the chain would read a marginal wildcard ('VAny') as an operand. An
-- inverse step's arithmetic and its deconstructions are both undefined there
-- -- @Minus (VAny, 3.0)@, @Fst VAny@ -- and the interpreter and the typed
-- backends answer a raw type error rather than the engine's refusal, so the
-- caller must test this BEFORE evaluating the value expression
-- (task fc-inverse-refuses-on-any-input).
--
-- A query's wildcard only ever enters at the seed and only ever travels along the
-- chain's *deconstructing* steps: an arithmetic step handed one does not
-- produce a wildcard, it dies, and by then this test has already answered True.
-- So the carriers -- the chain names whose runtime value can be a wildcard --
-- are the seed plus what the deconstructions reach from it, and each of them
-- has a direct accessor expression on the seed. That is what keeps this test
-- cheap: it never re-emits the chain's let-in block (which would double the
-- inverse at every nesting level of a let chain), only a handful of @isAny@
-- tests over accessor paths.
--
-- A wildcard a step makes up mid-chain (@fst@'s inverse answering
-- @(s, ANY)@) is not the query's; 'injectedWildcards' tracks those, and
-- 'toValueExpr' folds the certain ones into this test.
--
-- Nested like 'guardChain', for the same reason and with the same shape: a
-- step's premises are only inspected once every earlier step is known to be
-- in-domain, and a step that is out of its domain short-circuits to False
-- rather than True -- such a chain read no wildcard, and zeroing it is
-- 'guardChain's job, not this test's to refuse over.
--
-- What stays False here is a wildcard merely *copied* out of the chain, by an
-- equivalence step or as the final value: that is the *sink* case, decided at
-- the call site by testing the recovered value itself.
readsAnyChain :: [[HornClause]] -> [ADTDecl] -> [HornClause] -> IRExpr
readsAnyChain _ adtsDecls = go []
  where
    go _ [] = IRConst (VBool False)
    go carriers (c:cs) = foldr anyTest (afterTests carriers c cs) (readHits carriers c)
    anyTest e acc = IRIf (IRUnaryOp OpIsAny e) (IRConst (VBool True)) acc
    -- The carrier-valued premises this step computes with, in premise order.
    readHits carriers (ExprHornClause pre _ (InjFInfo _) _) = mapMaybe (`lookup` carriers) pre
    readHits _        _                                     = []
    afterTests carriers c cs = case c of
      -- The seed: the observation itself, which is what a marginal query puts
      -- a wildcard into.
      ParameterHornClause conc -> go ((conc, IRVar conc) : carriers) cs
      -- A copy, not a computation.
      EquivalenceHornClause [p] conc _ _
        | Just e <- lookup p carriers -> go ((conc, e) : carriers) cs
      _ | Just (inVar, bodyE, appE) <- deconstructionDecl adtsDecls c
        , Just src <- lookup inVar carriers ->
            let sub  = irMap (\e -> case e of IRVar n | n == inVar -> src; _ -> e)
                rest = go ((conclusion c, sub bodyE) : carriers) cs
            in case sub appE of
                 IRConst (VBool True) -> rest
                 appTest              -> IRIf appTest rest (IRConst (VBool False))
      _ -> go carriers cs

-- | The single-input FDecl a Horn clause invokes when that FDecl @deconstructing@s
-- its input -- @(input variable, body, applicability)@, all in the clause's own
-- premise names. These are the steps a wildcard survives (see 'readsAnyChain'):
-- @fst@/@snd@, @fromLeft@/@fromRight@, an ADT field accessor. Every other step
-- computes, and is handed the wildcard rather than passing it on.
deconstructionDecl :: [ADTDecl] -> HornClause -> Maybe (ChainName, IRExpr, IRExpr)
deconstructionDecl adtsDecls (ExprHornClause preVars _ (InjFInfo name) inv) =
  let FPair fwd invs = lookupFPair adtsDecls name
      decl           = if inv == 0 then fwd else invs !! (inv - 1)
      renamed        = foldr (\(old, new) d -> renameDecl old new d) decl (zip (inputVars decl) preVars)
  in case (deconstructing decl, inputVars renamed) of
       (True, [inVar]) -> Just (inVar, body renamed, applicability renamed)
       _               -> Nothing
deconstructionDecl _ _ = Nothing

-- | The applicability test of the inverse FDecl a Horn clause invokes (renamed
-- to the clause's own premise variables), or an unconditional True for clauses
-- that carry no domain restriction (constants, equivalences, forward InjF
-- applications, parameters).
clauseApplicability :: [ADTDecl] -> HornClause -> IRExpr
clauseApplicability adtsDecls (ExprHornClause preVars _ (InjFInfo name) inv) | inv > 0 =
  let FPair _ invInjF = lookupFPair adtsDecls name
      correctInv = invInjF !! (inv - 1)
      renamedF = foldr (\(old, new) decl -> renameDecl old new decl) correctInv (zip (inputVars correctInv) preVars)
  in applicability renamedF
clauseApplicability _ _ = IRConst (VBool True)

-- The clause-path core of 'toValueExpr': the topologically sorted, fulfilled
-- clauses up to (and including) the one concluding @startCN@, or Nothing when
-- forward chaining never derives it.
toValuePath :: [[HornClause]] -> [HornClause] -> ChainName -> Maybe [HornClause]
toValuePath clauses paramClauses startCN =
  case findConcludingHornClause solvedClauses startCN of
    Just concludingClause -> do
      -- Throw away superfluous clauses. Do this by sorting them by requirement
      -- and throwing away clauses after the clause that inferes the bound variable
      -- Also guarantees that the later generated letIns are in the correct order
      -- This may still contain some superflous clauses, but they can easily be detected by an optimizer
      let sortedClauses = topSortDAG solvedClauses
      Just (cutList sortedClauses concludingClause)
    Nothing -> Nothing
  where
    augmentedClauseSet = map (:[]) paramClauses ++ clauses
    -- Solve the set of Horn clauses for clauses which are fulfilled
    solvedClauses = solveHCSet augmentedClauseSet

-- | Whether the inverse chain seed→occurrence is monotone increasing or
-- decreasing, statically.
data Monotonicity = MonInc | MonDec deriving (Eq, Show)

-- | Like 'toSeededInvExpr', but for transporting an *interval* constraint
-- instead of a point: returns the inverse g (free variable @seedCN@) together
-- with a static monotonicity certificate. g monotone means g maps intervals to
-- intervals, with the endpoints swapped iff 'MonDec' — so
-- @seed ∈ [lo,hi] ⟺ occ ∈ [g lo, g hi]@ (resp. @[g hi, g lo]@). No Jacobian is
-- returned: interval mass needs no change-of-variables correction. Nothing when
-- there is no path or when a step on the value-carrying spine has no statically
-- known direction (e.g. multiplication by a non-literal operand) or is not a
-- scalar monotone float function at all.
--
-- Each spine step's input is first clamped into that step's forward
-- 'injFImage' ('clampToImage'), so an endpoint the forward function can never
-- produce is moved onto the image's boundary before the (partial) inverse
-- sees it, instead of being laundered into NaN and thence a silent zero mass
-- (task set-witness-interval-partial-inverse). Doing it per step, on the
-- step's own input, is what makes nested chains right: in @exp (exp x) > 0.5@
-- the outer step maps the bound to @log 0.5 < 0@, which the inner @exp@ can
-- never produce, so the inner step clamps it to 0 and answers @-inf@.
toSeededMonotoneInvExpr :: FCData -> [ADTDecl] -> ChainName -> ChainName -> Maybe (IRExpr, Monotonicity)
toSeededMonotoneInvExpr fcData adtsDecls seedCN occCN = do
  let clauses = hornClauses fcData
  path <- toValuePath clauses [ParameterHornClause seedCN] occCN
  spine <- chainSpine fcData path seedCN occCN
  dirs <- mapM (stepMonotonicity fcData) spine
  let dir = if odd (length (filter (== MonDec) dirs)) then MonDec else MonInc
  let clampInput c e
        | c `elem` spine
        , ExprHornClause _ _ (InjFInfo name) inv <- c, inv > 0
        , Just parent <- spineParent fcData c
        = substVar parent (clampToImage (injFImage name) (IRVar parent)) e
        | otherwise = e
  return (toLetInBlockWith clampInput clauses adtsDecls path, dir)
  where
    -- Every occurrence of the step's value-carrying premise inside the step's
    -- own inverse body. Not capture-avoiding: chain names are globally unique
    -- and an inverse FDecl body binds nothing.
    substVar n val = irMap (\e -> case e of { IRVar n' | n' == n -> val; _ -> e })

-- | The image of a monotone spine step's forward function in its
-- value-carrying argument -- the observed values that step can produce at
-- all. 'Nothing' on a side means unbounded there. Read next to
-- 'stepMonotonicity': an entry there whose inverse is partial needs an entry
-- here too, or an interval endpoint outside the image reaches the inverse
-- and comes back NaN.
data Image = Image { imageLo :: Maybe Double, imageHi :: Maybe Double }
  deriving (Eq, Show)

fullImage :: Image
fullImage = Image Nothing Nothing

-- | Per-InjF image table, keyed like 'stepMonotonicity'. Only @exp@ has a
-- proper sub-image today; every other monotone step in that table is onto
-- the reals (@log@ has a partial DOMAIN, not a partial image -- its inverse
-- @exp@ is total). The plan-guided engine's 'planPeelSlice' reads the same
-- table, so the two transports agree.
injFImage :: String -> Image
injFImage "exp" = Image (Just 0) Nothing
injFImage _     = fullImage

-- | Move a bound into the image before handing it to the step's inverse:
-- @max lo (min hi b)@, spelled with 'IRIf' since the IR has no float min/max
-- on every backend. A finite endpoint outside the image lands on the image's
-- boundary, which the inverse maps to the argument's own infinity (for
-- @exp@, @0 |-> log 0 = -inf@) -- exactly the preimage's endpoint; an
-- interval lying wholly outside the image collapses onto that boundary point
-- and so measures zero. Infinite bounds never reach this (the callers pass
-- them through untouched), which is right because the one entry with a
-- proper sub-image, @exp@, is continuous and strictly monotone on the whole
-- real line, so its image is open and its boundary IS the argument's
-- infinity -- an entry that attained its image boundary at a finite argument
-- would need the callers to clamp infinite bounds too. Identity on a full
-- image.
clampToImage :: Image -> IRExpr -> IRExpr
clampToImage (Image lo hi) b = clampLo lo (clampHi hi b)
  where
    clampLo Nothing e  = e
    clampLo (Just l) e = let c = IRConst (VFloat l) in IRIf (IROp OpLessThan e c) c e
    clampHi Nothing e  = e
    clampHi (Just h) e = let c = IRConst (VFloat h) in IRIf (IROp OpGreaterThan e c) c e

-- | The point-transport counterpart of 'clampToImage': Bool guards that hold
-- iff an observed POINT lies inside the image. A point outside it is not
-- moved but impossible (the world carrying it measures zero, and the
-- inverse is never evaluated on it). The tests are strict, which is exact
-- for @exp@'s open image and immaterial at the boundary of a closed one --
-- a single point of a continuous observation carries no mass.
-- Empty on a full image.
imageGuards :: Image -> IRExpr -> [IRExpr]
imageGuards (Image lo hi) b =
     [IROp OpGreaterThan b (IRConst (VFloat l)) | Just l <- [lo]]
  ++ [IROp OpLessThan b (IRConst (VFloat h))    | Just h <- [hi]]

-- The value-carrying spine of an inversion path: walking from the occurrence
-- back towards the seed, at each step the clause concluding the current node
-- and then its "parent" premise — the one holding the observed value flowing
-- down. Side computations (deriving the other operands) are not on the spine
-- and cannot affect monotonicity. Nothing when a spine step's parent cannot be
-- identified.
chainSpine :: FCData -> [HornClause] -> ChainName -> ChainName -> Maybe [HornClause]
chainSpine fcData path seedCN = go
  where
    go cn
      | cn == seedCN = Just []
      | otherwise = case findConcludingHornClause path cn of
          Nothing -> Just []  -- reached a self-sufficient start (parameter/anchor)
          Just (ParameterHornClause _) -> Just []
          Just c  -> do
            parent <- spineParent fcData c
            rest <- go parent
            return (c : rest)

-- The premise of a clause that carries the observed value. For an equivalence
-- it is the single premise; for an InjF inverse it is the conclusion of the
-- clause group's forward sibling (the node the inverted function computed) —
-- premise ORDER is not a reliable indicator, the forward output sits at
-- different positions in different inverse FDecls.
spineParent :: FCData -> HornClause -> Maybe ChainName
spineParent _ (EquivalenceHornClause [p] _ _ _) = Just p
spineParent _ (ExprHornClause [p] _ _ _) = Just p
spineParent fcData c@(ExprHornClause pres _ (InjFInfo _) inv) | inv > 0 = do
  grp <- find (c `elem`) (hornClauses fcData)
  fwd <- find (\cl -> isExprHornClause cl && inversion cl == 0) grp
  let parent = conclusion fwd
  if parent `elem` pres then Just parent else Nothing
spineParent _ _ = Nothing

-- Static monotonicity of one spine step, in its value-carrying argument.
-- Conservative: any InjF without an entry here fails the whole transport.
stepMonotonicity :: FCData -> HornClause -> Maybe Monotonicity
stepMonotonicity _ (EquivalenceHornClause {}) = Just MonInc
stepMonotonicity fcData c@(ExprHornClause pres _ (InjFInfo name) inv) | inv > 0 =
  case name of
    "plus"   -> Just MonInc   -- subtract the other operand
    "double" -> Just MonInc
    "exp"    -> Just MonInc   -- inverse is log
    "log"    -> Just MonInc   -- inverse is exp
    "neg"    -> Just MonDec
    "mult"   -> do
      -- divide by the other operand: direction is the sign of that operand,
      -- known statically only when it is a literal constant.
      parent <- spineParent fcData c
      case filter (/= parent) pres of
        [other] -> case lookup (untag other) (chainNameInfo fcData) of
          Just (ConstantInfo (VFloat f))
            | f > 0 -> Just MonInc
            | f < 0 -> Just MonDec
          _ -> Nothing
        _ -> Nothing
    -- The Int variants of the same steps (see 'resolveInjF'). Not @multI@:
    -- its inverse is exact division, which no interval endpoint survives.
    "plusI"  -> Just MonInc
    "negI"   -> Just MonDec
    _ -> Nothing
stepMonotonicity _ _ = Nothing

-- Takes a chain name of a point in the AST and finds the lambda, this point is equivalent to.
-- Also return the uniquely identifying tag if the lambda is tagged
findEquivalentExpression :: FCData -> ChainName -> Maybe (ChainName, ExprInfo, String)
findEquivalentExpression fcData startCN = go [startCN] startCN
  where
    go visited cn = case lookup cn (chainNameInfo fcData) of
      Nothing -> error $ "Could not find chainName in FCData " ++ cn
      Just x | isFinalExpr x -> Just (cn, x, "")
      Just _ -> do
        let origClauses = getAllOriginatingEquivalenceHornClauses (hornClauses fcData) cn
        case [hc | hc@EquivalenceHornClause{inversion = 1} <- origClauses] of
          [EquivalenceHornClause [pre] _ _ _] ->
            let next = untag pre in
            if next `elem` visited
              then Nothing  -- cycle detected; no valid lambda found along this chain
              else do
                (resCN, resInfo, _) <- go (next : visited) next
                return (resCN, resInfo, getTag pre)
          _ -> Nothing
    isFinalExpr (ApplyInfo _ _) = False
    isFinalExpr (VarInfo _) = False
    isFinalExpr _ = True

-- Build the 'lambdaVarOccurrences' map for a whole program: every Lambda node
-- paired with the (shadowing-aware) occurrences of its bound variable in its
-- own body. Empty for a dead binding — the caller decides; 'inversionSetup'
-- answers Nothing there.
progToLambdaVarOccurrences :: Program -> [(ChainName, [ChainName])]
progToLambdaVarOccurrences Program{functions=fs} = concatMap (go . snd) fs
  where
    go e@(Expr TypeInfo{chainName=cn} (Lambda n bodyExpr)) =
      (cn, varOccurrences n bodyExpr) : concatMap go (getSubExprs e)
    go e = concatMap go (getSubExprs e)
    varOccurrences n (Expr TypeInfo{chainName=cn} (Var m)) | m == n = [cn]
    varOccurrences n (Expr _ (Lambda m _)) | m == n = []  -- shadowed; don't descend
    varOccurrences n e = concatMap (varOccurrences n) (getSubExprs e)

-- Strip the expression of all wrapping lambdas. Return the chain name of the resulting expression and all names of the bound variables stripped away
unwrapLambdas :: FCData -> ChainName -> (ChainName, [String])
unwrapLambdas fcData cn = case lookup cn (chainNameInfo fcData) of
  Just (LambdaInfo name bodyName) ->
    let (lCN, names) = unwrapLambdas fcData bodyName in (lCN, name:names)
  Just _ -> (cn, [])
  Nothing -> error ("unwrapLambdas: no chain name '" ++ cn ++ "' in FCData")

-- This takes a list of value expressions and merges then such that in tuple constructions a existing value overwrites an ANY.
-- If two paths provide information for the same part of the tuple, we discard the second, because the should be semantically equal and therefor redundant
-- We also assume that the different paths do not have conflicting LetIns
-- The covariance factors are multiplied only in the two disjoint-tuple-slot
-- merges below (each path fills one component, the other ANY). Disjoint
-- components are independent coordinates, so the Jacobian is block-diagonal and
-- its determinant IS that product — the correct Gramian for this shape. Any other
-- merge takes the first path's covariance (semantically-equal values, one
-- Jacobian), never a product. Proven sound by investigation
-- forward-chaining-math-correctness.
-- The first three arguments are purely diagnostic context for the failure case below:
-- the name of the variable being witnessed, the chain name of the lambda being inverted,
-- and the candidate occurrences (chain names) that were attempted and yielded no path.
mergeExpr :: String -> ChainName -> [ChainName] -> [InvChain] -> InvChain
mergeExpr varName lambdaCN candidateCNs [] = error $ unlines
  [ "Forward chaining failed to find a solution: no inversion path could be constructed for variable \"" ++ varName ++ "\""
  , "while inverting the function bound at chain name " ++ lambdaCN ++ "."
  , "Candidate occurrences that were tried and could not be witnessed: " ++ show candidateCNs
  , "This usually means the function is not algebraically invertible in this variable (e.g. it is"
  , "many-to-one, like a count/sum of conditional contributions) and the program shape did not"
  , "qualify for enumeration-based inference instead (the IsConditional + toIREnumerate path in the"
  , "IRCompiler). See docs/forward-chaining-recursion-constraint.md for the failure analysis."
  ]
mergeExpr _ _ _ [x] = x
mergeExpr varName lambdaCN candidateCNs (x:xs) =
  let m = mergeExpr2 id x (mergeExpr varName lambdaCN candidateCNs xs)
  in pointChain (invValue m) (invCoV m) (invGuard m) (invReadsAny m)

-- The wildcard test merges by disjunction wherever the guards merge by
-- conjunction: a merged value is built out of both paths, so either path
-- reading a wildcard makes the merged value unevaluable.
mergeExpr2 :: (IRExpr -> IRExpr) -> InvChain -> InvChain -> InvChain
mergeExpr2 bindings c1@InvChain{invValue = IRLetIn n v bodyExpr1} c2 = mergeExpr2 (bindings . IRLetIn n v) c1{invValue = bodyExpr1} c2
mergeExpr2 bindings c1 c2@InvChain{invValue = IRLetIn n v bodyExpr2} = mergeExpr2 (bindings . IRLetIn n v) c1 c2{invValue = bodyExpr2}
mergeExpr2 bindings (InvChain (IRConstruct TgTuple [IRConst VAny, b]) cov1 g1 ra1 _ _) (InvChain (IRConstruct TgTuple [a, IRConst VAny]) cov2 g2 ra2 _ _) = pointChain (bindings $ IRConstruct TgTuple [a, b]) (IROp OpMult cov1 cov2) (IROp OpAnd g1 g2) (IROp OpOr ra1 ra2)
mergeExpr2 bindings (InvChain (IRConstruct TgTuple [a, IRConst VAny]) cov1 g1 ra1 _ _) (InvChain (IRConstruct TgTuple [IRConst VAny, b]) cov2 g2 ra2 _ _) = pointChain (bindings $ IRConstruct TgTuple [a, b]) (IROp OpMult cov1 cov2) (IROp OpAnd g1 g2) (IROp OpOr ra1 ra2)
-- The same, field by field, for a user-ADT constructor: one path knows the
-- constructor only (@isDCons ds@ inverts to @DCons ANY ANY@), another a field
-- of it (@dig ds * 3 == 21@ to @DCons 7 ANY@). Taking the first, as below,
-- dropped the field: the observation was answered as P(DCons), with the
-- digit never constrained (a silent wrong result once that inverse compiled,
-- fuzz-admission-oracle-bugs item 9). Fields a path leaves ANY carry no
-- coordinate, so the Jacobian is the product as for the tuple slots.
mergeExpr2 bindings (InvChain e1 cov1 g1 ra1 _ _) (InvChain e2 cov2 g2 ra2 _ _)
  | Just (c1, fs1) <- ctorSpine e1, Just (c2, fs2) <- ctorSpine e2
  , c1 == c2, length fs1 == length fs2
  , and (zipWith (\a b -> isAnyConst a || isAnyConst b) fs1 fs2)
  , any (not . isAnyConst) fs2
  = pointChain (bindings $ foldl IRApply (IRVar c1) (zipWith (\a b -> if isAnyConst a then b else a) fs1 fs2))
             (IROp OpMult cov1 cov2) (IROp OpAnd g1 g2) (IROp OpOr ra1 ra2)
  where
    isAnyConst (IRConst VAny) = True
    isAnyConst _ = False
    ctorSpine e = go e []
      where go (IRApply f x) acc = go f (x : acc)
            go (IRVar c@(h:_)) acc@(_:_) | isUpper h = Just (c, acc)
            go _ _ = Nothing
-- Expressions are not compatible. Assume they are semantically equal. Then just
-- take the first -- unless only the second is a whole value. A constructor
-- test's inverse knows the constructor and nothing else (@Face ANY ANY@, or
-- the @VAnyExcept@ "anything but" on False); in @(isFace h, h)@ it came first,
-- the slot holding @h@ itself was dropped, and every field went unconstrained:
-- 1.0 at every point (task tuple-ctor-test-of-shared-draw-wrong-result), with
-- @isFace@ of the sentinel crashing at a False first slot. Taking the whole
-- value loses nothing: the consistency of every slot with the witness is
-- checked for the query as a whole.
mergeExpr2 bindings c1 c2
  | holdsWildcard (invValue c1), not (holdsWildcard (invValue c2)) = c2{invValue = bindings (invValue c2)}
  | otherwise = c1{invValue = bindings (invValue c1)}
  where
    holdsWildcard e = any isWildcard (universeIR e)
    isWildcard (IRConst VAny) = True
    isWildcard (IRConst (VAnyExcept _)) = True
    isWildcard _ = False
    universeIR e = e : concatMap universeIR (getIRSubExprs e)

getAllOriginatingEquivalenceHornClauses :: [[HornClause]] -> ChainName -> [HornClause]
getAllOriginatingEquivalenceHornClauses clauses cn = concatMap (filter (\hc -> isEquivalenceHornClause hc && conclusion hc == cn)) clauses

-- Takes a list of Horn clauses and converts them to nested letIn expressions.
-- We do this by declaring a new variable named after the conclusion of the clause
-- The value of this letIn depends on the type of Horn clause, but is in general either the forward path or an inversion of the expression used to create the clause
-- Each clause's expression passes through a hook before it is bound (or,
-- for the last clause, returned): 'toSeededMonotoneInvExpr' uses it to clamp
-- a spine step's input into the step's image, 'toValueExpr' to pass a
-- chain-introduced wildcard on ('passInjectedWildcard').
toLetInBlockWith :: (HornClause -> IRExpr -> IRExpr) -> [[HornClause]] -> [ADTDecl] -> [HornClause] -> IRExpr
toLetInBlockWith _ _ _ [] = error "Cannot convert empty clause set to LetIn block"
toLetInBlockWith post clauses adtsDecls cs = wrapInLetInBlockWith post clauses adtsDecls (init cs) (post (last cs) (hornClauseToIRExpr clauses adtsDecls (last cs)))

wrapInLetInBlockWith :: (HornClause -> IRExpr -> IRExpr) -> [[HornClause]] -> [ADTDecl] -> [HornClause] -> IRExpr -> IRExpr
wrapInLetInBlockWith post clauses adtsDecls (ParameterHornClause _:cs) inner = wrapInLetInBlockWith post clauses adtsDecls cs inner
wrapInLetInBlockWith post clauses adtsDecls (c:cs) inner = IRLetIn (conclusion c) (post c (hornClauseToIRExpr clauses adtsDecls c)) (wrapInLetInBlockWith post clauses adtsDecls cs inner)
wrapInLetInBlockWith _ _ _ [] inner = inner

-- Generates IRExpr from Horn clauses
hornClauseToIRExpr :: [[HornClause]] -> [ADTDecl] -> HornClause -> IRExpr
hornClauseToIRExpr _ adtsDecls clause =
  case clause of
    -- Constants are always their value
    ExprHornClause _ _ (ConstantInfo v) 0 -> IRConst (valueToIR v)
    -- Get the correct names of the parameters from the horn clause and instantiate the InjF
    ExprHornClause preVars _ (InjFInfo name) inv | inv == 0 ->
        let FPair fwdInjF _ = lookupFPair adtsDecls name
            renamedF = foldr (\(old, new) decl -> renameDecl old new decl) fwdInjF (zip (inputVars fwdInjF) preVars) in
              body renamedF
    -- Similar to the forward InjF, but additionally find the correct inversion first
    -- Inversions are always in the correct order in globalFEnv, because the inversion number is created from this order
    ExprHornClause preVars _ (InjFInfo name) inv -> do
      let FPair _ invInjF = lookupFPair adtsDecls name
      let correctInv = invInjF !! (inv - 1)
      let renamedF = foldr (\(old, new) decl -> renameDecl old new decl) correctInv (zip (inputVars correctInv) preVars)
      body renamedF
    ParameterHornClause conc -> IRVar conc
    EquivalenceHornClause [p] _ _ _ -> IRVar p
    _ -> error $ "Cannot convert clause to IRExpr: " ++ show clause

-- Finds the first horn clause in a list that has a given conclusion
findConcludingHornClause :: [HornClause] -> ChainName -> Maybe HornClause
findConcludingHornClause hcs cn =
  case filter ((== cn) . conclusion) hcs of
    [] -> Nothing
    res -> Just $ head res

-- An FC inversion path is a linear chain of single-input invertible steps, and
-- the witnessed variable flows through it exactly once (a step with two
-- un-witnessed random inputs has no inversion clause and never enters a path).
-- So this product of per-step inverse derivatives IS the chain rule
-- d/dx g(h(x)) = g'(h(x))·h'(x), i.e. the full path Jacobian — proven sound under
-- that structural constraint by investigation forward-chaining-math-correctness.
derivativeOfPath :: [ADTDecl] -> [HornClause] -> IRExpr
derivativeOfPath adtsDecls clauses = foldr1 (IROp OpMult) derivs
  where derivs = map (derivativeOfHornClause adtsDecls) clauses

derivativeOfHornClause :: [ADTDecl] -> HornClause -> IRExpr
derivativeOfHornClause adtsDecls (ExprHornClause pre _ (InjFInfo name) inv) | inv > 0 = do
  let FPair injFFwdDecl injFInvDecls = lookupFPair adtsDecls name
  let correctDecl = injFInvDecls !! (inv - 1)
  -- The premises of the of the HornClause are the input of the inverse InjF
  let FDecl {derivatives=invDerivs} = foldr (\(old, new) decl -> renameDecl old new decl) correctDecl (zip (inputVars correctDecl) pre)
  -- We need to find out which variable is the output of the forward InjF. For this take the fwd InjF and do the same renaming as for the inverse
  let invVar = soleOutputVar (foldr (\(old, new) decl -> renameDecl old new decl) injFFwdDecl (zip (inputVars correctDecl) pre))
  fromJust $ lookup invVar invDerivs
derivativeOfHornClause _ _ = IRConst (VFloat 1.0)

-- | Build the forward-chaining certificate for a whole program. The 'Set'
-- argument is the determinism field's known-anchor set (chain names whose value
-- is known without observing the sample); it seeds extra self-sufficient anchors
-- beyond the structural @Constant@-only approximation (modality-determinism-pass,
-- consumed here per modality-split-forwardchaining).
progToFCData :: Set ChainName -> Program -> FCData
progToFCData anchors prog =
  FCData { hornClauses = anchorClauses ++ baseClauses
         , chainNameInfo = cnInfo
         , fcAnchors = anchorInstances
         , lambdaVarOccurrences = progToLambdaVarOccurrences prog }
  where
    cnInfo = progToChainNameInfo prog
    baseClauses = progToHornClauses prog cnInfo
    -- Each known anchor is a self-sufficient (empty-premise) starting point for
    -- forward chaining, mirroring how @Constant@ already self-derives. This
    -- replaces FC's structural @Constant@-only under-approximation with the real
    -- determinism field, so ThetaI/Subtree/derived-deterministic operands become
    -- invertible-through.
    --
    -- Anchors are computed on the untagged program, but FC tags chain names per
    -- function invocation (e.g. @ast5_t0@) when it duplicates a helper-function
    -- body. So we anchor every chain name in the clause graph whose /untagged/
    -- form is a known anchor — otherwise a @theta@ inside an inverted helper
    -- (the @inner z = z + theta_0@ shape) would never match. The corresponding
    -- values are materialised in codegen (IRCompiler) for non-constant anchors.
    anchorInstances = Set.fromList
      [ cn | cn <- allClauseChainNames baseClauses, Set.member (untag cn) anchors ]
    anchorClauses = [ [ParameterHornClause cn] | cn <- Set.toList anchorInstances ]

-- Every chain name appearing as a premise or conclusion anywhere in a clause set.
allClauseChainNames :: [[HornClause]] -> [ChainName]
allClauseChainNames = nub . concatMap (concatMap (\c -> conclusion c : premises c))


progToChainNameInfo :: Program -> [(ChainName, ExprInfo)]
progToChainNameInfo Program{functions=fs} = concatMap (exprToChainNameInfo . snd) fs

exprToChainNameInfo :: Expr -> [(ChainName, ExprInfo)]
exprToChainNameInfo (Expr TypeInfo{chainName=cn} (Lambda n b)) = (cn, LambdaInfo n (getChainName b)):exprToChainNameInfo b
exprToChainNameInfo (Expr TypeInfo{chainName=cn} (Constant v)) = [(cn, ConstantInfo v)]
exprToChainNameInfo (Expr TypeInfo{chainName=cn} (Var n)) = [(cn, VarInfo n)]
exprToChainNameInfo (Expr TypeInfo{chainName=cn} (Apply l v)) = (cn, ApplyInfo (getChainName l) (getChainName v)):exprToChainNameInfo l ++ exprToChainNameInfo v
exprToChainNameInfo (Expr TypeInfo{chainName=cn} (IfThenElse c t e)) = (cn, IfInfo (getChainName c) (getChainName t) (getChainName e)): exprToChainNameInfo c ++ exprToChainNameInfo t ++ exprToChainNameInfo e
exprToChainNameInfo e = (getChainName e, StubInfo (toStub e)):concatMap exprToChainNameInfo (getSubExprs e)

-- Convert a Program to a set of groups of Horn clauses
progToHornClauses :: Program -> [(ChainName, ExprInfo)] -> [[HornClause]]
progToHornClauses Program{functions=fs, adts=adtsDecls} _ = nub $ initialRun ++ topEquivClauses ++ equivClauses
  where
    -- We need two runs for this: first run is every expression converted into a group of Horn clauses
    initialRun = concatMap (exprToHornClauses adtsDecls . snd) fs
    topEquivClauses = constructTopLevelEquivalenceClauses initialRun fs
    equivClauses = lambdasToHornClauses (initialRun ++ topEquivClauses) fs

-- Converts an expression with all its subexpressions into Horn clauses
exprToHornClauses :: [ADTDecl] -> Expr -> [[HornClause]]
exprToHornClauses adtsDecls e = case e of
  Expr _ (Constant v) -> [[ExprHornClause [] (getChainName e) (ConstantInfo v) 0]]
  -- Field constructors (Cons/TCons/user-ADT constructors) emit only their
  -- inverse clauses, each in its own group because the fields can be solved
  -- independently. The forward clause is omitted deliberately: constructing the
  -- container from its fields could create cycles in the chaining graph. This is
  -- safe (not merely defensive): container construction inference is handled
  -- out-of-band by IRCompiler's field-constructor path, so no program needs the
  -- forward clause (investigation forward-chaining-math-correctness, Q3).
  Expr _ (InjF (Named name) params)
    | isFieldConstructor adtsDecls name ->
        map (: []) (tail (injFtoHornClause adtsDecls e)) ++ concatMap (exprToHornClauses adtsDecls) params
  Expr _ (InjF _ params) -> injFtoHornClause adtsDecls e: concatMap (exprToHornClauses adtsDecls) params
  -- Some expressions are not invertable and therefor do not produce Horn clauses
  _ -> concatMap (exprToHornClauses adtsDecls) (getSubExprs e)

-- Converts an instance of a InjF into a Horn clause with corresponding variables in the premises and conclusion
injFtoHornClause :: [ADTDecl] -> Expr -> [HornClause]
injFtoHornClause adtsDecls e = case e of
  -- Forward Horn clause: Inverse Horn clauses with corresponding inversion number
  Expr TypeInfo{rType=rt} (InjF (Named name0) _) -> (constructInjFHornClause subst eCN name eFwd 0): zipWith (constructInjFHornClause subst eCN name) eInv [1..]
    where
      -- The Int variant where the node is Int-typed, as IRCompiler dispatches it.
      name = resolveInjF rt name0
      -- Create a substitution, that maps the variables in the declaration of the InjF
      -- to the ChainNames in the instantiation
      subst = (outV, eCN):zip inV (getInputChainNames e)
      eCN = chainName $ getTypeInfo e
      inV = inputVars eFwd
      outV = soleOutputVar eFwd
      FPair eFwd eInv = lookupFPair adtsDecls name
  _ -> error "Cannot get horn clause of non-predefined function"

-- Creates a Horn clause of an FDecl and substitutes the variables with a substition
constructInjFHornClause :: [(String, ChainName)] -> ChainName -> String -> FDecl -> Int -> HornClause
constructInjFHornClause subst _ name decl inv = ExprHornClause (map lookupSubst inV) (lookupSubst outV) (InjFInfo name) inv
  where
    inV = inputVars decl
    outV = soleOutputVar decl
    lookupSubst v = fromJust (lookup v subst)

-- Find the chainName this a given chain name is equivalent to
-- TODO: Can multiple equivalences happen? What then?
getEquivCN :: [[HornClause]] -> ChainName -> ChainName
getEquivCN clauses cn = fromMaybe (error $ "Found no equivalent chain name to: " ++ cn) (getEquivCNMaybe clauses cn)

-- 'getEquivCN', recoverable: 'Nothing' where that errors with "no equivalent
-- chain name" (a value with no single equivalence -- e.g. an if-selected
-- mixture of closures, which has no ONE body an equivalence clause could name).
-- Still errors on more than one candidate -- that is a genuine invariant
-- violation elsewhere, not a shape this caller is meant to tolerate.
getEquivCNMaybe :: [[HornClause]] -> ChainName -> Maybe ChainName
getEquivCNMaybe clauses cn = case [hc | hc@(EquivalenceHornClause [pre] _ _ _) <- equiv, pre == cn] of
  [EquivalenceHornClause _ back _ _] -> Just back
  []                                 -> Nothing
  _ -> error $ "Found multiple equivalent chain name to: " ++ cn
  where
    equiv = filter isEquivalenceHornClause (map head clauses)

-- Applies create two different types of quivalences in a program.
-- 1. Bound variables are equivalent to the value of their binding apply
-- 2. An Apply is equivalent to the body of the lambda it applies
-- This function creates HornCLauses for these equivalences
lambdasToHornClauses :: [[HornClause]] -> [FnDecl] -> [[HornClause]]
lambdasToHornClauses clauses fns = fixpointLoop fExprs clauses
  where
    fExprs = map snd fns
    fixpointLoop exprs cs = let extension = concatMap (constructEquivalenceClauses cs fExprs) exprs in if null extension then cs else fixpointLoop exprs (extension ++ cs)

-- Top level functions act like an apply binding their body to their name
constructTopLevelEquivalenceClauses :: [[HornClause]] -> [FnDecl] -> [[HornClause]]
constructTopLevelEquivalenceClauses clauses decls = concatMap (constructTopLevelEquivalenceClauses' clauses (map snd decls)) decls

constructTopLevelEquivalenceClauses' :: [[HornClause]] -> [Expr] -> FnDecl -> [[HornClause]]
constructTopLevelEquivalenceClauses' clauses exprs (name, expr) = case rType (getTypeInfo expr) of
  TArrow _ _ -> concat $ evalSupply $ mapM (\otherExpr -> do
    let (_, bodyExpr) = asLambda "constructTopLevelEquivalenceClauses'" expr
    let dependent = getDependentGroups clauses (getChainName bodyExpr)
    (varClauses, applyCnt) <- associateFunctionVariable name (getChainName expr) "" otherExpr
    let taggedDependents = concatMap (\tag -> map (tagGroup tag) dependent) [0..applyCnt - 1]
    return $ varClauses ++ taggedDependents) exprs
  _ -> concatMap (associateVariable name (getChainName expr) "") exprs

-- Construct horn clauses for equivalences induced by Applies. See lambdasToHornClauses for more info
constructEquivalenceClauses :: [[HornClause]] -> [Expr] -> Expr -> [[HornClause]]
constructEquivalenceClauses clauses exprs (Expr TypeInfo{chainName=exCn} (Apply l v)) | not (isInClauseSet clauses exCn) && (isLambdaExpr l || isInClauseSet clauses (getChainName l)) = do
    -- Find the declaration of the lambda on the left side of the Apply. Trivial if the lambda is directly there, else follow equivalences
    let (_, lTag, lVar, lBody) = case l of
          Expr TypeInfo{chainName=lCn'} (Lambda n bodyExpr) -> (lCn', "", n, bodyExpr)
          _ ->
            let appliedLambdaCn = getEquivCN clauses (getChainName l)
                appliedLambdaTag = getTag appliedLambdaCn
                (name, bodyExpr) = asLambda "constructEquivalenceClauses" (findExprWithCN exprs (untag appliedLambdaCn)) in
                  (appliedLambdaCn, appliedLambdaTag, name, bodyExpr)
    let lBodyCn = getChainName lBody ++ lTag
    -- The Apply is equivalent to the body of the lambda it is applying
    let appliedGroup = createEquivHornClauseGroup AppliedEquivalence exCn lBodyCn
    -- The Var expressions are equivalent to the value bound to them
    -- The following depends on whether the applied value is a function or a plain value
    case rType (getTypeInfo v) of
      -- If it is a function we have the problems if the function is invoked multiple times, because different invokations may have differrnt return values.
      -- This is not possible, because we identify values by their chainName, which is the same for different invokations
      -- Solve this by duplicating the sub-AST of the function and tagging each chainName with a tag unique for each invokation
      TArrow _ _ ->
        -- Find the lambda bound. A value that does not resolve to exactly one
        -- lambda body -- e.g. an if-selected mixture of two different closures
        -- (task arrow-lifted-mixture-for-function-values) -- has no single body
        -- to tag per-invocation copies against: there is nothing to make the
        -- multiple-invocation distinction FOR here, since there is no one
        -- lambda whose sub-AST could be duplicated and tagged. Skip the
        -- tagging (this Apply's own equivalence-to-its-body clause still
        -- stands) rather than crash building a certificate that a mixture's
        -- OWN compilation path (the pointwise-lifted mixture combinator in
        -- IRCompiler) never consults anyway.
        case resolveVLambdaCn of
          Nothing -> [appliedGroup]
          Just vLambdaCn -> do
            let (_, vBody) = asLambda "constructEquivalenceClauses" (findExprWithCN exprs vLambdaCn)
            -- Get all horn clauses, which corresspond to expressions in the sub-AST of the lambda
            let dependent = getDependentGroups clauses (getChainName vBody)
            -- Supply each invokation with a unique tag and create the corresponding clauses
            let (varClauses, applyCnt) = evalSupply $ associateFunctionVariable lVar vLambdaCn lTag lBody
            -- Create a tagged copy of the dependent Hron clauses
            let taggedDependents = concatMap (\tag -> map (tagGroup tag) dependent) [0..applyCnt - 1]
            appliedGroup:varClauses ++ taggedDependents
        where
          resolveVLambdaCn = case v of
            Expr TypeInfo{chainName = vlCn} (Lambda _ _) -> Just vlCn
            _ -> do
              cn <- getEquivCNMaybe clauses (getChainName v)
              case findExprWithCN exprs cn of
                Expr _ Lambda{} -> Just cn
                _               -> Nothing
      -- Easy if the applied value is no function, because it is constant across the program.
      _ ->
        -- We still need to create a tagged group if our original lambda was tagged
        let taggedGroups = if null lTag then [] else map (map (tagHornClause lTag)) (getDependentGroups clauses (getChainName lBody)) in
        appliedGroup:taggedGroups ++ associateVariable lVar (getChainName v) lTag lBody
  where
    isLambdaExpr (Expr _ Lambda{}) = True
    isLambdaExpr _ = False
constructEquivalenceClauses clauses exprs ex = concatMap (constructEquivalenceClauses clauses exprs) (getSubExprs ex)


isInClauseSet :: [[HornClause]] -> ChainName -> Bool
isInClauseSet clauses cn = any (\cs -> isEquivalenceHornClause (head cs) && premises (getForwardClauseOfGroup cs) == [cn]) clauses

-- Creates Horn clauses implying an equivalence between a given chainName and all occurances of a given variable in an expression
associateVariable :: String -> ChainName -> String -> Expr -> [[HornClause]]
associateVariable varName chainTo tag (Expr TypeInfo{chainName=cn} (Var n)) | n == varName = [createEquivHornClauseGroup (VariableEquivalence varName) (cn ++ tag) chainTo]
associateVariable varName chainTo tag ex = concatMap (associateVariable varName chainTo tag) (getSubExprs ex)

-- Creates Horn clauses implying an equivalence between a given chainName and all occurances of a given variable in an expression
-- Gives each variable a unique tag. The number of tags created is returned
associateFunctionVariable :: String -> ChainName -> String -> Expr -> Supply ([[HornClause]], Int)
associateFunctionVariable varName chainTo tag (Expr TypeInfo{chainName=cn} (Var n)) | n == varName = demandUniqueNumber <&> \num -> ([createEquivHornClauseGroup (VariableEquivalence varName) (cn ++ tag) (chainTo ++ tagPrefix ++ show num)], 1)
associateFunctionVariable varName _ _ (Expr _ (Lambda n _)) | n == varName = return ([], 0)  -- Variable is shadowed. Don't search in this branch
associateFunctionVariable varName chainTo tag ex = do
  a <- mapM (associateFunctionVariable varName chainTo tag) (getSubExprs ex)
  return (concatMap fst a, sum (map snd a))

-- Creates a Horn clause group implying equivalence between two chain names
createEquivHornClauseGroup :: EquivalenceType -> ChainName -> ChainName -> [HornClause]
createEquivHornClauseGroup ty cn1 cn2 = [EquivalenceHornClause [cn1] cn2 ty 0, EquivalenceHornClause [cn2] cn1 ty 1]

findExprWithCN :: [Expr] -> ChainName -> Expr
findExprWithCN exprs cn = case mapMaybe (findExprWithCN' cn) exprs of
  [e] -> e
  [] -> error $ "Expression with given chain name not found " ++ cn
  _ -> error $ "Multiple expressions with the same chain name" ++ cn

findExprWithCN' :: ChainName -> Expr -> Maybe Expr
findExprWithCN' cn expr | getChainName expr == cn = Just expr
findExprWithCN' cn expr = msum $ map (findExprWithCN' cn) (getSubExprs expr)

-- A tag is a suffix to a chain name. It consists of this prefix with a number appended
tagPrefix :: String
tagPrefix = "_t"

-- Remove a tag from a chain name
untag :: ChainName -> ChainName
untag = fst . splitByString tagPrefix

getTag :: ChainName -> String
getTag = snd . splitByString tagPrefix

tagGroup :: Int -> [HornClause] -> [HornClause]
tagGroup tagNum group = do
  let tag = tagPrefix ++ show tagNum
  map (tagHornClause tag) group

-- Tag all clauses in a group
tagHornClause :: String -> HornClause -> HornClause
tagHornClause tag (ExprHornClause pre conc info inv) = ExprHornClause (map (++ tag) pre) (conc ++ tag) info inv
tagHornClause tag (EquivalenceHornClause pre conc info inv) = EquivalenceHornClause (map (++ tag) pre) (conc ++ tag) info inv
tagHornClause tag (ParameterHornClause conc) = ParameterHornClause (conc ++ tag)


getDependentGroups :: [[HornClause]] -> ChainName -> [[HornClause]]
getDependentGroups clauses cn = directDependence cn ++ concatMap (getDependentGroups clauses) (concatMap forwardPremises (directDependence cn))
  where
    -- Variable equivalences work the other way around as other clauses
    --forwardConclusion cs = let fc = getForwardClauseOfGroup cs in if isEquivalenceHornClause fc && isVariableEquivalence (equivalenceType fc) then head $ premises fc else conclusion fc
    forwardConclusion = conclusion . getForwardClauseOfGroup
    -- We want to include the equivalence clauses in the dependent clauses, but don't want to follow their jumps
    forwardPremises cs
      | hasForwardClause cs = let fc = getForwardClauseOfGroup cs in if isEquivalenceHornClause fc then [] else premises fc
      -- A field constructor's group carries only its inverse clauses (see
      -- exprToHornClauses), each deconstructing the container into one field:
      -- the fields are that group's sub-expressions.
      | otherwise = map conclusion cs
    --forwardPremises = premises . getForwardClauseOfGroup
    directDependence c = filter (dependsOn c) clauses
    dependsOn c cs
      | hasForwardClause cs = forwardConclusion cs == c
      -- Inverse-only (field constructor) group: it belongs to the container it
      -- deconstructs. Skipping these used to drop every field of a list/tuple/ADT
      -- constructor from a named function's per-invocation tagged copy, so its
      -- parameter could not be recovered from e.g. the head of the returned list
      -- (task named-function-list-head-witness-not-recovered).
      | otherwise = any (\cl -> isExprHornClause cl && premises cl == [c]) cs
    hasForwardClause = any ((== 0) . inversion)

-- Some clause groups, like TCons, may not have a forward clause. You need to make sure this is not the case when incokink this function
getForwardClauseOfGroup :: [HornClause] -> HornClause
getForwardClauseOfGroup clauses = case filter (\c -> (isExprHornClause c || isEquivalenceHornClause c) && inversion c == 0) clauses of
  [x] -> x
  [] -> error $ "Found no forward clause in clause group: " ++ show clauses
  _ -> error $ "Found multiple forward clauses in clause group: " ++ show clauses

-- Chain name of subexpressions
getInputChainNames :: Expr -> [ChainName]
getInputChainNames e = map getChainName (getSubExprs e)

-- Annotates a Program with chain names for every expression
annotateProg :: Program -> Program
annotateProg p@Program {functions=fs} = p{functions=annotFs}
  where
    annotFs = evalSupply (mapM (\(n, f) -> annotateExpr f <&> \x -> (n, x)) fs)


-- Annotate an expression and all of its subexpressions
annotateExpr :: Expr -> Supply Expr
annotateExpr = tMapM (\ex -> demandUniqueNumber <&> ("ast" ++) . show <&> setChainName (getTypeInfo ex))

-- Returns all recursively fulfilled clauses, in reverse discovery order (most
-- recently fulfilled first), matching the legacy accumulation order downstream
-- code (findConcludingHornClause / topSortDAG) relies on.
--
-- Each clause group contributes at most one fulfilled clause: the first whose
-- premises are all already known AND whose conclusion is not already derived.
-- We track used groups by index and known conclusions in 'Set's, so membership
-- tests are logarithmic rather than the linear list 'delete'/'elem' scans this
-- used to do (cleanup-forward-chaining).
--
-- The conclusion test is what keeps the fulfilled set ACYCLIC, and it is
-- load-bearing rather than an optimisation. A chain name reachable by two
-- routes (an over-determined observation: @(x, (x+y+3, x+y+2))@, where both
-- tuple slots recover @y@ and hence @x@) used to fulfil both routes -- the
-- second one only after the cycle had already closed the long way round --
-- yielding two clauses concluding the same name, one of them with a premise
-- that no earlier clause binds. 'topSortDAG' cannot order a cycle, so codegen
-- emitted a shadowing @let ast18 = ast14@ over an unbound @ast14@ and the query
-- died at run time with "Variable ast14 not declared" (task
-- multi-path-recovery-unmaterialized-crash). Since forward chaining's premise
-- is that two routes to a name are semantically equal, the second derivation
-- carries no information; dropping it loses nothing, and the redundancy is
-- still paid for where it belongs -- in the deterministic-slot consistency
-- indicator IRCompiler emits for the observation as a whole.
solveHCSet :: [[HornClause]] -> [HornClause]
solveHCSet hcs = go Set.empty Set.empty []
  where
    groups = zip [0 :: Int ..] hcs
    go usedGroups detVars fulfilled =
      case [ (i, c) | (i, g) <- groups
                    , not (i `Set.member` usedGroups)
                    , c <- g
                    , all (`Set.member` detVars) (premises c)
                    , not (conclusion c `Set.member` detVars) ] of
        [] -> fulfilled
        ((i, c):_) -> go (Set.insert i usedGroups) (Set.insert (conclusion c) detVars) (c : fulfilled)

-- Returns all elements that come before a given parameter in a list
cutList :: Eq a => [a] -> a -> [a]
cutList [] _ = []
cutList (x:xs) stop
  | x == stop = [x]
  | otherwise = x : cutList xs stop


-- Define a DAG Edge that corresponds to dependancy. A is less than B if B depends on A 
instance DAGEdge HornClause where
  -- A <= B iff B depends on A
  edge :: HornClause -> HornClause -> Bool
  c1 `edge` c2 = conclusion c1 `elem` premises c2




-- Pretty printing / Debugging functions for horn clause sets
showClause :: HornClause -> [Char]
showClause (ExprHornClause pre conc info inv) = show pre ++ " -> " ++ conc ++ " (Inv " ++ show inv ++ ", Expression) " ++ show info
showClause (EquivalenceHornClause [pre] conc info inv) = pre ++ " -> " ++ conc ++ " (Inv " ++ show inv ++ ", Equivalence) " ++ show info
showClause (EquivalenceHornClause pre conc info inv) = show pre ++ " -> " ++ conc ++ " (Inv " ++ show inv ++ ", Equivalence) " ++ show info
showClause (ParameterHornClause param) = "Parameter " ++ param

showClauseGroup :: [HornClause] -> String
showClauseGroup cs = intercalate "\n" (map showClause cs)

showClauseGroups :: [[HornClause]] -> String
showClauseGroups groups = intercalate "\n\n" (map showClauseGroup groups)
