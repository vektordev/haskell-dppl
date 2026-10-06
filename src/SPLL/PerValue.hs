-- | Per-value queries (task @per-value-query-over-enumerated-slot@).
--
-- A function whose type signature marks one slot of its result @Enumerated@,
--
-- > main2 :: Symbol -> (Enumerated Int, Face)
-- > main2 = main
--
-- answers a probability query with the whole vector
-- @[P(slot = v, rest) | v <- domain slot]@ in one call, instead of one number.
-- Two properties fix the meaning, and the tests pin both: element @v@ is the
-- point query with the slot set to @v@, and the vector's sum is the query with
-- the slot @ANY@. The value the query carries at the marked slot is ignored
-- (pass @ANY@); every other slot follows the ordinary query rules, @ANY@ holes
-- included. @topK@ pruning, the dimension and the impossibility flag are each
-- the point query's, per element.
--
-- The result is laid out as the point query's result with every field turned
-- into a vector over the domain, plus the domain itself as a last field:
-- @(probs, (dims, (imposs, values)))@, or @(probs, (dims, (branchCounts,
-- (imposs, values))))@ under branch counting. In the scalar backends a vector
-- is a list (Python) or an array (Julia), in the interpreter a rank-1
-- 'VTensor'.
--
-- How it is compiled:
--
-- * 'expandPerValue' (front end, before RType inference) gives @f@ helper
--   definitions ('SPLL.ReservedNames.perValueHelperSuffixes'). @f__point@ is
--   @f@'s own definition; @f@ itself becomes a call to it, and every other
--   function's reference to @f@ is redirected to it, so @f@ as a value is
--   unchanged and only its query interface differs. @f__slot@ is the marked
--   slot alone, whose Analysis tag gives the domain; it is never compiled.
-- * When the marked slot is bound directly to the first draw of @f@'s body
--   (after inlining an alias such as @main2 = main@), the body splits at that
--   draw into @f__prior@ (the draw's distribution) and @f__given@ (the rest,
--   with the drawn value as a parameter). That is the __fast path__: element
--   @v@ is @f__prior(v) * f__given((v, rest), v)@, and the slot is never
--   enumerated, so there is no reduction over its domain at all. Otherwise
--   the __fallback__ is one point query of @f__point@ per domain value.
-- * 'installPerValue' (after IR compilation and branch-count stripping)
--   replaces @f@'s probability function by the per-value body: a 'BMap' over
--   the domain, then one projection 'BMap' per result field.
--
-- Refused, as an absent probability variant with the reason recorded: a slot
-- with no finite domain (a continuous slot, an @Int@ the compiler cannot
-- bound), a domain over 'materializationCardinality', and @--batched@. A
-- per-value function has no integrate variant and no @writeLogits@.
module SPLL.PerValue
  ( validateSignatures
  , expandPerValue
  , PerValuePlan(..)
  , perValuePlans
  , checkSignatureTypes
  , dropSlotProbes
  , installPerValue
  , prettySlotPath
  ) where

import SPLL.Lang.Types
import SPLL.Lang.Lang (substituteVar, freeVarsExpr, autoDeriveMultiValue, multiValueIsFinite, multiValueToValueList, prettyRType)
import SPLL.Typing.RType (RType(..))
import SPLL.IntermediateRepresentation
import SPLL.ReservedNames (perValuePointSuffix, perValuePriorSuffix, perValueGivenSuffix, perValueSlotSuffix,
                           perValueHelperSuffixes, queryParamName, accProbParamName, probSuffix)
import SPLL.Semiring (Semiring(..), mkSemiring, orIR)
import SPLL.Analysis (annotateEnumsProg)

import Data.List (intercalate, nub)
import Data.Maybe (isJust, listToMaybe, mapMaybe)
import qualified Data.Set as Set

-- ---------------------------------------------------------------------------
-- Validation (on the program as written)

-- | Structural checks on the signatures: each names a definition, none is
-- duplicated, at most one slot is marked (v1), and no user definition takes a
-- per-value helper's name.
validateSignatures :: Program -> Either CompilerError ()
validateSignatures p = mapM_ check (signatures p) >> noDuplicates
  where
    defined = map fst (functions p)
    check sig
      | sigName sig `notElem` defined =
          Left ("Compiler Error: the type signature for '" ++ sigName sig ++ "' has no definition.")
      | length (sigEnumerated sig) > 1 =
          Left ("Compiler Error: the signature of '" ++ sigName sig ++ "' marks "
                ++ show (length (sigEnumerated sig)) ++ " result slots Enumerated ("
                ++ intercalate ", " (map prettySlotPath (sigEnumerated sig))
                ++ "); a per-value query over several slots (a tensor-valued result) is not supported yet. Mark one slot.")
      | otherwise = case [ h | not (null (sigEnumerated sig)), s <- perValueHelperSuffixes
                             , let h = sigName sig ++ s, h `elem` defined ] of
          (h : _) -> Left ("Compiler Error: '" ++ h ++ "' is the name of a helper the compiler derives from the per-value function '"
                           ++ sigName sig ++ "'; rename the definition.")
          [] -> Right ()
    noDuplicates = case [ n | n <- nub names, length (filter (== n) names) > 1 ] of
      (n : _) -> Left ("Compiler Error: '" ++ n ++ "' has more than one type signature.")
      [] -> Right ()
      where names = map sigName (signatures p)

-- | A slot path as an accessor chain: @fst@, @snd.fst@, or @the whole result@.
prettySlotPath :: [SigStep] -> String
prettySlotPath [] = "the whole result"
prettySlotPath steps = intercalate "." (map step steps)
  where step SigFst = "fst"
        step SigSnd = "snd"

-- ---------------------------------------------------------------------------
-- Front-end expansion

mk :: ExprF Expr -> Expr
mk = Expr makeTypeInfo

lambdaParams :: Expr -> ([String], Expr)
lambdaParams (Expr _ (Lambda n b)) = let (ns, core) = lambdaParams b in (n : ns, core)
lambdaParams e = ([], e)

wrapLambdas :: [String] -> Expr -> Expr
wrapLambdas ns body = foldr (\n b -> mk (Lambda n b)) body ns

applySpine :: Expr -> (Expr, [Expr])
applySpine (Expr _ (Apply f x)) = let (h, as) = applySpine f in (h, as ++ [x])
applySpine e = (e, [])

-- | The marked functions: name and slot path.
markedFunctions :: Program -> [(String, [SigStep])]
markedFunctions p = [ (sigName s, path) | s <- signatures p, [path] <- [sigEnumerated s] ]

-- | Give every marked function its helper definitions, make it a call to its
-- @__point@ copy, and redirect every other reference to it there (see the
-- module header). @fastPathAllowed@ is false under @topK@: the fast path
-- would multiply the prior in after the given part has already been pruned
-- against an accumulated probability that lacked it, so per-element pruning
-- would not be the point query's.
expandPerValue :: Bool -> Program -> Program
expandPerValue fastPathAllowed p0 = foldl expandOne p0 (markedFunctions p0)
  where
    expandOne p (f, path) = case (lookup f (functions p), [ sigType s | s <- signatures p, sigName s == f ]) of
      (Just binding, declared : _)
        | let (params, _) = inlineAliases p f binding, length params == length (fst (arrows declared)) ->
            expandWith p f path binding declared
      _ -> p
    expandWith p f path binding declared =
        let point = f ++ perValuePointSuffix
            (params, core) = inlineAliases p f binding
            (argTs, resultT) = arrows declared
            slotT = slotTypeAt path resultT
            -- The helpers' signatures pin what the declared type says about
            -- them, so a slot that is a parameter of the given part is the
            -- slot's type rather than a type variable, whose comparison is a
            -- run-time dispatch ('SPLL.IRCompiler.leafEqIR') rather than the
            -- slot type's own.
            helperSigs = [ FnSignature point declared []
                         , FnSignature (f ++ perValuePriorSuffix) (foldr TArrow slotT argTs) []
                         , FnSignature (f ++ perValueGivenSuffix) (foldr TArrow resultT (argTs ++ [slotT])) []
                         , FnSignature (f ++ perValueSlotSuffix) (foldr TArrow slotT argTs) [] ]
            redirect = substituteVar f (mk (Var point))
            -- f's own definition, eta-expanded to the parameters the alias
            -- inlining found: @main2 = main@ becomes @\x -> main x@. Kept as a
            -- call rather than the inlined body, so it costs one call; and not
            -- left point-free, because calling a point-free alias with an
            -- argument crashes forward chaining (see the task's follow-up).
            (ownParams, ownCore) = lambdaParams binding
            extra = drop (length ownParams) params
            pointDef = (point, redirect (wrapLambdas params
                         (foldl (\acc a -> mk (Apply acc (mk (Var a)))) (renameParams (zip ownParams params) ownCore) extra)))
            fBody = wrapLambdas params (foldl (\acc a -> mk (Apply acc (mk (Var a)))) (mk (Var point)) params)
            slotDef = (f ++ perValueSlotSuffix, wrapLambdas params (redirect (slotProbe path core)))
            fastDefs = case fastSplit path core of
              -- Defensive: a binder shadowing a parameter would give the given
              -- part two parameters of one name. The validator refuses
              -- shadowing today, so this does not arise.
              Just (s, prior, given) | fastPathAllowed, s `notElem` params ->
                [ (f ++ perValuePriorSuffix, wrapLambdas params (redirect prior))
                , (f ++ perValueGivenSuffix, wrapLambdas (params ++ [s]) (redirect given)) ]
              _ -> []
            defined = map fst ([pointDef] ++ fastDefs ++ [slotDef])
        in p { functions = [ if n == f then (f, fBody) else (n, redirect e) | (n, e) <- functions p ]
                           ++ [pointDef] ++ fastDefs ++ [slotDef]
             , signatures = signatures p ++ [ sg | sg <- helperSigs, sigName sg `elem` defined ] }

-- | A type's parameter types and its codomain.
arrows :: RType -> ([RType], RType)
arrows (TArrow a b) = let (as, r) = arrows b in (a : as, r)
arrows t = ([], t)

-- | The type at a slot path of a tuple type.
slotTypeAt :: [SigStep] -> RType -> RType
slotTypeAt [] t = t
slotTypeAt (SigFst : rest) (Tuple a _) = slotTypeAt rest a
slotTypeAt (SigSnd : rest) (Tuple _ b) = slotTypeAt rest b
slotTypeAt _ t = t

-- | Rename leading parameters (identity when the names agree, which they do:
-- alias inlining only appends parameters).
renameParams :: [(String, String)] -> Expr -> Expr
renameParams pairs e = foldr (\(old, new) acc -> if old == new then acc else substituteVar old (mk (Var new)) acc) e pairs

-- | @f@'s parameters and body, with an alias to another top-level function
-- inlined: @main2 = main@, @main2 x = main x@, @main2 = main c@. The callee's
-- missing arguments become parameters of @f@ (eta expansion), so the body
-- the fast path inspects is the callee's. Stops at anything that is not a
-- call of a known top-level function by its name, at @f@ itself, and at a
-- cycle.
inlineAliases :: Program -> String -> Expr -> ([String], Expr)
inlineAliases p f binding = go (Set.singleton f) (lambdaParams binding)
  where
    go seen (params, core) = case applySpine core of
      (Expr _ (Var g), args)
        | g `notElem` params, not (g `Set.member` seen), Just gBinding <- lookup g (functions p)
        , let (gParams, gCore) = lambdaParams gBinding
        , length args <= length gParams ->
            let taken = Set.unions (Set.fromList params : map freeVarsExpr args)
                fresh = freshNames taken (drop (length args) gParams)
                renamed = foldr (\(old, new) e -> if old == new then e else substituteVar old (mk (Var new)) e)
                                gCore (zip (drop (length args) gParams) fresh)
                body = foldr (\(y, a) e -> substituteVar y a e) renamed (zip gParams args)
            in go (Set.insert g seen) (params ++ fresh, body)
      _ -> (params, core)
    freshNames taken = snd . foldl pick (taken, [])
      where pick (t, acc) n = let n' = head [ c | c <- n : [ n ++ "_pv" ++ show i | i <- [(1 :: Int) ..] ], not (c `Set.member` t) ]
                              in (Set.insert n' t, acc ++ [n'])

-- | A @draw@ (an applied lambda): its binder, its body and its bound value.
asDraw :: Expr -> Maybe (String, Expr, Expr)
asDraw (Expr _ (Apply (Expr _ (Lambda v body)) rhs)) = Just (v, body, rhs)
asDraw _ = Nothing

asTuple :: Expr -> Maybe (Expr, Expr)
asTuple (Expr _ (InjF (Named "TCons") [a, b])) = Just (a, b)
asTuple _ = Nothing

-- | The marked slot alone, keeping the @draw@ chain it sits under: the
-- observation tree's descent through @draw@ bodies and tuple constructors,
-- with each tuple replaced by the component on the path. A body that is not
-- a tuple where the path needs one is projected with @fst@/@snd@ instead.
slotProbe :: [SigStep] -> Expr -> Expr
slotProbe [] e = e
slotProbe path@(step : rest) e
  | Just (v, body, rhs) <- asDraw e = mk (Apply (mk (Lambda v (slotProbe path body))) rhs)
  | Just (a, b) <- asTuple e = slotProbe rest (if step == SigFst then a else b)
  | otherwise = foldl (\acc s -> mk (InjF (Named (if s == SigFst then "fst" else "snd")) [acc])) e path

-- | The fast path's split: the body's first construct is @draw s = E in B@,
-- and following the slot path through @B@'s draws and tuples reaches exactly
-- @s@, not rebound on the way.
fastSplit :: [SigStep] -> Expr -> Maybe (String, Expr, Expr)
fastSplit path core = do
  (s, body, prior) <- asDraw core
  if leafIs s path body then Just (s, prior, body) else Nothing
  where
    leafIs s steps e
      | Just (v, body, _) <- asDraw e = v /= s && leafIs s steps body
      | step : rest <- steps, Just (a, b) <- asTuple e = leafIs s rest (if step == SigFst then a else b)
      | [] <- steps, Expr _ (Var v) <- e = v == s
      | otherwise = False

-- ---------------------------------------------------------------------------
-- Plans (on the RType-inferred program)

data PerValuePlan = PerValuePlan
  { pvName       :: String
  , pvParams     :: [String]
  , pvPath       :: [SigStep]
  , pvResultType :: RType          -- ^ the codomain, query-type guard of the per-value body
  , pvFast       :: Bool
  , pvDomain     :: Either String [Value]  -- ^ the slot's values in domain order, or why there are none
  }

-- | Each signature's declared type against the inferred one. A parameter or
-- result the inference left polymorphic accepts any declared type there.
checkSignatureTypes :: Program -> Either CompilerError ()
checkSignatureTypes p = mapM_ check (signatures p)
  where
    check sig = case lookup (sigName sig) (functions p) of
      Nothing -> Right ()
      Just binding ->
        let inferred = rType (ann binding)
        in if conforms (sigType sig) inferred then Right ()
           else Left ("Compiler Error: the signature of '" ++ sigName sig ++ "' declares the type "
                      ++ prettyRType (sigType sig) ++ ", but its definition has the type "
                      ++ prettyRType inferred ++ ".")
    conforms _ (TVarR _) = True
    conforms _ NotSetYet = True
    conforms NotSetYet _ = True
    conforms (TArrow a b) (TArrow c d) = conforms a c && conforms b d
    conforms (Tuple a b) (Tuple c d) = conforms a c && conforms b d
    conforms (TEither a b) (TEither c d) = conforms a c && conforms b d
    conforms (ListOf a) (ListOf b) = conforms a b
    conforms a b = a == b

-- | One plan per marked function: its parameters, whether the fast path
-- helpers exist, and the marked slot's domain, read off @f__slot@'s Analysis
-- tag (the source that knows a numeric domain, such as a neural read's
-- @of [...]@ list) or else derived from the slot's type, exactly as a
-- function's own 'sampleDomain' is.
perValuePlans :: CompilerConfig -> Program -> [PerValuePlan]
perValuePlans conf rtyped = mapMaybe plan (signatures rtyped)
  where
    tagged = annotateEnumsProg rtyped
    plan sig = do
      [path] <- Just (sigEnumerated sig)
      let f = sigName sig
      binding <- lookup f (functions rtyped)
      let (params, _) = lambdaParams binding
          resultT = snd (arrows (sigType sig))
          slotT = slotTypeAt path resultT
          fast = isJust (lookup (f ++ perValueGivenSuffix) (functions rtyped))
          what = "the Enumerated slot " ++ prettySlotPath path ++ " of '" ++ f ++ "' (" ++ prettyRType slotT ++ ")"
          domain
            | batched conf = Left ("per-value queries are not supported under --batched yet; "
                                   ++ "compile without it to query " ++ what)
            | otherwise = case lookup (f ++ perValueSlotSuffix) (functions tagged) of
                Nothing -> Left ("the definition of '" ++ f ++ "' does not take every argument its signature declares as a parameter; "
                                 ++ "a per-value function needs them all, e.g. '" ++ f ++ " x = ...' or an alias '" ++ f ++ " = g'")
                Just probe -> case finiteDomain probe slotT of
                  Nothing
                    | slotT == TFloat -> Left (what ++ " is continuous; a per-value query needs a finite discrete domain to enumerate")
                    | otherwise -> Left (what ++ " has no finite domain the compiler can derive; an unbounded slot "
                                         ++ "needs to be bound to an enumerable draw (for example a neural read with an 'of [...]' list)")
                  Just vals
                    | length vals > materializationCardinality conf ->
                        Left (what ++ " has " ++ show (length vals) ++ " values, over the materialization budget of "
                              ++ show (materializationCardinality conf) ++ " (--materializationBudget)")
                    | otherwise -> Right vals
      return (PerValuePlan f params path resultT fast domain)
    finiteDomain probe slotT = fmap multiValueToValueList $ listToMaybe $ filter multiValueIsFinite $
      [ mv | DiscreteValues mv <- tags (ann (snd (lambdaParams probe))) ]
      ++ [ mv | Right mv <- [autoDeriveMultiValue (adts rtyped) slotT] ]

-- | The program without the @f__slot@ domain probes, which are read for their
-- tags only and must not be compiled.
dropSlotProbes :: Program -> Program
dropSlotProbes p = p { functions = [ d | d@(n, _) <- functions p, n `notElem` probes ] }
  where probes = [ sigName s ++ perValueSlotSuffix | s <- signatures p ]

-- ---------------------------------------------------------------------------
-- Installation (on the compiled, branch-count-stripped IR)

-- | Replace each planned function's probability function with its per-value
-- body (see the module header for the layout), and drop the variants a
-- per-value function has no meaning for.
installPerValue :: CompilerConfig -> [PerValuePlan] -> IREnv -> IREnv
installPerValue conf plans (IREnv groups decls consts) = IREnv (map install groups) decls consts
  where
    install g = case [ pl | pl <- plans, pvName pl == groupName g ] of
      (pl : _) -> perValueGroup pl g
      [] -> g

    groupNamed n = listToMaybe [ g | g <- groups, groupName g == n ]

    perValueGroup pl g =
      let f = pvName pl
          helpers = if pvFast pl then [f ++ perValuePriorSuffix, f ++ perValueGivenSuffix] else [f ++ perValuePointSuffix]
          missing = [ (h, why h) | h <- helpers, maybe True (not . isJust . probFun) (groupNamed h) ]
          why h = case groupNamed h >>= lookup "prob" . refusedVariants of
            Just r -> showRefusal r
            Nothing -> "its probability is intractable"
          integRefusal = VariantRefusal ("'" ++ f ++ "' answers per-value queries and has no integrate function; query '"
                                         ++ f ++ perValuePointSuffix ++ "' for the ordinary CDF") ""
          base = g { integFun = Nothing
                   , writeLogitsFun = Nothing
                   , refusedVariants = [ r | r@(lbl, _) <- refusedVariants g, lbl `notElem` ["prob", "integ"] ]
                                       ++ [("integ", integRefusal)] }
          refused reason = base { probFun = Nothing
                                , refusedVariants = refusedVariants base ++ [("prob", VariantRefusal reason "")]
                                , groupDoc = groupDoc g ++ "\nPer-value query over " ++ prettySlotPath (pvPath pl) ++ ": refused" }
      in case (pvDomain pl, missing) of
        (Left reason, _) -> refused reason
        (Right _, (h, r) : _) -> refused ("the per-value query of '" ++ f ++ "' is built from '" ++ h ++ "', which was not compiled: " ++ r)
        (Right vals, []) ->
          base { probFun = Just (perValueBody conf pl vals, perValueDoc pl vals)
               , groupDoc = groupDoc g ++ "\nPer-value query over " ++ prettySlotPath (pvPath pl) ++ " of the result ("
                            ++ show (length vals) ++ " values, " ++ (if pvFast pl then "fast path" else "one point query per value") ++ ")" }

perValueDoc :: PerValuePlan -> [Value] -> String
perValueDoc pl vals =
  "Per-value query: for every value v of the Enumerated slot " ++ prettySlotPath (pvPath pl)
  ++ " (" ++ show (length vals) ++ " values), the probability of the sample with that slot set to v. "
  ++ "The sample's own value at that slot is ignored. Returns (probs, (dims, ("
  ++ "imposs, values))) -- with branch counts before imposs under --countBranches -- each a vector in domain order."

perValueBody :: CompilerConfig -> PerValuePlan -> [Value] -> IRExpr
perValueBody conf pl vals =
  IRLambda queryParamName (accLambda (foldr IRLambda guarded (pvParams pl)))
  where
    f = pvName pl
    topK = isJust (topKThreshold conf)
    accLambda = if topK then IRLambda accProbParamName else id
    accArg = [ IRVar accProbParamName | topK ]
    params = map IRVar (pvParams pl)
    sample = IRVar queryParamName
    guarded
      | checkQueryType conf =
          IRIf (IRConformsTo (pvResultType pl) sample) core
               (IRError ("p(" ++ f ++ "): query value does not conform to return type " ++ show (pvResultType pl)))
      | otherwise = core

    domName = "l_pv_domain"
    resName = "l_pv_results"
    valName = "l_pv_value"
    elemName = "l_pv_r"
    domTensor = IRBuiltin (BTensor [EFixed (length vals)]) (map (IRConst . valueToIR) vals)
    value = IRVar valName

    core = IRLetIn domName domTensor
             (IRLetIn resName (IRBuiltin BMap [IRLambda valName element, IRVar domName])
               (foldr (\proj acc -> IRConstruct TgTuple [fieldVector proj, acc]) (IRVar domName) fields))
    fieldVector proj = IRBuiltin BMap [IRLambda elemName (proj (IRVar elemName)), IRVar resName]

    -- The result fields as the point query packs them, branch counts having
    -- been stripped unless --countBranches kept them.
    fields
      | countBranches conf = [fstIR, fstIR . sndIR, fstIR . sndIR . sndIR, sndIR . sndIR . sndIR]
      | otherwise = [fstIR, fstIR . sndIR, sndIR . sndIR]
    fstIR = IRDestruct AcFst
    sndIR = IRDestruct AcSnd

    call name args = foldl IRApply (IRVar (name ++ probSuffix)) args
    pointed = withSlot (pvPath pl) sample

    element
      | pvFast pl =
          let a = IRVar "l_pv_prior"
              b = IRVar "l_pv_given"
          in IRLetIn "l_pv_prior" (call (f ++ perValuePriorSuffix) (value : params))
               (IRLetIn "l_pv_given" (call (f ++ perValueGivenSuffix) (pointed : params ++ [value]))
                 (product2 a b))
      | otherwise = call (f ++ perValuePointSuffix) (pointed : accArg ++ params)

    -- The product of two independent results, field by field as 'prodP' does.
    sr = mkSemiring SRSumProduct (logSpace conf)
    product2 a b
      | countBranches conf =
          IRConstruct TgTuple [ srTimes sr (fstIR a) (fstIR b)
                              , IRConstruct TgTuple [ IROp OpPlus (fstIR (sndIR a)) (fstIR (sndIR b))
                                                    , IRConstruct TgTuple [ IROp OpPlus (fstIR (sndIR (sndIR a))) (fstIR (sndIR (sndIR b)))
                                                                          , orIR (sndIR (sndIR (sndIR a))) (sndIR (sndIR (sndIR b))) ] ] ]
      | otherwise =
          IRConstruct TgTuple [ srTimes sr (fstIR a) (fstIR b)
                              , IRConstruct TgTuple [ IROp OpPlus (fstIR (sndIR a)) (fstIR (sndIR b))
                                                    , orIR (sndIR (sndIR a)) (sndIR (sndIR b)) ] ]

    -- The query with the marked slot set to the loop value. Every other slot
    -- is the query's own; a query that is ANY at a tuple above the slot is ANY
    -- at each of that tuple's other components.
    withSlot [] _ = value
    withSlot (step : rest) x =
      IRIf (IRUnaryOp OpIsAny x) (anyWith (step : rest))
        (case step of
           SigFst -> IRConstruct TgTuple [withSlot rest (fstIR x), sndIR x]
           SigSnd -> IRConstruct TgTuple [fstIR x, withSlot rest (sndIR x)])
    anyWith [] = value
    anyWith (SigFst : rest) = IRConstruct TgTuple [anyWith rest, IRConst VAny]
    anyWith (SigSnd : rest) = IRConstruct TgTuple [IRConst VAny, anyWith rest]
