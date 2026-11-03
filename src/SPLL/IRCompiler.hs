module SPLL.IRCompiler (
  envToIRUnoptimized,
  generateBackedSites,
  requireNoGenerateBacked,
  stripBranchCount,
  toIRNormal,
  sharesEnumeratedLatent,
  latentDependencies,
  injFLatentVerdicts,
  materializationVerdicts,
  isCandidateBinaryEnumInjF,
  -- white-box: the plan factorization's independence guard (see its haddock)
  planFactorExternals,
  -- white-box: the dense-enumeration budget gate's count (see its haddock)
  enumeratedCount,
  -- the cdf() diagnostic for a Symbol-valued node (see 'compareValueExpr')
  symbolCdfMessage
)where
import SPLL.ReservedNames (queryParamName, accProbParamName, topKCutoffName, topKCutoffParamName, accProbInitName, componentNormalGroupPrefix, componentNormalName)
import SPLL.IntermediateRepresentation
import SPLL.CompilerConfig
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.IROptimizer
import PrettyPrint (pPrintValue)
import SPLL.Analysis (latentDependencies, sharesEnumeratedLatent, isCandidateBinaryEnumInjF, injFLatentVerdicts, materializationVerdicts, materializationScopes, getValuesFromExpr, enumerableDomain)
import SPLL.Typing.PType
import Data.Maybe
import Data.List (isPrefixOf, isSuffixOf, stripPrefix, nub, intercalate)
import SPLL.AutoNeural hiding (planReadOf, planProjectedReadOf)
import SPLL.Typing.ForwardChaining
import SPLL.Typing.Determinism (functionSummaries)
import SPLL.Typing.ModalityInfer (reinferCtx, LawTable)
import Control.Applicative ((<|>))
import qualified SPLL.Typing.ModalityInfer as ModalityInfer
import SPLL.Typing.AlgebraicDataTypes
import SPLL.IRTypeBridge (irConformanceType)
import SPLL.Semiring
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Graph (SCC(..), stronglyConnComp)
import SPLL.IRCompiler.Monad
import SPLL.IRCompiler.Materialize
import SPLL.IRCompiler.Gaussian
import SPLL.IRCompiler.Worlds
import SPLL.IRCompiler.Plan
import SPLL.IRCompiler.Enumerate
import SPLL.IRCompiler.Inference (knot)

-- The FCData certificate is built once in 'Prelude.compile' and threaded in,
-- rather than rebuilt here (modality-split-forwardchaining).
--
-- Wraps the actual compilation ('envToIRUnoptimized'') with the central
-- generate-backed-inference guard (task central-generate-backed-prob-body-guard):
-- every probability/integrate/normal/writeLogits body this stage produces is
-- required to be free of randomness before it can reach the optimizer or any
-- backend. This is the single point where 'genFun'/'probFun'/'integFun'/
-- 'normalFun'/'writeLogitsFun' are assembled, so the check sees every site
-- regardless of which combinator produced it and needs no per-site edits.
envToIRUnoptimized :: CompilerConfig -> FCData -> LawTable -> Program -> Either CompilerError IREnv
envToIRUnoptimized conf fcDat laws p = requireNoGenerateBacked conf (propagateRefusals (envToIRUnoptimized' conf fcDat laws p))

-- | Refuse every compiled variant that calls a refused one, to a fixed point
-- (task static-refusals-become-absent-variants). A refused variant is absent,
-- so a caller that still referenced it -- @main_prob@ calling @f_prob@ -- would
-- emit a call to a function that is never written. The caller is refused too,
-- naming the callee and the callee's own reason; the shape mirrors
-- 'requireNoGenerateBacked''s treatment of a @--noGenerate@-suppressed
-- generator, except that the unit refused is the one variant, not the compile.
--
-- Only /refused/ variants propagate. A variant absent because its pType is
-- intractable is never referenced by a compiled caller (the caller would be
-- intractable too), and a --noX flag's absences are the generate-backed
-- guard's business.
propagateRefusals :: IREnv -> IREnv
propagateRefusals (IREnv groups0 adts' consts) = IREnv (go groups0) adts' consts
  where
    go gs =
      let refused = Map.fromList [ (variantRefName g lbl, (lbl, groupName g, r))
                                 | g <- gs, (lbl, r) <- refusedVariants g ]
          gs' = map (dropDangling refused) gs
      in if sum (map (length . refusedVariants) gs') == sum (map (length . refusedVariants) gs)
           then gs else go gs'
    dropDangling refused g = foldl (dropOne refused) g variantLabels
    dropOne refused g lbl = case variantOf lbl g of
      Just (vBody, _)
        | (callee, (calleeLbl, calleeGroup, r)) : _ <-
            [ (n, hit) | n <- nub (irVarNames vBody), Just hit <- [Map.lookup n refused] ] ->
            let why = "this " ++ variantWord lbl ++ " function calls " ++ callee ++ ", the "
                      ++ variantWord calleeLbl ++ " function of '" ++ calleeGroup
                      ++ "', which NeST refused to compile:\n" ++ showRefusal r
            in (clearVariant lbl g) { refusedVariants = refusedVariants g ++ [(lbl, VariantRefusal why "")] }
      _ -> g
    variantLabels = ["gen", "prob", "integ", "normal", "writeLogits"]
    variantOf lbl g = case lbl of
      "gen" -> genFun g
      "prob" -> probFun g
      "integ" -> integFun g
      "normal" -> normalFun g
      _ -> writeLogitsFun g
    clearVariant lbl g = case lbl of
      "gen" -> g { genFun = Nothing }
      "prob" -> g { probFun = Nothing }
      "integ" -> g { integFun = Nothing }
      "normal" -> g { normalFun = Nothing }
      _ -> g { writeLogitsFun = Nothing }
    variantWord lbl = case lbl of
      "gen" -> "generate"
      "prob" -> "probability"
      "integ" -> "integrate"
      other -> other
    -- The name the IR references a group's variant by (cf. the backends'
    -- lookup tables and 'IRInterpreter.reduceIREnv').
    variantRefName g lbl = case lbl of
      "normal" -> fromMaybe (groupName g ++ "_normal") (componentNormalName (groupName g))
      "gen" -> groupName g ++ "_gen"
      "prob" -> groupName g ++ "_prob"
      "integ" -> groupName g ++ "_integ"
      _ -> groupName g ++ "_writeLogits"
    -- Accumulator-passing, for the reason 'firstAnyExceptIR' gives.
    irVarNames e0 = walk e0 []
      where
        walk e rest = case e of
          IRVar n -> n : rest
          _ -> foldr walk rest (getIRSubExprs e)

-- | Refuse at compile time rather than hand back an 'IREnv' containing a
-- generate-backed probability/integrate/normal/writeLogits body -- see
-- 'generateBackedSites' for what that means and why a syntactic test would be
-- wrong. This converts every present and future generate-backed inference
-- path (a compiled body that resamples instead of computing an exact
-- probability, so it returns a different number on every call with the same
-- query) from a silent wrong answer into a named refusal.
--
-- Task @nogenerate-dangling-cross-function-generate-call@: under
-- @--noGenerate@, every 'IRFunGroup''s 'genFun' is 'Nothing' regardless of
-- whether that function's own generate body would have been pure, so a
-- reference to another (or the same) function's now-absent @<name>_gen@ is
-- conservatively flagged the same as genuine randomness by
-- 'generateBackedSites' -- correctly refused, but with a message
-- ("draws randomness") that is misleading when the callee is actually
-- deterministic and the only real defect is that the user asked for it not
-- to be emitted. When every randomness source the refusal names is exactly
-- such a suppressed-by-the-flag reference, name the flag as the cause
-- instead of the generic message: the reviewed resolution is that
-- @--noGenerate@ promising "no generate code at all" and a query that
-- structurally depends on another function's generator are incompatible,
-- and NeST says so rather than emitting a call to a method it agreed not to
-- write.
--
-- The refusal is a 'Left' rather than an 'error': it is a verdict on the user's
-- program, and 'Prelude.compile' already reports program-level verdicts through
-- 'CompilerError'. Throwing made an established, correct refusal
-- indistinguishable from a compiler crash -- which is exactly what
-- 'prop_Fuzz_TypedCompileNeverCrashes' is there to tell apart
-- (task compiler-throws-instead-of-returning-left). Whether the guard should
-- fire at all on a given draw is a separate question, owned by
-- 'fuzz-structured-type-bugs'; this only changes how an already-decided refusal
-- travels.
requireNoGenerateBacked :: CompilerConfig -> IREnv -> Either CompilerError IREnv
requireNoGenerateBacked conf env@(IREnv groups _ _) = case generateBackedSites env of
  [] -> Right env
  bad
    | noGenerate conf, not (null suppressedFns) -> Left $ unlines $
      [ "envToIRUnoptimized: --noGenerate suppressed the generate function(s) of "
        ++ intercalate ", " (Set.toList suppressedFns) ++ ", but the following compiled"
      , "probability/integrate/normal/writeLogits body/bodies still need to call into"
      , "them (each with the call site name(s) it reaches):" ]
      ++ [ "  " ++ nm ++ ": " ++ intercalate ", " ws | (nm, ws) <- bad ]
      ++ [ "NeST will not silently emit a call to a generate function you asked it not"
         , "to compile, nor drop the call and emit code that fails at run time instead."
         , "--noGenerate and this query are incompatible: drop --noGenerate, or restructure"
         , "the program so this query does not depend on another function's generator."
         , "(task nogenerate-dangling-cross-function-generate-call)" ]
    | otherwise -> Left $ unlines $
      [ "envToIRUnoptimized: a compiled probability/integrate/normal/writeLogits body draws"
      , "randomness instead of computing an exact probability, so it would return a"
      , "different number on every call with the same query value. NeST does exact"
      , "inference, so this is refused at compile time rather than emitted. Offending"
      , "function(s), each with the randomness source(s) it reaches:" ]
      ++ [ "  " ++ nm ++ ": " ++ intercalate ", " ws | (nm, ws) <- bad ]
      ++ [ "(task central-generate-backed-prob-body-guard)" ]
    where
      groupsByName = Map.fromList [(groupName g, g) | g <- groups]
      -- A randomness-source string is exactly "from <dist>" (a real
      -- 'IRSample') or "by calling <name>" ('randomDrawSites'). Only the
      -- latter can ever be a suppressed generator; a bare 'IRSample' is
      -- randomness --noGenerate had nothing to do with.
      dropGenSuffix n
        | "_gen" `isSuffixOf` n = Just (take (length n - length "_gen") n)
        | otherwise = Nothing
      suppressedCallee w = do
        n <- stripPrefix "by calling " w
        base <- dropGenSuffix n
        g <- Map.lookup base groupsByName
        if isNothing (genFun g) then Just base else Nothing
      -- Attribute the whole refusal to --noGenerate only when *every*
      -- randomness source of *every* offending function is such a
      -- suppressed reference -- a genuine 'IRSample' anywhere falls back to
      -- the generic message rather than mislabeling real randomness as a
      -- flag artifact.
      suppressedFns
        | all (all (isJust . suppressedCallee) . snd) bad =
            Set.fromList [ base | (_, ws) <- bad, w <- ws, Just base <- [suppressedCallee w] ]
        | otherwise = Set.empty

-- | Every "<group>.<prob|integ|normal|writeLogits>" site in the whole 'IREnv' whose
-- compiled body is generate-backed -- i.e. not provably free of randomness --
-- paired with the randomness source(s) 'randomDrawSites' finds in it.
--
-- The oracle has to be transitive purity, not a syntactic "mentions a @_gen@
-- 'IRVar'" test: a pure higher-order helper can carry a @_gen@ reference in
-- its plumbing without the *caller* drawing randomness. `testCases/hoTopLevel.ppl`
-- (@f g = g 1.0@, @main = f (\\x -> Uniform + x)@) compiles @main.forward@ to
-- @f_gen(\<the density continuation\>)@: @f_gen@'s own body is pure (it never
-- itself samples), so a syntactic test naming every @_gen@ mention would flag
-- this false positive where a purity oracle does not.
--
-- 'deterministicGens' already computes exactly that oracle, as a whole-program
-- fixed point over 'genFun' bodies via 'isPureGiven' -- purely from the
-- compiled IR, needing no separate determinism pass over the source
-- ('CompilerMetadata.detGenNames', built from 'Typing.Determinism', is too
-- coarse for this central check: see 'requireDeterministicUnderEnum', whose
-- narrower local guard it correctly serves). A generator this pass never saw
-- a body for (e.g. under @--noGenerate@) is never a candidate, so any
-- reference to it is conservatively random; self- and mutual recursion is
-- handled because the fixed point is global, not a per-site descent.
-- 'randomDrawSites', reused unmodified from the local enumeration guard, then
-- names the actual sources against that same oracle.
generateBackedSites :: IREnv -> [(String, [String])]
generateBackedSites (IREnv groups _ _) =
  [ (nm, ws) | (nm, ws) <- concatMap chk groups, not (null ws) ]
  where
    det = deterministicGens groups
    -- A writeLogits body's dead-arm fill is deliberate noise, not a generate-backed slot
    -- (task writelogits-dead-arm-nan): it is stripped before the check, so every live slot
    -- must still be exact.
    chk g =
      [ (groupName g ++ "." ++ lbl, nub (randomDrawSites det b))
      | (lbl, Just (b, _)) <- [ ("prob", probFun g), ("integ", integFun g)
                              , ("normal", normalFun g)
                              , ("writeLogits", (\(b, ps) -> (stripDeadSlotFills b, ps)) <$> writeLogitsFun g) ]
      ]

envToIRUnoptimized' :: CompilerConfig -> FCData -> LawTable -> Program -> IREnv
envToIRUnoptimized' conf@CompilerConfig{noIntegrate=noInteg, noProbability=noProb, noGenerate=noGen} fcDat laws p@Program{adts=progADTs} = IREnv (
  map (makeAutoNeural progADTs conf (writeLogitsDecls p)) (neurals p) ++
  concatMap (\(name, binding) ->
    let progTypeEnv = getGlobalTypeEnv p
        bindingParamNames = extractParamNames binding
        pt = pType $ getTypeInfo binding
        ptUnderLambdas = pType $ getTypeInfo $ stripLambdas binding
        -- Every logit-representable top-level function gets its own writeLogitsFun, keyed to its
        -- own <name>_prob / <name>_normal functions, with no neural declaration required
        -- (task encode-per-function-endpoints; `main` is just the name == "main" case).
        -- Lazily references baseFunGroup/tupleNormalFuns to read whether this function's
        -- prob/normal functions were generated; non-representable functions keep
        -- writeLogitsFun = Nothing (purely additive, no new error surface).
        writeLogitsF =
              makeTopLevelWriteLogitsFun progADTs conf (writeLogitsDecls p)
                name
                (rType (getTypeInfo (stripLambdas binding)))
                (getValuesFromExpr (stripLambdas binding))
                bindingParamNames
                (isJust (probFun baseFunGroup))
                (baseFunGroup : tupleNormalFuns)
                nonGaussianNormals
        -- The type the query value must structurally match: the function's result
        -- type with any outer parameter lambdas stripped. Backs the query-type guard.
        returnRType = rType (getTypeInfo (stripLambdas binding))
        -- Wrap a value-returning inference body so a wrong-typed query value fails
        -- with a clear diagnostic (see IRConformsTo) instead of a silent bogus
        -- number or a deep "not a boolean" panic. `sample` is already bound by the
        -- enclosing IRLambda. Gated on checkQueryType (default on, independent of -O).
        -- Pushed under any outer parameter lambdas (via guardUnderLambdas) so those
        -- stay at the function head where codegen collects them into the signature.
        guardQuery kind = guardUnderLambdas
          where
            guardUnderLambdas (IRLambda n b) = IRLambda n (guardUnderLambdas b)
            guardUnderLambdas bodyExpr
              | checkQueryType conf =
                  IRIf (IRConformsTo (irConformanceType returnRType) (IRVar queryParamName))
                       bodyExpr
                       (IRError (kind ++ "(" ++ name ++ "): query value does not conform to return type " ++ show returnRType))
              | otherwise = bodyExpr
        -- Appended to the guarded function's doc (emitted as a comment by codegen)
        -- so the generated code points at the flag that produced the check.
        guardNote = if checkQueryType conf
                    then "\nQuery-type guard active: rejects a query value not matching return type " ++ show returnRType ++ " (disable with --noTypeCheck)."
                    else ""
        appendDoc note (e, d) = (e, d ++ note)
        -- Design heterogeneous-batch-inference M3: the finite enumeration of
        -- query values, when this function has one. Analysis's DiscreteValues
        -- tag is preferred, being the only source that knows a *numeric* finite
        -- domain (`coin`'s [0,1,2], `discreteFloats`' [2.0,3.0,4.0]); the return
        -- type is the fallback for the structurally finite types Analysis has no
        -- reason to tag (Bool, enum ADTs, tuples/Eithers thereof). A domain that
        -- is not wholly finite ('multiValueIsFinite') is no domain at all -- see
        -- there for why a partial enumeration would be worse than none.
        --
        -- This is the domain of the function's own *result*, i.e. of a query
        -- against it; the domains it enumerates internally are tensor reductions,
        -- a separate axis this deliberately does not touch.
        sampleDom = listToMaybe $ filter multiValueIsFinite $
          maybeToList (enumerableDomain (tags (getTypeInfo (stripLambdas binding))))
          ++ [mv | Right mv <- [autoDeriveMultiValue progADTs returnRType]]
        -- Each variant is attempted ('Just') or not ('Nothing': intractable by
        -- its pType, or suppressed by a --noX flag); an attempt answers 'Left'
        -- when the compiler refuses the shape (see 'refuse'). A refused variant
        -- is absent exactly like an intractable one, and its reason is kept in
        -- 'refusedVariants' (task static-refusals-become-absent-variants).
        integE =
          if not noInteg && admittedPT pt then
            Just (appendDoc guardNote . toIntegDecl name . IRLambda queryParamName . cutoffLambda . guardQuery "cdf"
                    <$> runCompile (meta progTypeEnv) (toIRInferenceSave (meta progTypeEnv) True binding (IRVar queryParamName)))
          else Nothing
        probE =
            if not noProb && admittedPT pt then
              let metaBase = meta progTypeEnv
                  compileBody m = runCompile m (toIRInferenceSave m False binding (IRVar queryParamName))
              in Just (appendDoc guardNote . toProbDecl name <$> case topKThreshold conf of
                   Just _ -> IRLambda queryParamName . IRLambda accProbParamName . cutoffLambda . guardQuery "p" <$> compileBody (metaBase { accProb = IRVar accProbParamName })
                   Nothing -> IRLambda queryParamName . guardQuery "p" <$> compileBody metaBase)
            else Nothing
        genE =
            if not noGen then
              Just (toGenDecl name . cutoffBinding . openValue <$> runCompilerMonad (toIRGenerate (meta progTypeEnv) binding))
            else
              Nothing
        normalE =
            -- The modality read under the parameter lambdas, not on the binding
            -- itself: a curried function's outer Lambda is Deterministic (its
            -- result is a closure), so `pt` only reports PNormal for a
            -- zero-or-one-argument function. compileNormalExpr strips the
            -- lambdas anyway, and a two-argument helper is exactly as much a
            -- Normal shortcut as a one-argument one
            -- (task normal-shortcut-crashes-through-function-call).
            if (ptUnderLambdas == PNormal || ptUnderLambdas == PLogNormal) && isNormalExtractable binding then
              Just (toNormalDecl name . cutoffBinding <$> compileNormalExpr (meta progTypeEnv) binding)
            else
              Nothing
        baseFunGroup = IRFunGroup {groupName=name, writeLogitsFun=writeLogitsF, sampleDomain=fmap multiValueToIR sampleDom, maskVariantOf=Nothing,
          integFun = presentVariant integE,
          probFun = presentVariant probE,
          genFun = presentVariant genE,
          normalFun = presentVariant normalE,
          refusedVariants = refusedVariant "gen" genE ++ refusedVariant "prob" probE
                            ++ refusedVariant "integ" integE ++ refusedVariant "normal" normalE
                            ++ intractableRefusal "prob" noProb ++ intractableRefusal "integ" noInteg
                            ++ [ ("writeLogits", VariantRefusal
                                    "writeLogits: the output has a log-normal Float slot, which the Gaussian (mu, sigma) layout cannot hold (it would label the underlying Normal's parameters as the output's own)" "")
                               | isNothing writeLogitsF, not (null nonGaussianNormals) ],
          groupDoc="Function group " ++ name}
        -- A variant absent because its pType is intractable is otherwise absent
        -- without a reason. When the intractability starts at a comparison
        -- with no closed form for its operands, say so (task
        -- uniform-below-random-threshold-no-forward: @draw x = Uniform in
        -- (x < 0.5, Uniform < x)@ compiled with exit 0 and no word on why
        -- the probability function was missing), and likewise at a binding no
        -- inference engine applies to (task engine-applicability-as-data).
        -- Any other intractable root names the node its 'Bottom' starts at
        -- ('bottomOrigin', task bottom-verdict-records-no-refusal-reason).
        intractableRefusal lbl suppressed
          | suppressed || admittedPT pt = []
          | otherwise = [ (lbl, VariantRefusal why cn)
                        | Just (why, cn) <- [comparisonWithoutClosedForm binding <|> bindingWithoutEngine laws binding <|> bottomOrigin binding] ]
        -- Generate per-component normal functions for tuple outputs
        tupleNormalGroups = generateTupleComponentNormalFunctions (meta progTypeEnv) name binding
        tupleNormalFuns = map fst tupleNormalGroups
        -- Normal functions whose (mu, sigma) are those of an underlying Normal (a log-normal's
        -- (mu_log, sigma)), not of the output itself: writeLogits' Gaussian slots must not read
        -- them (task writelogits-labels-lognormal-as-gaussian).
        nonGaussianNormals =
          [ name ++ "_normal" | ptUnderLambdas == PLogNormal ]
          ++ [ fromMaybe (groupName g) (componentNormalName (groupName g)) | (g, False) <- tupleNormalGroups ]
        -- One extra 'IRFunGroup' per 'extraSemirings' entry (task
        -- semiring-parametric-marginals, design materialized-marginals-semiring
        -- Tier 1): "<name>_<suffix>" (e.g. "main_map"), with ONLY 'probFun'
        -- populated, compiled by the exact same 'toIRInferenceSave' call as
        -- 'baseFunGroup's own 'probFun' -- the sole difference is 'metaBase'
        -- carrying the requested 'semiringFamily' instead of 'SRSumProduct', so
        -- 'semiringOf' (and every one of 'prodP'/'mixP'/'enumSumP'/the leaf
        -- combinators built on it) picks the alternate 'Semiring' with no
        -- change to the recursive compilation code itself. A distinct group,
        -- not a field on 'baseFunGroup', because every downstream generic pass
        -- (tensor lowering, select pass, the optimizer, the generate-backed
        -- guard, branch-count stripping, and every backend's codegen) already
        -- maps over 'IREnv's group list uniformly, so this needs no changes
        -- there at all -- and it is what lets several semirings land in the
        -- same output file as ordinary named entry points, per the task's
        -- acceptance criteria, rather than a whole-artifact mode switch.
        --
        -- Scope cuts, both documented on 'extraSemirings' itself: no
        -- 'integFun'/'genFun'/'normalFun'/'writeLogitsFun' (CDF and generation have
        -- no settled meaning under max-product), and no topK interaction (the
        -- 'acc_prob' extra parameter/'TOP_K_CUTOFF' plumbing 'baseFunGroup's
        -- own 'probFun' has under 'topKThreshold' is not replicated here).
        extraFunGroups =
          [ IRFunGroup { groupName = name ++ "_" ++ semiringSuffix fam, writeLogitsFun = Nothing, sampleDomain = Nothing, maskVariantOf = Nothing
                        , integFun = Nothing
                        , probFun = presentVariant extraProbE
                        , refusedVariants = refusedVariant "prob" extraProbE
                        , genFun = Nothing
                        , normalFun = Nothing
                        , groupDoc = "Function group " ++ name ++ " under the " ++ show fam ++ " semiring" }
          | fam <- extraSemirings conf
          , let extraProbE =
                  if not noProb && admittedPT pt then
                    let metaExtra = (meta progTypeEnv) { semiringFamily = fam }
                        compileBody m = runCompile m (toIRInferenceSave m False binding (IRVar queryParamName))
                    in Just (appendDoc guardNote . toProbDecl name . IRLambda queryParamName . guardQuery "p" <$> compileBody metaExtra)
                  else Nothing ]
    in [baseFunGroup] ++ tupleNormalFuns ++ extraFunGroups) (functions p))
  (map irADTDecl progADTs)
  -- The cutoff must live in the same space as the accumulated probability it's
  -- compared against: under logSpace that's log(thresh), not the raw linear
  -- threshold. The comparison operators themselves (OpLessThan/OpGreaterThan)
  -- stay unchanged either way -- log is a monotone increasing transform, so
  -- ordering against the cutoff is preserved without touching the comparisons.
  -- TOP_K_CUTOFF is only the default for the runtime 'topKCutoffParamName'
  -- parameter; nothing in the compiled functions reads it, so a caller may pass
  -- any other cutoff (in the same space) without recompiling.
  -- ACC_PROB_INIT mirrors TOP_K_CUTOFF's marker-const idiom: the value a
  -- caller must seed the extra acc_prob parameter with at the query root
  -- (linear 1.0, or log-space 0.0). Both are read back by 'SPLL.Prelude.runProbNamedC'.
  (case topKThreshold conf of
    Just thresh -> [(topKCutoffName, VFloat (if logSpace conf then log thresh else thresh)),
                     (accProbInitName, VFloat (if logSpace conf then 0.0 else 1.0))]
    Nothing     -> [])

  where
    -- Under topK every probability and integrate function takes the cutoff as
    -- a runtime parameter, so one compile answers any threshold (task
    -- runtime-parametric-topk-threshold); the TOP_K_CUTOFF const above is only
    -- the default a caller passes.
    cutoffLambda = if isJust (topKThreshold conf) then IRLambda topKCutoffParamName else id
    -- A generate or normal body has no cutoff parameter, yet it can call a
    -- probability function: a 'collapse' operand's mixture weighs its arms by
    -- its condition's probability, and the condition may be a call. That call
    -- is compiled 'unpruned' (accumulated probability infinite), so no arm is
    -- cut whatever the cutoff; the body binds the parameter's name to the
    -- default so the call's argument is in scope.
    cutoffBinding = if isJust (topKThreshold conf) then underParams else id
    underParams (IRLambda n b) = IRLambda n (underParams b)
    underParams b
      | readsCutoff b = IRLetIn topKCutoffParamName (IRVar topKCutoffName) b
      | otherwise = b
    readsCutoff (IRVar n) = n == topKCutoffParamName
    readsCutoff e = any readsCutoff (getIRSubExprs e)
    -- The four rungs a probability and an integrate function are compiled for.
    admittedPT pt' = pt' == Deterministic || pt' == Integrate || pt' == PNormal || pt' == PLogNormal
    presentVariant :: Maybe (Either VariantRefusal IRFunDecl) -> Maybe IRFunDecl
    presentVariant e = e >>= either (const Nothing) Just
    refusedVariant :: String -> Maybe (Either VariantRefusal IRFunDecl) -> [(String, VariantRefusal)]
    refusedVariant lbl e = [ (lbl, r) | Just (Left r) <- [e] ]
    toGenDecl name expr = (expr, "Generates a random sample of the " ++ name ++ " function")
    toProbDecl name expr =
      (expr, "Calculates the probability of the sample parameter being returned from the " ++ name ++ "function")
    toIntegDecl name expr = (expr, "Calculates the probability of the sample parameter being less than or equal to the " ++ name ++ " function")
    toNormalDecl name expr = (expr, "Returns (mu, sigma) normal distribution parameters for the " ++ name ++ " function")
    -- accProb starts at the semiring's multiplicative identity: linear 1.0, or
    -- log-space 0.0 (log 1). Hardcoding VFloat 1.0 here silently discarded all
    -- probability mass under logSpace, since every branch's accumulated weight
    -- was then a linear 1.0 multiplied against log (negative) per-branch terms
    -- (task topk-logspace-unsound).
    meta te = CompilerMetadata conf fcDat te progADTs p (srOne (mkSemiring SRSumProduct (logSpace conf))) verdicts sharedSets Set.empty detGens cyclicGens SRSumProduct reinferC Set.empty [] [] laws Map.empty True False knot
    reinferC = reinferCtx fcDat p
    -- One walk of the whole program, shared by every 'meta' built below.
    verdicts = materializationVerdicts p
    sharedSets = materializationScopes p
    -- Likewise one call-graph fixpoint, shared: which generate functions are
    -- deterministic when applied to deterministic arguments.
    detGens = Set.fromList [n ++ "_gen" | (n, True) <- Map.toList (functionSummaries p)]
    -- The call graph over-approximates exactly as 'ModalityInfer.summaries'
    -- does (referenced names taken flat), which can only enlarge a cycle and
    -- so only ever refuses more.
    cyclicGens =
      let decls = functions p
          declNames = Set.fromList (map fst decls)
          callees b = Set.toList (Set.intersection declNames (containedVars varsOfExpr b))
      in Set.fromList [ n ++ "_gen"
                      | CyclicSCC grp <- stronglyConnComp [ (n, n, callees b) | (n, b) <- decls ]
                      , n <- grp ]
    extractParamNames (Expr _ (Lambda name lambdaBody)) = name : extractParamNames lambdaBody
    extractParamNames _ = []
    stripLambdas (Expr _ (Lambda _ lambdaBody)) = stripLambdas lambdaBody
    stripLambdas e = e


-- | Run one variant's compilation. A 'Left' is a static refusal (see
-- 'refuse'): the variant is then absent, with that reason recorded on its group.
runCompile :: CompilerMetadata -> CompilerMonad PResult -> Either VariantRefusal IRExpr
runCompile meta codeGen = generateLetInBlock meta <$> (runCompilerMonad $ do
  res <- codeGen
  case unP (rProb res) of
    IRLambda _ _ -> return res
    _ -> setVariables [("l_r", packResult res)] >>
                return (unpackResult "l_r")
  --
  )

-- | Compile a PNormal/PLogNormal expression to a function returning (mu, sigma) as
-- an @IRConstruct TgTuple@ pair.  Lambda wrappers are preserved so the result has
-- the same arity as the original binding; parameter types are added to the type
-- environment so that inner Var references resolve correctly.
compileNormalExpr :: CompilerMetadata -> Expr -> Either VariantRefusal IRExpr
compileNormalExpr = compileNormalWith toIRNormal

-- | 'compileNormalExpr' with the (mu, sigma) extraction of the stripped body given.
compileNormalWith :: (CompilerMetadata -> Expr -> CompilerMonad (IRExpr, IRExpr))
                  -> CompilerMetadata -> Expr -> Either VariantRefusal IRExpr
compileNormalWith extract meta (Expr _ (Lambda name subExpr)) =
  let newMeta = meta { typeEnv = (name, (rType (getTypeInfo subExpr), False)) : typeEnv meta }
  in IRLambda name <$> compileNormalWith extract newMeta subExpr
compileNormalWith extract meta expr = do
  o <- runCompilerMonad (extract meta expr)
  return (closeExpr o (\(mu, sigma) -> IRConstruct TgTuple [mu, sigma]))

-- | Per-component normal functions for the Continuous positions of a structured
-- output: tuple components, Either payloads and ADT fields, at any nesting depth.
-- A position is named by the same path scheme 'SPLL.AutoNeural.requiredNormalFns'
-- uses (@_fst@/@_snd@, @_left@/@_right@, @_<Ctor>_<field>@), so @main = Pos Normal
-- Normal@ yields @main_normal_Pos_0@ and @main_normal_Pos_1@.
--
-- A position below a constructor holds the payload's law *given* that constructor
-- (task writelogits-continuous-leaf-under-sum-type). That is the leaf's own law only
-- when the leaf is the one expression that can produce the position: the walk goes
-- through the outer parameter lambdas, tuple and constructor applications and @if@
-- arms, and stops at anything else. A position is generated only when exactly one
-- stopped-at expression lies on or above it -- two are a mixture (refused until
-- encode-07's @collapse@), and an opaque one above it (a call, a variable, a @let@)
-- may produce it unseen. Since the walk never enters a @let@, the leaf shares no
-- random variable with the conditions that select it, so the arm's conditioning
-- does not change its law (a gated variable's truncated law is the case this rules
-- out). The leaf must still be one Normal by its own modality
-- ('generateComponentNormalFunction'). A dead arm needs nothing here: writeLogits
-- guards it ('SPLL.AutoNeural.deadSlotFill').
--
-- A network read's own slots (task writelogits-dropped-for-read-passthrough-continuous-leaf).
-- A read with a plan is Gaussian in every Continuous slot, each conditional on its
-- constructor, so a stopped-at leaf that *is* a read, or a constructor-guarded
-- projection of one -- field accessors and @fst@/@snd@ over a read, or over a
-- variable a @draw@ bound to one -- holds the read's slots below the projected
-- position, and gets a normal function per slot reading its (mu, sigma)
-- ('readNNSlotNormal'). So the walk enters a @draw@ (an applied lambda) whose
-- argument is such a read projection, and then must not let the read's
-- variable condition the leaf: an @if@ whose condition reads it is opaque (a
-- stopped-at expression), unless the condition reads it only through
-- constructor tests (@isObj (ob1 sc)@), which condition no Continuous slot
-- beyond the constructor its law is already given. A leaf that transforms a
-- read (@px (ob1 sc) - 1.0@) is not a projection and stays refused, as does a
-- position two arms produce.
-- Functions are registered via the _component_ prefix mechanism in reduceIREnv.
generateTupleComponentNormalFunctions :: CompilerMetadata -> String -> Expr -> [(IRFunGroup, Bool)]
generateTupleComponentNormalFunctions meta baseName expr =
  catMaybes
    [ generateComponentNormalFunction meta (baseName ++ "_normal" ++ concat path) (wrap leaf) (getTypeInfo leaf)
    | (env, path, leaf) <- occurrences, not (null path), soleProducer path
    , isNothing (readProjection env leaf)
    , Set.null (freeVarsExpr leaf `Set.intersection` Set.fromList (map fst env)) ]
  -- A network read's fields are Gaussian by the read-logits plan itself (each field
  -- conditional on its constructor), so every Continuous slot of its plan below the
  -- projected position is one.
  ++ [ (componentNormalGroup fullName
         (compileNormalWith (\m e -> readNNSlotNormal m k e) meta (wrap readE)), True)
     | (env, path, leaf) <- occurrences, soleProducer path
     , Just (readE, plan, acc) <- [readProjection env leaf]
     , (slotSteps, k) <- continuousSlotPaths plan
     , Just below <- [stripPrefix acc slotSteps]
     , not (null path && null below)
     , let fullName = baseName ++ "_normal" ++ concat path ++ concat below ]
  where
    (wrap, outBody) = stripOuter expr id
    stripOuter (Expr ti (Lambda name lambdaBody)) w = stripOuter lambdaBody (\e -> w (Expr ti (Lambda name e)))
    stripOuter e w = (w, e)
    outerParams = lambdaParams expr
    lambdaParams (Expr _ (Lambda name lambdaBody)) = Set.insert name (lambdaParams lambdaBody)
    lambdaParams _ = Set.empty
    ctorNames = [ c | decl <- adtDecls meta, (c, _) <- constructors decl ]
    ctorTests = [ "is" ++ c | c <- ctorNames ]
    fieldPaths = [ (field, "_" ++ c ++ "_" ++ show j)
                 | decl <- adtDecls meta, (c, fields) <- constructors decl
                 , (j, (field, _)) <- zip [0 :: Int ..] fields ]
    occurrences = walk [] [] outBody
    -- env: draw-bound variables whose value is a read projection, resolved.
    walk env path e@(Expr _ f) = case f of
      InjF (Named "TCons") [a, b] -> walk env (path ++ ["_fst"]) a ++ walk env (path ++ ["_snd"]) b
      InjF (Named "left") [a]     -> walk env (path ++ ["_left"]) a
      InjF (Named "right") [a]    -> walk env (path ++ ["_right"]) a
      InjF (Named c) args | c `elem` ctorNames ->
        concat [ walk env (path ++ ["_" ++ c ++ "_" ++ show j]) a | (j, a) <- zip [0 :: Int ..] args ]
      IfThenElse c a b | conditionOk env c -> walk env path a ++ walk env path b
      Apply (Expr _ (Lambda x drawBody)) arg
        | Just r <- readProjection env arg -> walk ((x, r) : env) path drawBody
      _ -> [(env, path, e)]
    soleProducer path = length [ () | (_, q, _) <- occurrences, q `isPrefixOf` path ] == 1
    -- The network read a projection chain ends in, its plan, and the chain's path
    -- in the plan's slot naming scheme.
    readProjection env e@(Expr _ f) = case f of
      ReadNN _ _
        | Just (_, plan, _) <- planReadOf meta e
        , freeVarsExpr e `Set.isSubsetOf` outerParams -> Just (e, plan, [])
      Var x | Just r <- lookup x env -> Just r
      InjF (Named "fst") [a] -> extend "_fst" <$> readProjection env a
      InjF (Named "snd") [a] -> extend "_snd" <$> readProjection env a
      InjF (Named n) [a] | Just step <- lookup n fieldPaths -> extend step <$> readProjection env a
      _ -> Nothing
      where extend step (r, plan, acc) = (r, plan, acc ++ [step])
    -- A condition may read a draw-bound read only through constructor tests.
    conditionOk env c = Set.null (freeVarsExpr (stripTests env c) `Set.intersection` Set.fromList (map fst env))
    stripTests env (Expr ti f) = case f of
      InjF (Named t) [a] | t `elem` ctorTests, isJust (readProjection env a) -> Expr ti (Constant (VBool True))
      _ -> Expr ti (fmap (stripTests env) f)

-- | Generate a single per-component normal function if the expression is extractable and PNormal/PLogNormal.
-- Stored in normalFun field and registered via _component_ prefix in reduceIREnv (bare name, no suffix).
-- The flag is whether the component is Gaussian: a PLogNormal one returns the parameters of the
-- underlying Normal (mu_log, sigma), which a writeLogits Gaussian slot must not be filled from
-- (task writelogits-labels-lognormal-as-gaussian).
generateComponentNormalFunction :: CompilerMetadata -> String -> Expr -> TypeInfo -> Maybe (IRFunGroup, Bool)
generateComponentNormalFunction meta fullName expr ti
  | (pType ti == PNormal || pType ti == PLogNormal) && isNormalExtractable expr =
      Just (componentNormalGroup fullName (compileNormalExpr meta expr), pType ti == PNormal)
  | otherwise = Nothing

-- | The group holding one output component's normal function.
componentNormalGroup :: String -> Either VariantRefusal IRExpr -> IRFunGroup
componentNormalGroup fullName compiled =
  IRFunGroup (componentNormalGroupPrefix ++ fullName)
    Nothing
    Nothing
    Nothing
    Nothing
    (either (const Nothing) (\c -> Just (c, "Per-component normal extraction for output component: " ++ fullName)) compiled)
    ""
    [ ("normal", r) | Left r <- [compiled] ]
    -- No prob function, so no query domain to enumerate (M3).
    Nothing
    Nothing

-- Return type (name, rType, hasInferenceFunctions)
getGlobalTypeEnv :: Program -> TypeEnv
getGlobalTypeEnv p = funcEnv ++ implicitFuncEnv ++ neuralEnv
  where funcEnv = map (\(name, expr) -> (name, (rType (getTypeInfo expr), True))) (functions p)
        implicitFuncEnv = map (\(name, rt) -> (name, (rt, False))) (implicitFunctionsRTypeProg p)
        neuralEnv = map (\(name, rt, _) -> (name, (rt, False))) (neurals p)


-- | The first comparison (@<@\/@>@) in an expression that modality inference
-- left intractable although both its operands are tractable -- the node where
-- 'SPLL.Typing.ModalityInfer.compareGround' found no closed form for the pair
-- -- with a diagnostic and its chain name.
comparisonWithoutClosedForm :: Expr -> Maybe (String, ChainName)
comparisonWithoutClosedForm e@(Expr ti f) = case f of
  InjF (Named op) [a, b]
    | op `elem` ["lt", "gt"], pType ti == Bottom, tractable a, tractable b ->
        Just (why op, chainName ti)
  _ -> listToMaybe (mapMaybe comparisonWithoutClosedForm (getSubExprs e))
  where
    tractable x = pType (getTypeInfo x) `elem` [Deterministic, Integrate, PNormal, PLogNormal]
    why op = "the comparison `" ++ (if op == "lt" then "<" else ">") ++ "`"
          ++ maybe "" ((" at " ++) . spanPretty) (srcPos ti)
          ++ " has no closed form for its two random operands. NeST measures a comparison"
          ++ " when one side is deterministic or recovered from the observation as a point,"
          ++ " both sides are Gaussian, both sides are"
          ++ " enumerable, or one side is enumerable and the two read no random variable"
          ++ " in common"

-- | The first random binding in an expression that no inference engine
-- applies to -- its applied lambda's certificate ('lawTable') lists none, so
-- the modality engine bound it sample-only (task engine-applicability-as-data)
-- -- with a diagnostic and its chain name.
bindingWithoutEngine :: LawTable -> Expr -> Maybe (String, ChainName)
bindingWithoutEngine laws e@(Expr _ f) = case f of
  Apply (Expr lti (Lambda x _)) _
    | Just (ModalityInfer.Law _ (ModalityInfer.JBinding [])) <- Map.lookup (chainName lti) laws ->
        Just (why ("the binding of '" ++ x ++ "'") lti, chainName lti)
  -- A named callee's binding, recorded on its call (task
  -- named-callee-binding-not-floored). The argument first: it is evaluated
  -- before the call binds it.
  Apply g a
    | Nothing <- bindingWithoutEngine laws a
    , Just (ModalityInfer.Law _ (ModalityInfer.JBinding [])) <- Map.lookup (ModalityInfer.callBindingKey (chainName ti)) laws ->
        Just (why ("the parameter bound by the call" ++ callee g) ti, chainName ti)
  _ -> listToMaybe (mapMaybe (bindingWithoutEngine laws) (getSubExprs e))
  where
    ti = getTypeInfo e
    callee g = case fst (flattenApplySpine g) of
      Expr _ (Var n) -> " of '" ++ n ++ "'"
      _ -> ""
    why what lti = "no inference engine applies to " ++ what
      ++ maybe "" ((" at " ++) . spanPretty) (srcPos lti)
      ++ ": its value is random and the body reads it, but it is not enumerable,"
      ++ " not a neural plan read, not point-invertible from the observation, has no"
      ++ " affine Gaussian form flowing into one consumer or jointly into at most "
      ++ show ModalityInfer.jointAffineMaxSlots ++ " tuple fields, and the observation has no"
      ++ " set-valued inverse onto it. The binding is sample-only, and so is the function"

-- | Where a 'Bottom' verdict starts, for a function whose root modality
-- inference typed 'Bottom' and neither 'comparisonWithoutClosedForm' nor
-- 'bindingWithoutEngine' explains (task bottom-verdict-records-no-refusal-reason:
-- @Normal + Uniform@ compiled generate-only with no word on why). Descends
-- through 'Bottom' nodes into their first 'Bottom' operand; the node none of
-- whose operands is 'Bottom' is where the rule itself returned 'Bottom', and
-- the diagnostic names it, its source position and its operands' laws. A
-- curried call is one node, its spine head and its arguments the operands, so
-- @f x y@ is named "the call of 'f'" rather than by its inner partial
-- application. A call of a function that is itself sample-only says so: that
-- function's own group carries the reason.
bottomOrigin :: Expr -> Maybe (String, ChainName)
bottomOrigin e@(Expr ti _)
  | not (isBottom e) = Nothing
  | (Expr hti (Var f), args) <- callSpine e, pType hti == Bottom =
      Just (phrase ((if null args then "" else "the call of ") ++ "'" ++ f ++ "'")
              ++ " is sample-only because '" ++ f ++ "' is: its own probability variant is refused", chainName ti)
  | (Expr _ (Var f), args@(_:_)) <- callSpine e =
      case filter isBottom args of
        (a:_) -> bottomOrigin a
        [] -> Just (rule ("the call of '" ++ f ++ "'") "arguments" args, chainName ti)
  | otherwise = case node e of
      -- The arguments first: in a let redex @(\x -> body) arg@ a 'Bottom'
      -- argument is the origin, and the body only reads it.
      Apply {} | (hd, args) <- callSpine e, (b:_) <- filter isBottom (args ++ [hd]) ->
        bottomOrigin b
      Apply {} | (hd, args) <- callSpine e -> Just (rule "the application" "operands" (hd : args), chainName ti)
      _ -> case filter isBottom (getSubExprs e) of
        (c:_) -> bottomOrigin c
        [] -> Just (rule (nodeName e) "operands" (getSubExprs e), chainName ti)
  where
    isBottom x = pType (getTypeInfo x) == Bottom
    -- The head and arguments of a curried application; a non-application is
    -- its own head.
    callSpine x = case node x of
      Apply g a -> let (h, as) = callSpine g in (h, as ++ [a])
      _ -> (x, [])
    phrase what = what ++ maybe "" ((" at " ++) . spanPretty) (srcPos ti)
    rule what kind ops =
      phrase what ++ " has no inference rule for its " ++ kind
      ++ (if null ops then "" else " " ++ listPhrase (map operand ops))
      ++ ": NeST computes no density or CDF for this combination, so it is"
      ++ " sample-only, and so is the function"
    listPhrase xs = case reverse xs of
      (l:r@(_:_)) -> intercalate ", " (reverse r) ++ " and " ++ l
      _ -> concat xs
    operand x = operandName x ++ " (" ++ lawName (pType (getTypeInfo x)) ++ ")"
    operandName x = case node x of
      Var n -> n
      Constant v -> "the literal " ++ pPrintValue v
      InjF (Named n) _ -> "a " ++ opName n ++ " expression"
      Apply {} | (Expr _ (Var f), _) <- callSpine x -> "a call of '" ++ f ++ "'"
      _ -> nodeName x
    nodeName x = case node x of
      InjF (Named n) _ -> opName n
      IfThenElse {} -> "the if-then-else"
      Lambda n _ -> "the lambda '\\" ++ n ++ "'"
      ReadNN n _ -> "the neural read of '" ++ n ++ "'"
      Var n -> "'" ++ n ++ "'"
      _ -> printFlat x
    opName n = maybe ("`" ++ n ++ "`") (\s -> "`" ++ s ++ "`") (lookup n surfaceOps)
    surfaceOps = [("plus", "+"), ("mult", "*"), ("lt", "<"), ("gt", ">"), ("neg", "-")]
    lawName p = case p of
      Deterministic -> "deterministic"
      PNormal -> "Gaussian"
      PLogNormal -> "log-normal"
      Integrate -> "random"
      PArr {} -> "a function"
      _ -> show p

-- | Strip the branch-count field from all probability-mode functions in the environment.
-- Applied after compilation and before optimisation when countBranches = False.
-- Two-step: (1) rewrite bc extractions throughout the body to a constant 0 and shift
-- the following field's extraction up one level; (2) peel through wrappers to collapse
-- the outermost (prob, (dim, (bc, imposs))) result to (prob, (dim, imposs)).
-- The impossibility flag is NOT stripped: it is the last field either way, and a
-- called function's callers read it (see 'unpackResult').
--
-- A generate function can call an inference function too: a 'collapse'
-- operand's moments weigh a mixture's arms by its condition's probability,
-- and that condition may be a call (a helper-extract rewrite of the
-- corpus program collapseMixture found it).
-- Its projections off such a call shift like any caller's, but the generate
-- body is not an inference result, so it is rewritten with 'stripGen': no
-- 'stripOuterTriple' (a sampled four-tuple is a value, not a packed result),
-- and only a call whose head is an inference function's name counts as a
-- callee result (a sampled tuple from a @_gen@ call keeps every field).
stripBranchCount :: IREnv -> IREnv
stripBranchCount (IREnv funcs adtDecls'' consts) = IREnv (map stripGroup funcs) adtDecls'' consts
  where
    stripGroup fg = fg { probFun  = fmap stripFun (probFun fg)
                       , integFun = fmap stripFun (integFun fg)
                       , normalFun = fmap stripFun (normalFun fg)
                       , genFun = fmap stripGen (genFun fg) }
    -- In an inference body any call may return a packed result (a closure
    -- parameter applied to the sample is one), except a call of a generate
    -- function: its value is a sample, whatever its shape. The deterministic-
    -- application leaf binds @mk_gen(s1)(s2)(s3)(s4)@ to compare it against
    -- the query, and a four-deep tuple read as a callee's result lost its
    -- last fields (task trajectory-tail-bound-as-tuple-type-error).
    stripFun (expr, doc) = (strip (not . callsNamed generateNames) True Set.empty expr, doc)
    stripGen (expr, doc) = (strip (callsNamed inferenceNames) False Set.empty expr, doc)

    inferenceNames = Set.fromList (concat [ [groupName fg ++ "_prob" | isJust (probFun fg)]
                                           ++ [groupName fg ++ "_integ" | isJust (integFun fg)]
                                         | fg <- funcs ])
    generateNames = Set.fromList [ groupName fg ++ "_gen" | fg <- funcs, isJust (genFun fg) ]
    callsNamed names e = case e of
      IRApply f _ -> callsNamed names f
      IRVar n -> n `Set.member` names
      _ -> False

    -- Scope-aware rewrite. @callResults@ holds the variables currently bound to
    -- ANOTHER function's result tuple: that callee's own body was collapsed by
    -- 'stripOuterTriple', so it now returns three fields and projections off it
    -- shift up one level. A variable bound to a locally packed result keeps its
    -- full width -- 'stripOuterTriple' only fires at a lambda body -- so its
    -- projections must NOT shift.
    --
    -- That distinction is structural, not lexical. The predecessor of this
    -- function asked whether the variable's NAME came from 'mkVariable'
    -- ("l_<digits>_<suffix>"), which is true of both kinds, and so mis-shifted
    -- any hoisted local result tuple. That forced call sites to keep such
    -- tuples inline as a workaround (the body-factor binding in the
    -- witnessed-let case), which in turn is what made per-field re-wrapping of
    -- let-in blocks the only option there.
    --
    -- @isCall@ decides which applications return a callee result, and @outer@
    -- whether a lambda body is a function's packed result ('stripOuterTriple').
    strip :: (IRExpr -> Bool) -> Bool -> Set.Set Varname -> IRExpr -> IRExpr
    strip isCall outer = go
     where
     go callResults e = case e of
      -- Projections off a callee's result: the bc slot is gone (read 0), and
      -- the flag that followed it moves up into the slot bc vacated.
      IRDestruct AcFst (IRDestruct AcSnd (IRDestruct AcSnd (IRVar x))) | x `Set.member` callResults -> IRConst (VFloat 0)
      IRDestruct AcSnd (IRDestruct AcSnd (IRDestruct AcSnd (IRVar x))) | x `Set.member` callResults -> IRDestruct AcSnd (IRDestruct AcSnd (IRVar x))
      -- Binding forms: rebind the name, so shadowing cannot leak a stale
      -- classification into an inner scope.
      --
      -- A value that holds a callee result in one arm is read as one in every
      -- arm, so an arm that packs a result locally (an impossible fallback
      -- beside a guarded call) is collapsed to the callee's width too. Left
      -- at full width, one 'IRIf' answered two layouts and the shifted flag
      -- projection read a tuple on the local arm (task
      -- ir-contract-violations-in-compiler-output,
      -- higher-order/namedFunctionCurriedWitness).
      IRLetIn n v irBody ->
        let v' = go callResults v
            callee = holdsCalleeResult isCall outer callResults v
        in IRLetIn n (if callee then stripLocalArms v' else v')
                     (go (rebind n callee callResults) irBody)
      IRLambda n irBody ->
        IRLambda n ((if outer then stripOuterTriple else id) (go (rebind n False callResults) irBody))
      -- A tensor map's lambda is an enumeration LOOP binder, not a function
      -- body, so it gets the rebind but NOT 'stripOuterTriple' -- which exists
      -- to collapse the result triple a compiled function returns. Before task
      -- retire-irenumsum the loop was @IREnumSum@/@IRLogEnumSum@, a
      -- constructor of its own that could not be confused with a lambda; now
      -- that it is a 'BMap' over an 'IRLambda', the distinction has to be made
      -- here or the generic 'IRLambda' arm above would claim it.
      IRBuiltin BMap [IRLambda n lamBody, t] ->
        IRBuiltin BMap [ IRLambda n (go (rebind n False callResults) lamBody)
                       , go callResults t ]
      _ -> irDescend (go callResults) e

    rebind n True  = Set.insert n
    rebind n False = Set.delete n

    -- Does this bound value come from calling a function whose body we just
    -- collapsed? Only an application does; a locally assembled 'IRConstruct'
    -- keeps its four fields. Both branch forms must agree, and an alias
    -- inherits the classification of what it aliases.
    --
    -- A redex of a literal lambda is classified by what the lambda returns
    -- (it is read before rewriting, as the lambda arm above leaves it). A
    -- packed result triple, which that arm collapses ('stripOuterTriple'),
    -- answers at the callee's width; any other tuple the body assembles is a
    -- value and keeps every field; a body ending in anything else falls back
    -- to @isCall@. In a probability function @isCall@ is @const True@, and
    -- the deterministic-application leaf binds
    -- @(\\p2 -> (s1, (p2, (s3, 0.0)))) (s1 + s2)@ to compare it against the
    -- sample: read as a callee's result, the third and fourth fields of that
    -- value were shifted like a result's bc and flag (task
    -- trajectory-tail-bound-as-tuple-type-error).
    --
    -- Only where that arm collapses it, i.e. under @outer@. A generate body
    -- ('stripGen') keeps every lambda body at full width, so a packed triple
    -- in a redex there stays four fields wide and is read as a local value:
    -- a 'collapse' operand's moments bind an inlined probability of its
    -- condition (@(\\k -> (cdf, (0, (1.0, False)))) 0.25@, the draw-intro
    -- rewrite of collapseMixture) and, read as a callee result, the shifted
    -- flag projection read @(1.0, False)@ as a Bool (the regression of
    -- 415173b, task trajectory-tail-bound-as-tuple-type-error).
    --
    -- A redex whose body ends in something other than a tuple is classified
    -- by that body, its parameter bound to what the argument is: the
    -- deterministic-application leaf binds @(\\y -> mk_gen(s1)(y)) s2@ where
    -- a @draw y = s2@ alias precedes a helper call, and the redex itself is
    -- no call of a generate function, so @isCall@ read the sampled four-tuple
    -- as a callee's result and shifted its last two fields (task
    -- alias-before-helper-built-tuple-tail-approx-type-error).
    holdsCalleeResult isCall outer env v = case v of
      IRApply (IRLambda n irBody) arg
        | tails <- returnedTuples irBody, not (null tails) ->
            outer && any isPackedTriple tails
        | otherwise ->
            holdsCalleeResult isCall outer (rebind n (holdsCalleeResult isCall outer env arg) env) irBody
      -- A call handed a closure that returns a packed result is read as one:
      -- that closure's body is collapsed by the lambda arm (under @outer@), so
      -- what the call returns -- the closure's result, which the compiler
      -- unpacks as a 'PResult' -- is three fields wide. The callee may be a
      -- generate function (@f_gen(\\x -> packed)@, a function-valued random
      -- argument applied by a named higher-order function, whose call
      -- @isCall@ excludes), so this is asked independently of @isCall@ (task
      -- integ-of-called-function-value-main-integ-type-error,
      -- higher-order/hoTopLevel, namedHofRandomFunctionArg).
      IRApply _ _      -> isCall v || (outer && any returnsPackedResult (spineArgs v))
      IRVar x          -> x `Set.member` env
      IRLetIn n b irBody -> holdsCalleeResult isCall outer (rebind n (holdsCalleeResult isCall outer env b) env) irBody
      IRIf _ t f       -> holdsCalleeResult isCall outer env t || holdsCalleeResult isCall outer env f
      _                -> False

    -- The tuples a lambda body returns, through its let-bindings, both arms
    -- of an 'IRIf' and nested literal-lambda redexes (a let too); empty when
    -- some arm ends in anything but a tuple construction.
    returnedTuples e = case e of
      IRLetIn _ _ irBody -> returnedTuples irBody
      IRApply (IRLambda _ irBody) _ -> returnedTuples irBody
      IRIf _ t f -> case (returnedTuples t, returnedTuples f) of
        (ts@(_:_), fs@(_:_)) -> ts ++ fs
        (ts, []) | isError f -> ts
        ([], fs) | isError t -> fs
        _ -> []
      IRConstruct TgTuple _ -> [e]
      _ -> []
    isError (IRError _) = True
    isError _ = False

    -- The arguments of an application spine, @f a b@ giving @[b, a]@.
    spineArgs (IRApply f a) = a : spineArgs f
    spineArgs _ = []

    -- A closure (possibly curried, let-bound or selected by an 'IRIf') whose
    -- body returns a packed result triple.
    returnsPackedResult e = case e of
      IRLambda _ irBody -> returnsPackedResult irBody || any isPackedTriple (returnedTuples irBody)
      IRLetIn _ _ irBody -> returnsPackedResult irBody
      IRIf _ t f -> returnsPackedResult t || returnsPackedResult f
      _ -> False
    isPackedTriple (IRConstruct TgTuple [_, IRConstruct TgTuple [_, IRConstruct TgTuple [_, _]]]) = True
    isPackedTriple _ = False

    -- Collapse (prob, (dim, _)) → (prob, dim) peeling through IRLambda/IRLetIn wrappers,
    -- and through the query-type guard's IRIf (whose then-branch carries the real triple;
    -- the else-branch is an IRError, left untouched by the catch-all).
    --
    -- One literal shape is matched for the triple: 'IRConstruct TgTuple' chains, built by
    -- both this module's own 'packResult' (migrated in design ir-reengineering, slice S1e)
    -- and 'SPLL.AutoNeural.makeProb' (slice S1b). Before S1e landed, the two producers
    -- disagreed (packResult still built 'IRTCons'), so this had two clauses for the same
    -- triple; they collapsed into one once packResult moved onto the shared encoding.
    stripOuterTriple (IRLambda n irBody)         = IRLambda n (stripOuterTriple irBody)
    stripOuterTriple (IRLetIn n v irBody)        = IRLetIn n v (stripOuterTriple irBody)
    stripOuterTriple (IRIf c t e)              = IRIf c (stripOuterTriple t) (stripOuterTriple e)
    stripOuterTriple (IRConstruct TgTuple [a, IRConstruct TgTuple [b, IRConstruct TgTuple [_, imp]]]) =
      IRConstruct TgTuple [a, IRConstruct TgTuple [b, imp]]
    stripOuterTriple e                         = e

    -- 'stripOuterTriple' through the arms of a bound value only: a lambda in
    -- a bound value is a closure, not that value's result.
    stripLocalArms (IRLetIn n v irBody) = IRLetIn n v (stripLocalArms irBody)
    stripLocalArms (IRIf c t e) = IRIf c (stripLocalArms t) (stripLocalArms e)
    stripLocalArms e@(IRConstruct TgTuple _) = stripOuterTriple e
    stripLocalArms e = e
