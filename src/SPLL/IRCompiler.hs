-- The pattern-match coverage checker exceeds its default 30-model budget on
-- 'toIRGenerate's Var case (a 4-way match over @Maybe (RType, Bool)@ with a
-- nested RType pattern), and then reports that exhaustive match as incomplete.
-- Raising the budget lets it finish rather than hiding the result. Two more
-- guarded clauses at the top of 'toIRInference' (task
-- set-witness-eq-o2-optimizer-crash) pushed a second check -- 'toIRGenerate's
-- Var case again, per the checker's own report site -- over 1000 as well;
-- raised again rather than split the check.
{-# OPTIONS_GHC -fmax-pmcheck-models=4000 #-}
module SPLL.IRCompiler (
  envToIR,
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
import SPLL.IRUtil
import SPLL.OptimizerProjection (optimizerConfig)
import SPLL.CompilerConfig
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.IROptimizer
import SPLL.IRSelectPass (selectPassEnv)
import PrettyPrint (pPrintValue)
import PredefinedFunctions
import SPLL.Analysis (isEnumerable, latentDependencies, sharesEnumeratedLatent, isCandidateBinaryEnumInjF, injFLatentVerdicts, materializationVerdicts, materializationScopes, getValuesFromExpr, enumerableDomain, headIsConditional)
import SPLL.Typing.PType
import Data.Maybe
import Data.List (isPrefixOf, isSuffixOf, stripPrefix, (\\), find, elemIndex, nub, intercalate, sort, partition)
import Data.Functor ((<&>))
import SPLL.AutoNeural hiding (planReadOf, planProjectedReadOf)
import SPLL.Typing.ForwardChaining
import SPLL.Typing.Determinism (functionSummaries)
import SPLL.Typing.ModalityInfer (reinferCtx, LawTable)
import Control.Applicative ((<|>))
import qualified SPLL.Typing.ModalityInfer as ModalityInfer
import SPLL.Typing.AlgebraicDataTypes
import SPLL.IRTypeBridge (irConformanceType)
import SPLL.Semiring
import Control.Monad (foldM, forM, when)
import Control.Monad.Except (catchError)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Graph (SCC(..), stronglyConnComp, flattenSCC)
import SPLL.IRCompiler.Monad hiding (toIRGenerate, toIRInference, toIRInferenceSave)
import SPLL.IRCompiler.Binding
import SPLL.IRCompiler.Materialize
import SPLL.IRCompiler.Gaussian
import SPLL.IRCompiler.Worlds
import SPLL.IRCompiler.Plan
import SPLL.IRCompiler.Dispatch

-- | Whether a condition weight is (approximately) the semiring zero, the test
-- an 'IfThenElse' arm guard reads. Linear 0.0 is tested approximately;
-- log-space uses exact equality against negative infinity, since
-- @(-inf) - (-inf)@ is NaN and an approximate test would report two
-- impossible operands "not equal", i.e. live -- the wrong direction for a
-- guard whose job is to skip an arm that may hold a nonterminating call.
deadWeightIR :: Semiring -> IRExpr -> IRExpr
deadWeightIR sr c
  | srLogSpace sr = IROp OpEq c (srZero sr)
  | otherwise     = IROp OpApprox c (srZero sr)

-- | The (True, False) weights of a Bool @if@ condition, compiled in one pass
-- (task map-semiring-complement-and-cdf-wrong).
--
-- A condition that is itself a Bool @if c then a else b@ is built from its
-- children's pairs, each child compiled once:
--
-- > pT = cT (x) aT (+) cF (x) bT
-- > pF = cT (x) aF (+) cF (x) bF
--
-- so its False weight is the semiring's own combine over the False
-- derivations. Deriving it as @1 - pT@ instead is a probability-conservation
-- identity: right under sum-product, wrong under max-product, where it is
-- @1 - max@ rather than the best False derivation. A @not@ swaps the pair.
-- Compile cost stays linear in nesting depth -- compiling the condition at
-- each polarity separately would double it per level, the O(2^d) blowup of
-- fuzz-qc-compiler-bugs item 3.
--
-- Each arm's pair is bound once, under the arm guard the 'IfThenElse' case
-- applies to its own arms: the arm's weight is not the semiring zero, and
-- under topK the accumulated path probability through it reaches the cutoff.
-- A pruned arm contributes the semiring zero to both weights, so both are
-- lower bounds, which is what lets the condition be compiled pruned.
--
-- Any other condition is a leaf of this recursion. Under a semiring that
-- conserves probability ('srConserves'), or when the leaf has a single
-- derivation ('singleDerivation': a comparison of one distribution leaf
-- against a bound, say), it is compiled at True, unpruned, and
-- its False weight is the complement in the semiring's sense ('mixWith' of
-- 'srComplement', so a True outcome that is a density leaves the whole unit
-- mass at dim 0 on the False side; task
-- sampling-matches-pdf-continuous-equality-density). Under one that does not,
-- the leaf is compiled at each polarity: the complement of a combined weight
-- (an @a || b@, a call) is not the other side's weight there. That doubles
-- only the leaf's own compile, and only under max-product.
condWeights :: CompilerMetadata -> Expr -> CompilerMonad (PResult, PResult)
condWeights meta (Expr _ (InjF (Named "not") [c])) = (\(t, f) -> (f, t)) <$> condWeights meta c
condWeights meta (Expr _ (IfThenElse c a b)) = do
  let sr = semiringOf meta
  (cT, cF) <- condWeights meta c
  cTV <- shareWeight "condpairT" cT
  cFV <- shareWeight "condpairF" cF
  (aT, aF) <- armPair cTV a
  (bT, bF) <- armPair cFV b
  let bc x y = IROp OpPlus (IRIf (deadWeightIR sr (unP (rProb cTV))) const0 (rBranches x))
                           (IRIf (deadWeightIR sr (unP (rProb cFV))) const0 (rBranches y))
  t <- mixP sr (bc aT bT) (weigh cTV aT) (weigh cFV bT)
  f <- mixP sr (bc aF bF) (weigh cTV aF) (weigh cFV bF)
  return (t, f)
  where
    sr' = semiringOf meta
    weigh w arm = onBranches (const (rBranches arm)) (prodP sr' w arm)
    shareWeight tag r = do
      v <- mkVariable tag
      setVariables [(v, packResult r)]
      return (unpackResult v)
    armPair w arm = do
      let accArm = srTimes sr' (accProb meta) (unP (rProb w))
          pruneGuard = case topKThreshold (compilerConfig meta) of
            Just _  -> [notIR (IROp OpLessThan accArm (IRVar topKCutoffParamName))]
            Nothing -> []
          guards = notIR (deadWeightIR sr' (unP (rProb w))) : pruneGuard
      armO <- scoped ((\(t, f) -> [t, f]) <$> condWeights meta { accProb = accArm } arm)
      -- Each weight is read once, by one of the two mixtures above.
      closed <- closeResults sr' "condpair_arm" guards armO
      case closed of
        [t, f] -> return (t, f)
        _ -> error "condWeights: closeResults returned other than two results"
condWeights meta c
  | srConserves sr || singleDerivation c = do
      t <- toIRInference (unpruned meta) False c (IRConst (VBool True))
      f <- mixWith (\_ p -> srComplement sr p) const0 (mass (srOne sr)) t
      return (t, f)
  | otherwise = (,) <$> toIRInference meta False c (IRConst (VBool True))
                    <*> toIRInference meta False c (IRConst (VBool False))
  where sr = semiringOf meta

-- | Whether every value of a random expression has at most one derivation (one
-- control-flow path producing it), so that 'srComplement' of its CDF is its
-- upper tail under every semiring, max-product included: a distribution
-- leaf, a Gaussian closed form, or an InjF that transforms one such operand
-- with deterministic ones. Conservative: anything else (an @if@, an
-- enumerated sum of two random operands, a call, a let) answers False.
singleDerivation :: Expr -> Bool
singleDerivation (Expr ti nd)
  | pType ti `elem` [Deterministic, PNormal, PLogNormal] = True
  | otherwise = case nd of
      Var "Uniform" -> True
      Var "Normal"  -> True
      InjF _ ps -> case filter (\x -> pType (getTypeInfo x) /= Deterministic) ps of
        [r] -> singleDerivation r
        _   -> False
      _ -> False


-- | The inverse body and applicability test to invert a bound through, in
-- the given mode. A point query takes the declaration's own. A cumulative one
-- through an exact integer quotient ('roundedQuotientInverse') takes the
-- rounded bound instead -- the floor where the inverse is increasing, the
-- ceiling where it is decreasing (@v * (-6) <= -7@ is @v >= ceil(7/6) = 2@) --
-- under a guard that no longer demands divisibility, which made every
-- non-multiple bound "impossible" (task cdf-through-discrete-inverse-wrong).
modeInverse :: Bool -> FDecl -> IRExpr -> (IRExpr, IRExpr)
modeInverse cumulative decl deriv
  | cumulative, Just (floorB, ceilB, app) <- roundedQuotientInverse decl =
      (IRIf (IROp OpGreaterThan deriv const0) floorB ceilB, app)
  | otherwise = (body decl, applicability decl)

envToIR :: CompilerConfig -> FCData -> LawTable -> Program -> IREnv
envToIR conf fcDat laws p
  | any (null . chainName . getTypeInfo . snd) (functions p) =
      error "envToIR: one or more top-level expressions have empty chainNames — did you call annotateProg before envToIR?"
  | otherwise =
      -- This entry point has no error channel of its own, so a refusal from
      -- 'requireNoGenerateBacked' can only be thrown here. 'Prelude.compile',
      -- the entry point everything actually uses, threads the 'Left' instead
      -- (task compiler-throws-instead-of-returning-left).
      let unopt    = either error id (envToIRUnoptimized conf fcDat laws p)
          stripped = if countBranches conf then unopt else stripBranchCount unopt
          -- Batched mode: retag elementwise ifs to selects before optimizing
          -- (design pytorch-tensorizer). Mirrors 'Prelude.compile'.
          selected = if batched conf then selectPassEnv stripped else stripped
      in optimizeEnvWith (optimizerConfig conf) (Set.fromList [n | (n, _, _) <- neurals p]) selected

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
    meta te = CompilerMetadata conf fcDat te progADTs p (srOne (mkSemiring SRSumProduct (logSpace conf))) verdicts sharedSets Set.empty detGens cyclicGens SRSumProduct reinferC Set.empty [] [] laws Map.empty True knot
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
          ++ " when one side is deterministic, both sides are Gaussian, both sides are"
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

toIRInferenceSave :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
toIRInferenceSave meta cumulative (Expr t (Lambda name subExpr)) sample = do
  let newMeta = extendMetaForLambda meta t name
  irTuple <- scoped (toIRInferenceSave newMeta cumulative subExpr sample) <&> generateLetInBlock meta
  return (detP (IRLambda name irTuple))
toIRInferenceSave meta cumulative expr sample = do
  o <- scoped (toIRInference meta cumulative expr sample)
  anySafeShared (semiringOf meta) sample o

-- | Does every value of this type necessarily contribute dimension 0 -- i.e.
-- is it discrete through and through?
--
-- This exists to bound the branch pruning in the field-constructor equation
-- (task recursive-list-prob-missed-cse). Pruning a field that an earlier field
-- has already ruled out means not evaluating it, which means its dimension
-- contribution is reported as 0 rather than whatever it would have been. That
-- is only safe when the two are the same number.
--
-- It has to be a TYPE-level test, and it is genuinely not possible to do
-- better by inspecting the compiled field: a recursive call's 'rDim' is a
-- projection off the call's own result ('IRDestruct AcFst (IRDestruct AcSnd
-- (IRVar "l_9_guarded"))'), so reading the true dimension requires performing
-- exactly the recursion the pruning exists to avoid. Dimension and pruning are
-- mutually exclusive for any field that can carry a continuous payload, which
-- is why this predicate is the boundary rather than something cleverer.
--
-- The convention it protects is pinned by 'test/cases/data-structures/
-- tupleRoundtrip.tst': @p((0.5, 2.5))=(0.0, 2.0)@ -- an out-of-support query
-- against a tuple of two continuous fields still reports dimension 2, not 0.
-- Dimensionality there is a property of the branch, not of the query point.
-- ('mixWith' is the opposite case and needs no protection: it discards an
-- impossible side's dimension outright before comparing.)
--
-- Conservative in both directions that matter: an unknown, open or
-- not-yet-resolved type answers 'False' (no pruning, current behaviour), and a
-- recursive ADT terminates via @seen@ rather than being assumed either way.
dimZeroByType :: [ADTDecl] -> RType -> Bool
dimZeroByType decls = go []
  where
    go seen ty = case ty of
      TBool        -> True
      TInt         -> True
      TSymbol      -> True
      TUnit        -> True
      NullList     -> True
      ListOf t     -> go seen t
      TTensor _ t  -> go seen t
      Tuple a b    -> go seen a && go seen b
      TEither a b  -> go seen a && go seen b
      -- A recursive ADT is dimension-0 as long as no reachable field is
      -- continuous; revisiting a name already on the stack adds no new
      -- field types, so it answers 'True' and lets the other arms decide.
      TADT n
        | n `elem` seen -> True
        | otherwise     -> case find ((== n) . dataName) decls of
            Nothing -> False
            Just d  -> all (go (n : seen) . snd) (concatMap snd (constructors d))
      -- TFloat, TVarR (may be instantiated continuous), TThetaTree, TArrow,
      -- BottomTuple, GreaterType, NotSetYet.
      _            -> False

toIRInference :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
--toIRInference meta cumulative expr sample | trace (show expr) False = undefined
-- A witnessed sample can itself be the 'VAnyExcept' placeholder an '==' (or ADT
-- constructor-test) inverse produces on its False branch ("any value other
-- than this one") -- either bare, or still wrapped in the 'IRIf' that selects
-- it. 'transportDirect' used to produce exactly this shape when it probed the
-- True/False polarity of a comparison the witnessed variable occurs in, and
-- handed it on as a point; it now turns it into a 'WExcept' set instead
-- ('witnessSet'), whose bare-complement measure is this same split. The
-- clause stays for any other producer of a sentinel-valued sample reaching
-- the bound distribution's own inference, rather than through the InjF-probability
-- 'hasAnyExcept' combinator below (which only fires when the comparison
-- itself, not some downstream consumer of its witness, is the thing being
-- queried). Arithmetic on the sentinel -- a density's '(sample - mu)/sigma',
-- say -- is undefined: 'VAnyExcept' names a set, not a point. Previously that
-- reached 'IROptimizer.forceOp' and the interpreter's own operator evaluator
-- as a raw operand and crashed both (task set-witness-eq-o2-optimizer-crash).
-- Splitting here, generically over whichever leaf is being inferred (Normal,
-- Uniform, a user function, ...), mirrors the split the direct InjF case
-- performs: the ANY-branch mass minus the excepted point's own mass/density.
-- A hole: the masked leaf of a pruned observation (design
-- witnessed-per-query-capability, task per-mask-variants-by-pruning;
-- 'SPLL.ObservationMask.pruneObservation'). It is the unit factor -- mass one,
-- dim 0, possible, no branch -- and it never reads the sample: the slot it
-- replaced is the one the query masked, so whatever value the dispatcher handed
-- this variant there is not an observation. First, so no clause below (the
-- equality guard of an ordinary 'Constant', the Boolean CDF split) gets to
-- compare against it. 'Constant VAny' cannot occur in a user program
-- ('SPLL.Validator' forbids it), so this fires on holes only.
toIRInference meta _ (Expr _ (Constant VAny)) _ = return (detP (srOne (semiringOf meta)))
toIRInference meta cumulative e sample
  | Just (binds, shape) <- anyExceptSampleShape sample = do
  let sr = semiringOf meta
  -- 'binds' are 'sample's own leading let-bindings (e.g. 'transportDirect's
  -- materialised anchors), stripped off to see the shape beneath. Registering
  -- them via 'setVariables' -- the same mechanism the InjF 'hasAnyExcept'
  -- combinator below uses for its own seeded variables -- rather than
  -- rewrapping the result afterwards keeps them properly threaded through
  -- 'guardedSubInference'/'closeResult's own let-hoisting, which floats a
  -- sub-result's binding to a scope a post-hoc rewrap would sit below.
  setVariables binds
  -- Both operands of the subtraction are compiled 'unpruned': a pruned
  -- excepted mass would inflate the difference, and a pruned marginal could
  -- drive it negative.
  let metaSub = unpruned meta
  case shape of
    Left ex -> do
      anyRes    <- anyMarginal metaSub cumulative e
      exceptRes <- toIRInferenceSave metaSub cumulative e ex
      mixSubP sr (rBranches exceptRes) anyRes exceptRes
    Right (cond, isPosAny, nonAnyExpr, exceptExpr) -> do
      let subGuard = if isPosAny then cond else notIR cond
      let nonGuard = notIR subGuard
      nonAnyRes <- guardedSubInference meta [nonGuard] (toIRInference meta cumulative e nonAnyExpr)
      anyRes    <- anyMarginal metaSub cumulative e
      exceptRes <- guardedSubInference metaSub [subGuard] (toIRInference metaSub cumulative e exceptExpr)
      subRes <- mixSubP sr (rBranches exceptRes) anyRes exceptRes
      let ifSample a na = if isPosAny then IRIf cond a na else IRIf cond na a
      return (zipResult ifSample subRes nonAnyRes)
-- CDFs on Booleans make little sense. We define that False < True. Therefor cdf(True) = 1 and cdf(False) = pdf(False)
toIRInference meta True expr sample | rType (getTypeInfo expr) == TBool = do
  false <- toIRInference meta False expr (IRConst (VBool False))
  -- cdf(True) = 1 is always attainable; cdf(False) inherits the False case.
  return (mkPResult (sealP (IRIf sample (srOne (semiringOf meta)) (unP (rProb false)))) dim0 (rBranches false)
                  (IRIf sample constFalseIR (rImposs false)))
-- A node whose certificate is a point mass of known value ('lawPoint'): the
-- value is compared against the sample, as for a literal 'Constant'. This is
-- the zero rule of @mult(0, y)@ read off the law (task
-- mult-inversion-unguarded-at-zero, design law-carrying-modality §E): the
-- product is never inverted through a division by its zero factor, and a
-- zero bound by a @draw@ or a value set {0} counts as the literal does. It
-- also measures @draw z = Normal in 0.0 * z@ at its point, whose binding
-- nothing reads the value of.
toIRInference meta cumulative e@(Expr TypeInfo {rType=rt} _) sample
  | Just v <- lawPoint meta e =
      if cumulative
        then return (mass (compareValueExpr (semiringOf meta) rt (IRConst (valueToIR v)) sample))
        else return (indicatorP (semiringOf meta) (equalityGuard rt (IRConst (valueToIR v)) sample))
-- A conjunction of clauses over enumerable draws whose clauses share the draws
-- in a cycle: variable elimination over the draws ('ConstraintNet'), instead
-- of the nested joint enumeration the stack would otherwise get.
toIRInference meta False e sample
  | Just net <- constraintNet meta e = compileConstraintNet meta net sample
-- The Gaussian catch-all: a PNormal node whose codegen law is a leaf or an
-- affine form ('gaussianLeaf') is one Gaussian density, from the (mu, sigma)
-- its law's builder gives ('gaussianParams').
toIRInference meta False e sample | pType (getTypeInfo e) == PNormal, Just g <- gaussianLeaf meta e = do
  (mu, sigma0) <- gaussianParams meta g e
  degenerateScaleGuard meta False TFloat mu sigma0 sample $ \sigma ->
    density (scaledNormalDensity (semiringOf meta) (IROp OpDiv (IROp OpSub sample mu) sigma) [sigma]) sample
toIRInference meta True e sample | pType (getTypeInfo e) == PNormal, Just g <- gaussianLeaf meta e = do
  (mu, sigma0) <- gaussianParams meta g e
  degenerateScaleGuard meta True TFloat mu sigma0 sample $ \sigma ->
    mass (distCumulative (semiringOf meta) IRNormal (IROp OpDiv (IROp OpSub sample mu) sigma))
-- The lognormal catch-all, gated structurally ('logNormalExtractable').
toIRInference meta False e sample | pType (getTypeInfo e) == PLogNormal, logNormalExtractable meta e = do
  (mu, sigma0) <- toIRLogNormalParams meta e
  let sr = semiringOf meta
  let positive = IROp OpGreaterThan sample const0
  let negativeGuard x = IRIf positive x (srZero sr)
  -- A degenerate scale is a point mass at exp(mu), which is positive, so the
  -- support guard below stays right around it.
  r <- degenerateScaleGuard meta False TFloat (IRUnaryOp OpExp mu) sigma0 sample $ \sigma ->
    let correctedSample = IROp OpDiv (IROp OpSub (IRUnaryOp OpLog sample) mu) sigma
    in density (scaledNormalDensity sr correctedSample [sigma, sample]) sample
  -- A non-positive sample is outside the lognormal's support: impossible, not
  -- merely unlikely. Support boundaries are the one way a *density* leaf can be
  -- a structural zero, and they are known statically here.
  return (impossibleWhen (notIR positive) (onProb negativeGuard r))
toIRInference meta True e sample | pType (getTypeInfo e) == PLogNormal, logNormalExtractable meta e = do
  (mu, sigma0) <- toIRLogNormalParams meta e
  let sr = semiringOf meta
  let positive = IROp OpGreaterThan sample const0
  let negativeGuard x = IRIf positive x (srZero sr)
  r <- degenerateScaleGuard meta True TFloat (IRUnaryOp OpExp mu) sigma0 sample $ \sigma ->
    mass (distCumulative sr IRNormal (IROp OpDiv (IROp OpSub (IRUnaryOp OpLog sample) mu) sigma))
  return (impossibleWhen (notIR positive) (onProb negativeGuard r))
-- Distribution primitives (reserved-name Vars). Normal usually reaches the PNormal
-- catch-all above; these equations are the direct density/CDF leaves for Uniform and
-- the defensive Normal fallback.
toIRInference meta False (Expr _ (Var "Normal")) sample = return (density (distDensity (semiringOf meta) IRNormal sample) sample)
-- Unlike Normal, Uniform has bounded support: off it the density is not a tiny
-- tail value but an impossible event, and saying so structurally is what keeps
-- 'mixWith' from having to read it back off the zero.
toIRInference meta False (Expr _ (Var "Uniform")) sample =
  return (impossibleWhen (outsideUnitInterval sample) (density (distDensity (semiringOf meta) IRUniform sample) sample))
toIRInference meta True (Expr _ (Var "Normal")) sample = return (mass (distCumulative (semiringOf meta) IRNormal sample))
toIRInference meta True (Expr _ (Var "Uniform")) sample = return (mass (distCumulative (semiringOf meta) IRUniform sample))
toIRInference _ _ (Expr _ (Constant (VError e))) _ = return (detP (IRError e))
toIRInference meta False (Expr TypeInfo {rType=rt} (Constant value)) sample = do
  let comp = equalityGuard rt (IRConst (fmap failConversion value)) sample
  return (indicatorP (semiringOf meta) comp)
toIRInference meta True (Expr TypeInfo {rType=rt} (Constant value)) sample = return (mass (compareValueExpr (semiringOf meta) rt (IRConst (valueToIR value)) sample))
toIRInference meta True (Expr _ (ThetaI a i)) sample = do
  a' <- toIRGenerate meta a
  return (mass (IRIf (IROp OpLessThan sample (IRDestruct (AcTheta i) a')) (srZero (semiringOf meta)) (srOne (semiringOf meta))))
toIRInference meta False (Expr _ (ThetaI a i)) sample = do
  a' <- toIRGenerate meta a
  return (indicatorP (semiringOf meta) (IROp OpApprox sample (IRDestruct (AcTheta i) a')))
-- A negated condition is the un-negated one with the arms swapped. The
-- equation below derives the False weight as the complement of the True
-- weight, and that complement cannot carry a null-set convention: the True
-- weight of @not (Normal == 0.5)@ is the mass 1, whose complement is the mass
-- 0, so the density convention of the equality's True outcome (task
-- sampling-matches-pdf-continuous-equality-density) was lost and the if-flip
-- of @if Normal == 0.5 then 1 else 2@ answered p(1) impossible. Swapping
-- measures the condition at the polarity that carries the density directly
-- (task null-set-conventions-not-preserved-under-negation).
toIRInference meta cumulative (Expr ti (IfThenElse (Expr _ (InjF (Named "not") [cond])) left right)) sample =
  toIRInference meta cumulative (Expr ti (IfThenElse cond right left)) sample
toIRInference meta cumulative (Expr _ (IfThenElse cond left right)) sample = do
  var_condT_p <- mkVariable "condT"
  var_condF_p <- mkVariable "condF"
  -- 'cond' is TBool, so its weights are the two sides of a partition. Both
  -- come from one pass over the condition ('condWeights'): a condition that is
  -- itself a Bool if (or a not of one) is built from its children's own
  -- pairs, so its False weight is the semiring's combine over its False
  -- derivations, and a leaf condition derives its False weight as the
  -- semiring complement of its True weight where that is sound. Compiling
  -- the condition once per polarity instead doubled the work at every
  -- nesting level (fuzz-qc-compiler-bugs item 3: an O(2^d) compile of a
  -- depth-d chain of nested Bool conditions); deriving every False weight as
  -- @1 - p(True)@ was linear but holds only under sum-product, and gave
  -- max-product @1 - max@ for a nested condition (task
  -- map-semiring-complement-and-cdf-wrong). rDim is carried over from each
  -- weight. A leaf's False weight is "certain minus p(cond=True)" in the
  -- semiring's sense ('mixWith' of 'srComplement'), not a bare 1 - p: when the
  -- True outcome is itself a density -- a continuous @x == c@, a null event
  -- reported at dim > 0 -- the False branch carries the whole unit mass at dim
  -- 0 (task sampling-matches-pdf-continuous-equality-density). The pair
  -- nodes' weights are lower bounds under topK, so the condition is compiled
  -- pruned; only the complemented leaves compile 'unpruned'.
  let sr = semiringOf meta
  (condTrue, condFalseMix) <- condWeights meta cond
  let condTrueExpr  = unP (rProb condTrue)
  let condFalseExpr = unP (rProb condFalseMix)
  -- Every later read of a condition weight reads its binding: the raw
  -- 'condTrueExpr' is the condition's whole probability field, and the arm
  -- guards and branch-count checks below read it three to four times (task
  -- presult-unbound-block-copied-per-field).
  let condTrueV  = IRVar var_condT_p
      condFalseV = IRVar var_condF_p
  let condFalse = mkPResult (sealP condFalseExpr) (rDim condFalseMix) const0
                          (IROp OpEq condFalseV (srZero sr))
  setVariables [(var_condT_p, condTrueExpr), (var_condF_p, condFalseExpr)]

  -- The arm is weighted by the condition's probability -- an independent factor,
  -- so 'prodP'. The branch count is the exception to the product rule: both arms
  -- share ONE condition, so its count is added once, below, and each arm carries
  -- only its own count through the product.
  let weighByCond v condRes armRes =
        onBranches (const (rBranches armRes))
          (prodP sr (mkPResult (sealP (IRVar v)) (rDim condRes) const0 (rImposs condRes)) armRes)
  -- Whether the condition's own probability is (approximately) the semiring
  -- zero ('deadWeightIR'). Comparing against the literal 0.0 here would
  -- falsely treat every log-space arm as live (a log probability is
  -- essentially never exactly 0.0).
  let deadArm = deadWeightIR sr
  let liveArm = notIR . deadArm
  -- Each arm is zero-checked with the same IRIf short-circuit the probability
  -- fields use, so a dead arm's count -- and any recursive call inside it --
  -- is never evaluated. That is what makes a recursive program's branch count
  -- terminate at all (task bc-recursive-prob-divergence).
  let zeroCheckBC c bc = IRIf (deadArm c) const0 bc

  let rt = rType (getTypeInfo left)
  case rt of
    -- Arrow-typed arms: each arm's compiled 'rProb' is itself a CLOSURE (see
    -- the 'Lambda' equation two cases up -- 'detP (IRLambda name irTuple)'),
    -- not a scalar, so weighing it by the condition's probability ('prodP')
    -- or summing the two arms ('mixP') is arithmetic on a function value --
    -- exactly the crash task arrow-lifted-mixture-for-function-values exists
    -- to fix ("Mult can only multiply numbers ...: VClosure"). Lift the
    -- combinators pointwise instead of applying them to the closures
    -- directly: mix(p_c, t, g) == \z -> mix(p_c, unpack(t z), unpack(g z)).
    -- Build a NEW closure over a fresh argument 'z' whose body, once applied,
    -- reduces to the ordinary scalar mixture of each arm's own
    -- (prob, dim, bc, imposs) AT that point -- ordinary, because opening a
    -- closure at one concrete 'z' always yields a plain value's PResult (a
    -- still-arrow-typed result, i.e. a curried multi-argument mixture,
    -- recurses through this very equation the next time IT is combined --
    -- not handled here; see task callee-normalize-curried-and-accessor-gaps
    -- and the arrow-lift task's own declined-scope note).
    --
    -- topK pruning is NOT implemented for this path: the pruned selection
    -- above picks among three PRE-COMPUTED packed alternatives, and here the
    -- "alternative" only exists once applied to an argument that isn't known
    -- yet. Always computing the exact (unpruned) mixture is a strict
    -- refinement of what topK would have approximated -- never a regression
    -- from the pre-fix behaviour of crashing outright -- so 'thr' is simply
    -- not consulted on this branch.
    TArrow _ _ -> do
      let metaTrue  = meta { accProb = srTimes sr (accProb meta) (IRVar var_condT_p) }
      let metaFalse = meta { accProb = srTimes sr (accProb meta) (IRVar var_condF_p) }
      trueClosure  <- toIRInference metaTrue  cumulative left  sample
      falseClosure <- toIRInference metaFalse cumulative right sample
      zVar <- mkVariable "argZ"
      closureBody <- scoped (do
        trueCallV  <- mkVariable "armTcall"
        falseCallV <- mkVariable "armFcall"
        let trueBind  = (trueCallV,  IRApply (unP (rProb trueClosure))  (IRVar zVar))
            falseBind = (falseCallV, IRApply (unP (rProb falseClosure)) (IRVar zVar))
        -- Let-bind each arm's application ONCE (mirroring the ReadNN/curried-
        -- call-spine idiom elsewhere in this module) rather than calling
        -- 'unpackResult' directly on the raw 'IRApply': that destructures its
        -- argument into four separate projections, which would otherwise
        -- inline four copies of a call that may itself be an arbitrarily
        -- expensive (or recursive) sub-inference. 'closeResult' places the
        -- binding inside the dead-arm guard below, so a call whose condition
        -- cannot hold is still never evaluated.
        trueAtZ  <- closeResult sr "armTz" [liveArm condTrueV]  (openWith [trueBind]  (unpackResult trueCallV))
        falseAtZ <- closeResult sr "armFz" [liveArm condFalseV] (openWith [falseBind] (unpackResult falseCallV))
        let weighedTrue  = weighByCond var_condT_p condTrue  trueAtZ
            weighedFalse = weighByCond var_condF_p condFalse falseAtZ
            branchesZ = IROp OpPlus (zeroCheckBC condTrueV  (rBranches weighedTrue))
                                    (zeroCheckBC condFalseV (rBranches weighedFalse))
        mixP sr branchesZ weighedTrue weighedFalse) <&> generateLetInBlock meta
      return (detP (IRLambda zVar closureBody))
    _ -> do
      -- p(y) = if p_cond < thresh then p_else(y) * (1-p_cond(y)) else if p_cond > 1 - thresh then p_then(y) * p_cond(y) else p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
      let thr = topKThreshold (compilerConfig meta)
      -- We need to restart the monad stack, because variables inside the branches may not be valid outside
      -- E.g. if length(a) > 0 then a[0] else ...
      -- If we were to access a[0] outside of the branch we would error
      mul1Raw <- scoped (do
        let metaTrue = meta { accProb = srTimes sr (accProb meta) (IRVar var_condT_p) }
        weighByCond var_condT_p condTrue <$> toIRInference metaTrue cumulative left sample)
      mul2Raw <- scoped (do
        let metaFalse = meta { accProb = srTimes sr (accProb meta) (IRVar var_condF_p) }
        weighByCond var_condF_p condFalse <$> toIRInference metaFalse cumulative right sample)
      -- If probability of this branch is 0 then set the product to 0 manually. This branch could throw an error multiplied by 0
      -- A condition that cannot hold makes its arm an impossible event, which is
      -- exactly what the mixture below needs to know to drop it -- so record it
      -- rather than leaving the zeroed product to be recognised numerically.
      -- The check is the arm block's guard (see 'closeResult'), so an arm whose
      -- condition cannot hold is never evaluated -- it may hold the recursive call
      -- the check exists to skip.
      mul1Zeroed <- closeResult sr "armT" [liveArm condTrueV] mul1Raw
      mul2Zeroed <- closeResult sr "armF" [liveArm condFalseV] mul2Raw
      let leftBranchesExpr  = rBranches mul1Zeroed
      let rightBranchesExpr = rBranches mul2Zeroed
      -- Dispatching is free: a node that delegates to sub-computations contributes
      -- no branch of its own, so the count is the sum of whichever arms were
      -- actually alive -- no term for evaluating the condition, and no -1 wash.
      -- (The previous formula, cond + left + right - 1, telescoped to left + right
      -- only because every condition tested so far happened to be leaf-shaped with
      -- its own count of exactly 1; a compound condition -- a nested if, a call --
      -- inflated the parent by its dispatch cost for no principled reason. Every
      -- other combinator here -- the enumerated sum, toIREnumerate, the topK dispatch --
      -- already sums surviving children and adds nothing for dispatching.)
      let branches = IROp OpPlus (zeroCheckBC condTrueV  leftBranchesExpr)
                                 (zeroCheckBC condFalseV rightBranchesExpr)
      addRes <- mixP sr branches mul1Zeroed mul2Zeroed
      case thr of
        Just _ -> do
          -- Pick among the three whole packed results ONCE, bound to a single
          -- variable, rather than wrapping each of the four PResult fields in
          -- its own copy of the accTrue/accFalse IRIf (the previous shape):
          -- that field-wise wrapping is exactly the duplication pattern
          -- 'closeResult' exists to avoid (see its docs) -- here it wasn't
          -- routed through closeResult at all, so it re-embedded mul1Zeroed's/
          -- mul2Zeroed's/addRes's own fields FOUR times per level. Since this
          -- whole 'IfThenElse' case can itself be 'cond' of an enclosing
          -- topK-guarded IfThenElse, that 4x-per-level duplication compounds
          -- with nesting depth into an exponential blowup independent of (and
          -- compounding on top of) the condTrue/condFalse fix above
          -- (fuzz-qc-compiler-bugs item 3: nested topK-guarded conditions timed
          -- out well before the plain default-config case did).
          accTrueV <- mkVariable "accTrue"
          accFalseV <- mkVariable "accFalse"
          setVariables [(accTrueV, srTimes sr (accProb meta) (IRVar var_condT_p))]
          setVariables [(accFalseV, srTimes sr (accProb meta) (IRVar var_condF_p))]
          prunedV <- mkVariable "pruned"
          let prunedExpr = IRIf
                (IROp OpLessThan (IRVar accTrueV) (IRVar topKCutoffParamName))
                (packResult mul2Zeroed)
                (IRIf (IROp OpLessThan (IRVar accFalseV) (IRVar topKCutoffParamName))
                  (packResult mul1Zeroed)
                  (packResult addRes))
          setVariables [(prunedV, prunedExpr)]
          return (unpackResult prunedV)
        -- p(y) = p_then(y) * p_cond(y) + p_else(y) * (1-p_cond(y))
        Nothing -> return addRes
-- A comparison against a deterministic bound under a semiring that does not
-- conserve probability ('srConserves', max-product): the fixed-bound
-- equations below answer the upper tail as the complement of the operand's
-- CDF, which is the upper tail's weight only when that CDF is a single
-- derivation's ('singleDerivation'). An operand with several derivations
-- (an enumerated sum, an @if@) has a CDF that is already their combine, and
-- @1 - max@ is not the best derivation above the bound (task
-- map-semiring-complement-and-cdf-wrong: @a + b > 0@ over two Bernoulli(0.5)
-- indicators answered 0.75 for the best derivation's 0.25). Such an operand
-- is summed over its enumerated domain instead, in the compile's semiring,
--
--   p(cmp = sample) = (+) over v in dom(X) of p(X = v) (x) [cmp(v, bound) = sample]
--
-- and refused when it has no domain within the materialization budget.
toIRInference meta False (Expr _ (InjF (Named cmp) [left, right])) sample
  | cmp `elem` ["gt", "lt"]
  , not (srConserves (semiringOf meta))
  , [randE] <- filter (\x -> pType (getTypeInfo x) /= Deterministic) [left, right]
  , not (singleDerivation randE) = do
    let sr = semiringOf meta
        randLeft = pType (getTypeInfo right) == Deterministic
        detE = if randLeft then right else left
        rtgs = tags (getTypeInfo randE)
    case enumerableDomain rtgs of
      Just dom | enumerationWithinMaterializationBudget meta rtgs -> do
        bnd <- mkVariable "cmp_bound"
        d <- toIRGenerate meta detE
        setVariables [(bnd, d)]
        v <- mkVariable "cmp_value"
        mTbl <- materializeOperandTable meta randE
        let op = if cmp == "gt" then OpGreaterThan else OpLessThan
            holds = if randLeft then IROp op (IRVar v) (IRVar bnd) else IROp op (IRVar bnd) (IRVar v)
        summandO <- scoped $ do
          pV <- operandProb meta mTbl randE (IRVar v)
          return (IRIf (equalityGuard TBool holds sample) pV (srZero sr))
        let (outerBinds, body') = hoistInvariantBindings v (closeExpr summandO id)
        setVariables outerBinds
        opaqueMass sr (enumSumNode sr v dom body') const0
      _ -> refuse (chainName (getTypeInfo randE))
             ("a comparison's upper tail under a semiring without complements (max-product) "
              ++ "needs an operand with a single derivation or a finite enumerated domain")
-- Both sides Gaussian: left - right ~ Normal(muL - muR, sqrt(sL^2 + sR^2)), so the
-- comparison is that difference's CDF evaluated at 0. Neither side is Deterministic,
-- so the bound-based equations below do not apply. resolveCompCons types this Bool
-- as Integrate (a closed-form discrete probability), matching the dim-0 result here.
toIRInference meta False (Expr _ (InjF (Named "gt") [left, right])) sample
  | pType (getTypeInfo left) == PNormal && pType (getTypeInfo right) == PNormal = do
    cdfAt0 <- normalDiffCdfAtZero meta left right
    -- p(left > right) = p(diff > 0) = 1 - cdf(0), spelled through
    -- 'complementWhen' so the upper tail keeps its precision
    mass <$> complementWhen (semiringOf meta) sample cdfAt0
toIRInference meta False (Expr _ (InjF (Named "lt") [left, right])) sample
  | pType (getTypeInfo left) == PNormal && pType (getTypeInfo right) == PNormal = do
    cdfAt0 <- normalDiffCdfAtZero meta left right
    -- p(left < right) = p(diff < 0) = cdf(0)
    mass <$> complementWhen (semiringOf meta) (notIR sample) cdfAt0
toIRInference meta False (Expr _ (InjF (Named "gt") [left, right])) sample
  | pType (getTypeInfo left) == Deterministic = do --p(x | const > var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate meta left
    setVariables [(var, strictBelowBound right l)]
    integ <- toIRInference (unpruned meta) True right (IRVar var)  -- complemented below, see 'unpruned'
    -- 'complementWhen' rather than a let-bound CDF and its complement, so a
    -- normal upper tail keeps its precision ('upperTailComplement')
    returnExpr <- complementWhen (semiringOf meta) (notIR sample) (unP (rProb integ))
    -- A comparison's mass, not a structural choice: possible either way.
    return (mkPResult (sealP returnExpr) dim0 (rBranches integ) constFalseIR)
  | pType (getTypeInfo right) == Deterministic = do --p(x | var >= const)
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate meta right
    setVariables [(var, r)]
    integ <- toIRInference (unpruned meta) True left (IRVar var)  -- complemented below, see 'unpruned'
    -- 'complementWhen' rather than a let-bound CDF and its complement, so a
    -- normal upper tail keeps its precision ('upperTailComplement')
    returnExpr <- complementWhen (semiringOf meta) sample (unP (rProb integ))
    -- A comparison's mass, not a structural choice: possible either way.
    return (mkPResult (sealP returnExpr) dim0 (rBranches integ) constFalseIR)
toIRInference meta False (Expr _ (InjF (Named "lt") [left, right])) sample
  | pType (getTypeInfo left) == Deterministic = do --p(x | const >= var)
    var <- mkVariable "fixed_bound"
    l <- toIRGenerate meta left
    setVariables [(var, l)]
    integ <- toIRInference (unpruned meta) True right (IRVar var)  -- complemented below, see 'unpruned'
    -- 'complementWhen' rather than a let-bound CDF and its complement, so a
    -- normal upper tail keeps its precision ('upperTailComplement')
    returnExpr <- complementWhen (semiringOf meta) sample (unP (rProb integ))
    -- A comparison's mass, not a structural choice: possible either way.
    return (mkPResult (sealP returnExpr) dim0 (rBranches integ) constFalseIR)
  | pType (getTypeInfo right) == Deterministic = do --p(x | var < const)
    var <- mkVariable "fixed_bound"
    r <- toIRGenerate meta right
    setVariables [(var, strictBelowBound left r)]
    integ <- toIRInference (unpruned meta) True left (IRVar var)  -- complemented below, see 'unpruned'
    -- 'complementWhen' rather than a let-bound CDF and its complement, so a
    -- normal upper tail keeps its precision ('upperTailComplement')
    returnExpr <- complementWhen (semiringOf meta) (notIR sample) (unP (rProb integ))
    -- A comparison's mass, not a structural choice: possible either way.
    return (mkPResult (sealP returnExpr) dim0 (rBranches integ) constFalseIR)
-- A comparison against a random but enumerable bound (task
-- uniform-below-random-threshold-no-forward): a Bernoulli whose rate is
-- itself random, @Uniform < (if b then 0.9 else 0.1)@ once DrawSinking has
-- moved @draw b@ into the threshold. Neither side is Deterministic, so the
-- two equations above do not apply, and the other side has no
-- 'DiscreteValues' domain, so the enumerate-both grid does not either. The
-- operands are independent ('enumeratedBoundShape'), so
--
--   p(cmp = sample) = sum over v in dom(E) of P(E = v) * p(cmp against v = sample)
--
-- where the inner factor is exactly the fixed-bound equation's: the other
-- side's CDF at @v@, complemented when the outcome asks for its upper tail.
-- ModalityInfer's 'compareGround' admits this shape under the same
-- conditions, and this equation must not outrun it.
toIRInference meta False (Expr _ (InjF (Named cmp) [left, right])) sample
  | cmp `elem` ["gt", "lt"]
  , Just (enumLeft, enumE, cdfE) <- enumeratedBoundShape meta left right = do
    let sr = semiringOf meta
    let enumList = head [x | DiscreteValues x <- tags (getTypeInfo enumE)]
    -- The CDF side lies below the bound when it is the left operand of @<@
    -- or the right operand of @>@; the True outcome is then its CDF, and
    -- the False outcome the complement (and the other way round otherwise).
    let cdfBelow = (cmp == "lt") /= enumLeft
    -- The CDF side is complemented below: under max-product only a single
    -- derivation's CDF has its complement as its upper tail (see the
    -- non-conserving fixed-bound equation above).
    when (not (srConserves sr) && not (singleDerivation cdfE)) $
      refuse (chainName (getTypeInfo cdfE))
        ("a comparison's upper tail under a semiring without complements (max-product) "
         ++ "needs an operand with a single derivation")
    bnd <- mkVariable "enumerated_bound"
    mTbl <- materializeOperandTable meta enumE
    returnO <- scoped $ do
      pE <- operandProb meta mTbl enumE (IRVar bnd)
      let cdfAt = if cdfBelow then strictBelowBound cdfE (IRVar bnd) else IRVar bnd
      integ <- toIRInference (unpruned meta) True cdfE cdfAt  -- complemented below, see 'unpruned'
      pCmp <- complementWhen sr (if cdfBelow then notIR sample else sample) (unP (rProb integ))
      return (srTimes sr pE pCmp)
    let (outerBinds, body') = hoistInvariantBindings bnd (closeExpr returnO id)
    setVariables outerBinds
    opaqueMass sr (enumSumNode sr bnd enumList body') const0
-- The run-time twin of the Dirac-law clause ('lawPoint') (task
-- helper-parameter-zero-factor-answers-nan): a deterministic factor that is
-- not statically known nonzero -- a helper's parameter, say -- can still be
-- zero when the product runs, and then the product is the same point mass,
-- while the inversion below divides by it (its applicability guard found every
-- value impossible). Branch on it: the point mass when it is zero, and the
-- ordinary compile, recorded in 'zeroGuardedProducts' so it does not branch
-- again, otherwise. A Gaussian product never gets here: the PNormal clause
-- above compiles it, and 'degenerateScaleGuard' handles its zero scale.
toIRInference meta cumulative e@(Expr TypeInfo {rType=rt, chainName=cn} (InjF (Named name) [left, right])) sample
  | name `elem` ["mult", "multI"]
  , Just factor <- runtimeZeroFactor left right
  , not (cn `Set.member` zeroGuardedProducts meta) = do
      f <- toIRGenerate meta factor
      v <- mkVariable "factor"
      setVariables [(v, f)]
      let sr = semiringOf meta
          zero = IRConst (valueToIR (zeroValueOf rt))
          isZero = IROp OpEq (IRVar v) zero
          dirac | cumulative = mass (compareValueExpr sr rt zero sample)
                | otherwise  = indicatorP sr (equalityGuard rt zero sample)
          meta' = meta { zeroGuardedProducts = Set.insert cn (zeroGuardedProducts meta) }
      rest <- guardedSubInference meta [notIR isZero] (toIRInference meta' cumulative e sample)
      return (zipResult (IRIf isZero) dirac rest)
-- The CDF of a neural read (task neural-int-read-cdf-returns-pmf). The
-- network's _auto_prob is a point mass, so the cumulative query sums it over
-- the read's enumerated domain, each value weighted by whether it lies at or
-- below the sample ('compareValueExpr'):
--
--   P(X <= x) = sum over v in dom(X) of P(X = v) * [v <= x]
--
-- in the compile's semiring. The point clause below used to answer both
-- queries, returning P(X = x). A read with a continuous leaf has no such sum
-- and is refused; a bare Bool read never gets here (the Boolean CDF split
-- above), nor does a Gaussian-headed one ('gaussianLeaf').
toIRInference meta True e@(Expr TypeInfo {rType=rt, tags=tgs, chainName=cn} (ReadNN name _)) sample =
  case enumerableDomain tgs of
    Just dom | enumerationWithinMaterializationBudget meta tgs -> do
      let sr = semiringOf meta
      v <- mkVariable "nn_cdf_value"
      summandO <- scoped $ do
        pV <- (unP . rProb) <$> toIRInference meta False e (IRVar v)
        return (srTimes sr pV (compareValueExpr sr rt (IRVar v) sample))
      let (outerBinds, body') = hoistInvariantBindings v (closeExpr summandO id)
      setVariables outerBinds
      opaqueMass sr (enumSumNode sr v dom body') const0
    _ -> refuse cn ("cannot compute the cumulative distribution of the neural read '" ++ name
                    ++ "': its domain is not a finite enumeration within the materialization budget")
toIRInference meta _ (Expr _ (ReadNN name symbol)) sample = do
  nnRaw <- mkVariable "nn_raw"
  var <- mkVariable "callNN"
  sym <- toIRGenerate meta symbol
  setVariables [(nnRaw, IRApply (IRVar name) sym)]
  setVariables [(var, IRApply (IRApply (IRVar (name ++ "_auto_prob")) (IRVar nnRaw)) sample)]
  -- Not a leaf: the network's own _auto_prob function already packed a triple.
  return (unpackResult var)
toIRInference meta cumulative (Expr t (Lambda name subExpr)) sample = do
  let newMeta = extendMetaForLambda meta t name
  irTuple <- scoped (toIRInference newMeta cumulative subExpr sample) <&> generateLetInBlock meta
  return (detP (IRLambda name irTuple))
-- Deterministic lambda and bound expression PDF
toIRInference meta False (Expr TypeInfo{rType=rt} (Apply l v)) sample | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  lIR <- toIRGenerate meta l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (detP (IRApply lIR vIR))
    _ ->
      -- A leaf resolution: a deterministically-known value compared against the
      -- sample, exactly as the 'Constant'/'ThetaI' cases do, so it counts as one
      -- branch like they do ('indicatorP', not 'detP' -- which is reserved for
      -- results that produce no value at all, i.e. closures). See the leaf-anchor
      -- note on the 'Var'-is-a-local-variable case below.
      --
      -- Compared by 'equalityGuard', as every other deterministic leaf is: a
      -- bare 'OpEq' compared a float leaf bit-exactly and read a nested ANY
      -- (@(3.0, (ANY, 2.0))@ against @draw z = (1.0, 2.0) in (3.0, z)@) as a
      -- mismatch. Rare while a @draw@ over a recovered variable kept its
      -- stale random type; common once re-inference types it Deterministic
      -- (task reinfer-body-under-recovered-bindings). Bound once, since the
      -- guard reads the value per field.
      do
        applied <- mkVariable "det_app"
        return (indicatorP (semiringOf meta)
                  (IRLetIn applied (IRApply lIR vIR) (equalityGuard rt (IRVar applied) sample)))
-- Deterministic lambda and bound expression CDF
toIRInference meta True (Expr TypeInfo{rType=rt} (Apply l v)) sample | pType (getTypeInfo l) == Deterministic && pType (getTypeInfo v) == Deterministic = do
  vIR <- toIRGenerate meta v
  lIR <- toIRGenerate meta l -- Dim and BC are irrelevant here
  -- The result is not a tuple if the return value is a closure
  case rt of
    TArrow _ _ -> return (detP (IRApply lIR vIR))
    _ ->
      return (mass (compareValueExpr (semiringOf meta) rt (IRApply lIR vIR) sample))
-- Enumerable conditional lambda applied to a probabilistic discrete argument:
-- enumerate the argument's discrete support and weight each value by its probability,
-- compiling the body via toIREnumerate. The body need not be deterministic given the
-- bound variable -- toIREnumerate recurses into further enumerable applications
-- (nested enumerable `let`s), so this rule no longer requires `pType l == Deterministic`.
-- Gated on the materialization budget (task of-annotation-forces-dense-enumeration):
-- this arm materializes the argument's whole support, and it is the FIRST matching
-- 'Apply' equation, so an `of` annotation alone used to force dense enumeration and
-- make the plan-guided lazy path below unreachable -- a 423x pessimization on an
-- otherwise identical program. The budget that already bounds Tier-0 marginal
-- materialization now bounds this too; over budget, the equation declines and
-- dispatch falls through to the plan-guided arm ('planWitnessApply'), which
-- factorizes over the 'PartitionPlan' slots without ever materializing the support.
-- Under budget nothing changes: every program the suite already routes here still
-- routes here, so this is strictly a refusal to blow up, not a reordering.
-- Since every read is tagged with its resolved annotation, written or not (task
-- of-annotation-and-auto-derived-enumeration-divergence), this order -- dense
-- first, plan above the budget -- holds for every neural read alike.
-- A stack of enumerable draws over a field constructor whose operands fall
-- into independent groups: the product of the groups' own enumerations
-- ('drawStack'), instead of one joint loop over every draw.
toIRInference meta cumulative e@(Expr _ (Apply _ _)) sample
  | Just ds <- drawStack meta e = factoredDrawStack meta cumulative ds sample
toIRInference meta cumulative (Expr TypeInfo {rType=_} (Apply l v)) sample
  | isEnumerableApplication meta l v
  , enumerationWithinMaterializationBudget meta (tags (getTypeInfo v))
  , calleeBodyInScope meta l =
  -- The agreement fusion (task categorical-product-ov-fusion) is tried first
  -- and answers 'Nothing' for everything it does not recognise or will not
  -- take, so the ordinary joint enumeration stays the default path.
  case agreementShape meta l v of
    Just ag -> enumerateAgreement meta cumulative ag sample
    Nothing -> enumerateAppliedLambda meta cumulative l v sample
-- A conditional top-level function applied, through a curried spine, to
-- deterministic leading arguments and a probabilistic enumerable last one:
-- @match c (readAttrs s)@ with @c@ fixed. Marginalise the last argument
-- exactly as the one-argument equation above does ('enumerateCurriedArgument').
-- The leading arguments are read with the enclosing enumerated latents fixed,
-- which is what makes the shared-latent spelling
-- @draw c = readQ q in match c (readAttrs s1) ++ match c (readAttrs s2)@
-- compile per slot inside the loop over @c@ (task
-- shared-enumerated-latent-loses-per-slot-factorization).
toIRInference meta cumulative (Expr ti (Apply l v)) sample
  | Just l' <- curriedEnumerableCallee meta l v
  , enumerationWithinMaterializationBudget meta (tags (getTypeInfo v)) =
  enumerateCurriedArgument meta cumulative (\x -> Expr ti (Apply l' x)) v sample
-- Deterministic curried call spine rooted at a known top-level function: build
-- the WHOLE application (the query sample, plus every source-level argument)
-- as one contiguous 'IRApply' chain and let-bind it exactly once, instead of
-- recursing per 'Apply' node -- which is what the general "Deterministic
-- bound expression" case below does, and which let-binds the callee's partial
-- application (awaiting the remaining curried arguments) *before* applying
-- the rest of the spine to it.
--
-- That per-level split is invisible at the default -O, where the let-inliner
-- collapses the single-use intermediate bindings back into one spine before
-- codegen ever sees it. At -O0 nothing does, so codegen is handed
-- @let c0 = f_prob(sample) in c0(x)@: a *contiguous* 'IRApply' spine is what
-- the scalar backends flatten into one @f_prob(sample, x)@ call site
-- ('IROptimizer.unconditionalAnns' states the same invariant, from the CSE
-- side, for why it refuses to hoist a partial spine), and a spine broken
-- across a let is exactly what that flattening cannot see through. Julia
-- calls a partial application as if it were the fully-applied one-argument
-- function and gets an arity 'MethodError'; Python would raise 'TypeError'
-- for the same reason (task
-- curried-call-spine-needs-optimizer-to-typecheck).
--
-- Guarded to the shapes this can handle soundly: every argument in the spine
-- must be Deterministic (a probabilistic argument needs inversion machinery,
-- handled by the existing per-argument cases below, which this equation
-- leaves untouched since its guard then fails), and the spine's head must be
-- a bare reference to a top-level function -- matching exactly the case the
-- 'Var' equation further down would otherwise have let-bound as the spine's
-- first, innermost partial call.
toIRInference meta cumulative expr@(Expr TypeInfo{rType=rt} (Apply _ _)) sample
  | (Expr _ (Var n), args@(_:_)) <- flattenApplySpine expr
  , all ((== Deterministic) . pType . getTypeInfo) args
  , Just (TArrow _ _, hasInference) <- lookup n (typeEnv meta) = do
      argIRs <- mapM (toIRGenerate meta) args
      name <- if hasInference then calleeInferenceName meta cumulative n else return n
      let base = if hasInference
            then inferenceCall meta cumulative (IRVar name) sample
            else IRApply (IRVar name) sample
      let wholeCall = foldl IRApply base argIRs
      case rt of
        TArrow _ _ -> return (detP wholeCall)
        _ -> do
          retVal <- mkVariable "call"
          setVariables [(retVal, wholeCall)]
          return (unpackResult retVal)
-- A dead binding of a function value: the body never reads it, so it is
-- compiled alone, exactly as the scalar arm below does at its own
-- 'deadBindingBodyCN' check. The arms next would generate the argument (the
-- deterministic one) or the whole callee (the random one): @draw f = snd
-- (Normal, \x -> Uniform) in (\x -> Uniform) c@ -- CalleeNormalize's rewrite
-- of a projected callee, leaving @f@ unread -- generated the discarded Normal,
-- and the probability was refused as generate-backed
-- (fuzz-admission-oracle-bugs item 2).
toIRInference meta cumulative (Expr _ (Apply l v)) sample
  | isTArrowType (rType (getTypeInfo v))
  , Just deadBody <- deadBindingBody meta l =
  toIRInference meta cumulative deadBody sample
-- Deterministic bound expression
toIRInference meta cumulative expr@(Expr TypeInfo{rType=rt} (Apply l v)) sample | pType (getTypeInfo v) == Deterministic = do
  let viaCallee = do
        vIR <- toIRGenerate meta v
        lIR <- (unP . rProb) <$> toIRInference meta cumulative l sample -- Dim and BC are irrelevant here. We need to extract these from the return tuple
        let applied = IRApply lIR vIR
        -- The result is not a tuple if the return value is a closure
        case rt of
          TArrow _ _ -> return (detP applied)
          _ -> do
            retVal <- mkVariable "call"
            setVariables [(retVal, applied)]
            return (unpackResult retVal)
  -- A call whose earlier argument is random, @obs b p@ with @b@ random: the
  -- callee applied to its leading arguments is a closure whose body reads a
  -- parameter bound to a random argument, which the arms compiling @l@ alone
  -- refuse. Where they do, that argument is bound first, in parameter order
  -- ('leadingArgBinding'), as for a random last argument. Tried second, so a
  -- call they answer keeps its emitted code.
  leading <- if cumulative then return Nothing else leadingArgBinding meta expr
  let viaBinding = case leading of
        Nothing -> viaCallee
        Just b -> do
          first <- (Right <$> scoped viaCallee) `catchError` (return . Left)
          case first of
            Right o -> inline o
            Left _ -> applyBinding meta cumulative rt b sample
  -- The call's one random argument, in a leading position and enumerable
  -- (@cont (trans fog) n@), is marginalised over its domain as a random last
  -- argument is ('enumerateCurriedArgument'), where the arms above refuse:
  -- the binding engines none enumerate a finite domain, so which refusal a
  -- call met depended on where its author put the random parameter (task
  -- random-leading-argument-into-recursion-refused). Tried last, so a call
  -- they answer keeps its emitted code; where all refuse, the enumeration's
  -- own refusal is the one reported. Not for the cumulative variant, which
  -- the binding path does not take either: there it would admit integrate
  -- variants that were absent before (corpus observePredicateParameterLambda),
  -- which batched mode cannot tensorize. Both restrictions work around
  -- symptoms and are not design choices. The engine order now depends on the
  -- argument's position, and nested leading calls compile in exponential time
  -- through these retries. Docs-repo tasks
  -- leading-argument-enumeration-as-binding-engine and
  -- nested-leading-random-argument-compile-exponential.
  case leadingEnumerableArgument meta expr of
    Just (mkBody, ai) | not cumulative
                      , enumerationWithinMaterializationBudget meta (tags (getTypeInfo ai)) -> do
      first <- (Right <$> scoped viaBinding) `catchError` (return . Left)
      case first of
        Right o -> inline o
        Left _ -> enumerateCurriedArgument meta False mkBody ai sample
    _ -> viaBinding
-- Probabilistic bound expression
toIRInference meta cumulative (Expr TypeInfo{rType=rt, chainName=_} (Apply l v)) sample | isTArrowType (rType (getTypeInfo v)) && (pType (getTypeInfo v) == Integrate || pType (getTypeInfo v) == PNormal || pType (getTypeInfo v) == PLogNormal) = do
  lIR <- toIRGenerate meta l
  vIR <- (unP . rProb) <$> toIRInference meta cumulative v sample
  -- The result is not a tuple if the return value is a closure, as in the
  -- deterministic arms above: @app g x@ with @g@ random reaches here as
  -- @(app g) x@, and @app g@ is a function still awaiting @x@. Unpacking it
  -- projected @fst@ out of a closure (task
  -- named-hof-random-function-argument-miscompiled); the enclosing
  -- application applies it and unpacks the PResult it then returns.
  case rt of
    TArrow _ _ -> return (detP (IRApply lIR vIR))
    _ -> do
      applied <- mkVariable "call"
      setVariables [(applied, IRApply lIR vIR)]
      return (unpackResult applied)
toIRInference meta cumulative expr@(Expr TypeInfo{rType=rt, chainName=_} (Apply l v)) sample | pType (getTypeInfo v) == Integrate || pType (getTypeInfo v) == PNormal || pType (getTypeInfo v) == PLogNormal = do
  -- This is the probabilistic inference of a known, deterministic lambda with a probabilistic parameter
  -- The inference looks like this: p(l(v) == sample) = p(l^-1(sample) == v)
  -- The inverse can not be created using recursive descend, therefor we use forward chaining for the inverse only
  -- Chain name of the callable
  let lChainName = chainName (getTypeInfo l)

  -- This logic is here to wrap the expression back into lambdas if the lambda we look at returns a lambda
  -- A callee forward chaining cannot resolve to a lambda is a shape this arm
  -- does not support, not a broken invariant: CalleeNormalize reduces the
  -- selections it knows (projections, an @if@, a redex), and anything it does
  -- not reach is refused rather than crashing the compile.
  case findEquivalentExpression (fcData meta) lChainName of
    Just (_, LambdaInfo{}, _) -> return ()
    other -> refuse lChainName ("the callee of this application does not resolve to a lambda the compiler can see"
                                ++ " (it resolved to " ++ show other ++ "); a function value selected some other way"
                                ++ " than by a projection, an if, or a redex is not supported here")
  let binding0 = resolveBinding meta l v

  -- Dead binding: if the bound variable never appears in the body, the body is independent
  -- of the argument. In that case p(result = sample) = p(body = sample).
  -- Scoped to THIS lambda's body: a same-named variable bound elsewhere must not count.
  -- 'deadBindingBodyCN' is the shared predicate; the Bottom-argument arm below asks it
  -- too, so a dead binding compiles the same way whether or not its argument happens
  -- to have a measurable distribution. It returns this very 'lambdaBodyCN' -- both
  -- resolve l's chain name through 'findEquivalentExpression'.
  let deadBinding = isJust (deadBindingBodyCN meta l)
  if deadBinding then
    toIRInference (withBindingLaw meta binding0 (bindVar binding0)) cumulative (bindBody binding0) sample
  else do
   -- A call whose body reads a leading parameter bound to a random argument
   -- binds that argument first ('leadingArgBinding').
   leading <- if isJust (bindScope binding0) then return Nothing else leadingArgBinding meta expr
   case leading of
     Just _ | cumulative -> refuse lChainName ("cannot compute a cumulative distribution through a call of '"
                 ++ fromMaybe "?" (bindTopLevel binding0) ++ "' binding more than one random argument:"
                 ++ " the slots they reach are correlated, and their joint CDF is not a product of per-slot factors")
     _ -> applyBinding meta cumulative rt (fromMaybe binding0 leading) sample

-- Dead binding over an *intractable* argument. The arms above all require the
-- argument's own pType to be one the compiler can measure (Deterministic, or one
-- of the three probabilistic rungs); a `Bottom` argument matches none of them and
-- used to reach the catch-all below. But a dead binding never reads the value, so
-- the argument's tractability is beside the point: p(result = sample) =
-- p(body = sample), exactly the reduction the probabilistic arm makes at its own
-- `deadBinding` check -- and the same predicate ('deadBindingBodyCN') decides it, so
-- the two agree on branch counts as well as on probability. This is what makes
-- `let x = Uniform * Uniform in Uniform` compile: the binding is unmeasurable and
-- unread, and ModalityInfer types the application by the *body*, so the program as
-- a whole is not Bottom and does get a probability function.
toIRInference meta cumulative (Expr TypeInfo{rType=_} (Apply l _)) sample
  | Just bodyExpr <- deadBindingBody meta l =
  toIRInference meta cumulative bodyExpr sample
-- What is left is an application whose argument has no measurable distribution and
-- whose value the body actually reads. There is no probability to compute: the
-- correct answer would be an integral over the argument's law, which is precisely
-- what `Bottom` says is unavailable. Reaching here is normally impossible --
-- a live occurrence of a Bottom-typed binding makes the body, hence the
-- application, Bottom too, and ModalityInfer then emits no probability function
-- at all -- so this is a diagnostic for a modality/codegen disagreement rather
-- than a user-facing refusal.
toIRInference _ cumulative (Expr TypeInfo{rType=rt, chainName=cnApp} (Apply l v)) _ =
  refuse cnApp ("Cannot compile an application in " ++ (if cumulative then "cumulative" else "probability")
    ++ " mode: the argument has pType " ++ show (pType (getTypeInfo v))
    ++ " (no measurable distribution) and the callee (pType "
    ++ show (pType (getTypeInfo l)) ++ ", chain name '" ++ chainName (getTypeInfo l)
    ++ "') reads its value. Result type: " ++ show rt)
-- Generic inference for multi-field constructor InjFs (Cons, TCons, user-ADT
-- constructors). Each field is independently recoverable from the constructed
-- sample via a deconstructing inverse, so we infer each field against its
-- recovered sub-sample and combine: probabilities multiply, dimensions add,
-- branch counts add. The components are independent, hence product (not the
-- additive PlusConstraint) semantics. Fires for >= 1 probabilistic parameter;
-- the all-deterministic case is handled by the generate-and-compare branch below.
toIRInference meta cumulative (Expr TypeInfo{rType=rt} (InjF (Named name) params)) sample
  | isFieldConstructor (adtDecls meta) name && countProbParams params >= 1 = do
  let resolvedName = resolveInjF rt name
  let localAdts = adtDecls meta
  FPair fwd inversions <- instantiate mkVariable localAdts resolvedName
  let inVars = inputVars fwd
  let outV = soleOutputVar fwd
  -- Inline the sample directly into each inverse body (instead of binding it to
  -- outV) so the optimizer can fold deconstructions like head(prepend(s, ANY))
  -- back to s. A let-binding referenced by every field plus the guard would
  -- survive optimization and force materialising the reconstructed container.
  let inlineSample = irMap (\e -> case e of IRVar n | n == outV -> sample; _ -> e)
  -- Fields are compiled LEFT TO RIGHT rather than independently, threading the
  -- disjunction of the impossibility flags established so far, so that a field
  -- whose predecessors have already ruled this construction out is never
  -- evaluated (task recursive-list-prob-missed-cse, second half). The product
  -- below is impossible as soon as any one factor is ('prodP' ORs the flags),
  -- so a later factor's value cannot affect the answer once an earlier one has
  -- set its flag -- but 'prodP' is an arithmetic combination of already-computed
  -- results, so without this the later factor is computed regardless and only
  -- then multiplied into a product known to be impossible.
  --
  -- This matters exactly where a cheap discriminating field precedes an
  -- expensive one, which is the shape of every branching recursive list: an
  -- 'A : rec' / 'B : rec' mixture compiles each arm as (head indicator, tail
  -- recursion), and the head indicator rules its arm out for all but one
  -- symbol. Unpruned, BOTH arms recurse at every level, doubling the work per
  -- element -- measured at exactly 2.0x/element, i.e. 2^n in list length, on
  -- 'rec = if Uniform < 0.5 then [] else (if Uniform < 0.5 then A : rec else
  -- B : rec)'. This is NOT the duplicate-evaluation bug the first half of that
  -- task fixed (that was one call emitted twice); here the two recursive calls
  -- are distinct and each emitted once, just not pruned by a sample that has
  -- already ruled one out.
  --
  -- The guard is threaded through 'guardedSubInference' -- the same mechanism
  -- the applicability test already uses -- so it is baked INTO the bound value
  -- by 'closeResult' rather than applied to the returned 'PResult' afterwards.
  -- That is what makes it prune rather than merely zero: a shared let-in block
  -- is evaluated where it is bound, so a guard layered on top of the result
  -- would come too late to stop the recursion.
  --
  -- 'rImposs' is taken AFTER guarding, so it already carries this field's own
  -- applicability test and prune guard; a field is thus pruned if any
  -- predecessor was impossible for any reason, not only an indicator mismatch.
  -- An all-constant accumulator adds no guard at all, which is what keeps
  -- cumulative mode untouched: its deterministic fields are 'mass'es with no
  -- impossibility flag, so nothing ever accumulates there.
  let pruneGuards fieldType accImposs
        | accImposs == constFalseIR        = []
        | not (dimZeroByType localAdts fieldType) = []
        | otherwise                        = [notIR accImposs]
  (revFieldResults, _) <- foldM
    (\(acc, accImposs) (inV, p) -> do
      let inv = inversionFor resolvedName inV inversions
      let FDecl {body=invBody, applicability=appT, deconstructing=decons} = inv
      -- Deconstructing inverses need the Any-safe inference variant.
      let probF = if decons then toIRInferenceSave else toIRInference
      let appTExpr = inlineSample appT
      -- A field can be a self-recursive probability call -- the tail of a
      -- recursive list, e.g. 'main = if Uniform>p then [] else X:main'
      -- compiles its tail field exactly here -- so this field's own
      -- computation is isolated and re-guarded on its own applicability test
      -- rather than left in the ambient scope (see 'guardedSubInference').
      fieldRes <- guardedSubInference meta
                    (appTExpr : pruneGuards (rType (getTypeInfo p)) accImposs)
                    (probF meta cumulative p (inlineSample invBody))
      -- Bind the accumulator: an inline field's flag already contains
      -- 'accImposs' (through its prune guard), so the unbound OR would hold
      -- it twice and N fields would copy the first flag 2^N times. Binding
      -- eagerly is safe -- each flag carries its own applicability test, and
      -- the product evaluates every field's flag anyway.
      accV <- case orIR accImposs (rImposs fieldRes) of
        c@(IRConst _) -> return c
        v@(IRVar _)   -> return v
        e             -> do
          accName <- mkVariable "acc_imposs"
          setVariables [(accName, e)]
          return (IRVar accName)
      return ((fieldRes, appTExpr) : acc, accV))
    ([], constFalseIR) (zip inVars params)
  let fieldResults = reverse revFieldResults
  -- The fields are independent, so the whole construction is their product.
  let combined = foldl1 (prodP (semiringOf meta)) (map fst fieldResults)
  -- Guard the result by the conjunction of all field applicability tests (e.g.
  -- the non-empty-list test carried by the Cons inverses).
  let guardCond = foldr1 (IROp OpAnd) (map snd fieldResults)
  return (guardP (semiringOf meta) [guardCond] combined)
toIRInference meta cumulative (Expr ti (InjF (Named name) params)) sample | isHigherOrder (adtDecls meta) name = do
  let localAdts = adtDecls meta
  let resolvedName = resolveInjF (rType ti) name
  -- FPair of the InjF with unique names
  fPair <- instantiate mkVariable localAdts resolvedName
  -- Unary InjF has a single inversion
  inv <- case fPair of
        FPair _ [i] -> return i
        FPair _ is -> refuse (chainName ti) ("Higher-order InjF '" ++ resolvedName ++ "' must declare exactly one inversion, but declares " ++ show (length is))
  let FDecl {inputVars=inVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=derivs} = inv
  --Handle the function being in different positions of the signature
  let aPoss = [0 .. (length params - 1)] \\ getFunctionParamIdx localAdts name
  aPos <- case aPoss of
        [n] -> return n
        x -> refuse (chainName ti) ("Higher-order InjF '" ++ resolvedName ++ "' expects exactly one non-function parameter, but got " ++ show (length x))
  let a = params !! aPos
  let aVar = inVars !! aPos
  let fs = map (params !!) (getFunctionParamIdx localAdts name)
  let fVars = map (inVars !!) (getFunctionParamIdx localAdts name)
  let invDerivExpr = inverseDerivative resolvedName aVar derivs
  -- Set sample value to the variable name in the InjF
  setVariables [(aVar, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Create all inverses of the ho functions and save them on the variable stack
  -- Then create a substitution that substitutes f^-1 to f_prob. All substitutions are then composed in the fold
  renVar <- foldM (\sub tup -> createHOInverse meta tup <&> (.) sub) id (zip fVars fs)
  -- When deconstructing an Either and sample contains a nested VAny (e.g. Left ANY),
  -- arithmetic in invExpr would crash before isAny can fire. Replace invExpr with a
  -- safe alternative (Left VAny / Right VAny) that lets OpEq handle the comparison.
  let renamedInvExpr = renVar invExpr
  let finalInvExpr = case (decons, rType (getTypeInfo a)) of
        (True, TEither _ _) ->
          let deepCheck = mkDeepAnyCheck (TEither undefined undefined) sample
          in IRIf deepCheck (mkSafeInvExpr sample) renamedInvExpr
        _ -> renamedInvExpr
  -- Isolated and re-guarded on appTest (see 'guardedSubInference') so a
  -- shared let-in block from inside 'a's own compilation -- e.g. a
  -- self-recursive probability call -- cannot escape into the ambient
  -- scope ahead of the applicability test 'guardP' applies below.
  -- Unpruned when the cumulative CoV below may flip it through a complement.
  let metaOp = covOperandMeta cumulative invDerivExpr meta
  paramRes <- guardedSubInference metaOp [appTest] (probF metaOp cumulative a finalInvExpr)
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula
  return (substResult renVar (guardP (semiringOf meta) [appTest] (scaleCoV (semiringOf meta) cumulative invDerivExpr paramRes)))
-- A function value computed by an InjF with no probabilistic operand --
-- @head ((\v3 -> [\v4 -> Uniform]) 1.0)@, @left (\r1 -> ..)@ -- would be
-- answered by the two leaf equations below, which generate the value and
-- compare it against the sample. A function is not a value a sample can be
-- compared with: the CDF has no order to integrate along (it reached
-- 'compareValueExpr''s internal-invariant 'error'), and an arrow-typed result
-- is consumed as a probability CLOSURE (the arrow-lifted @if@ mixture, the
-- arrow-typed probabilistic-argument 'Apply' arm), which an equality indicator
-- is not -- and one whose body draws trips the central generate-backed guard,
-- refusing the whole program, generate included. Refused here instead, as an
-- absent variant (task function-value-compared-in-probability-mode).
toIRInference _ _ (Expr TypeInfo {rType=rt, chainName=cn} (InjF (Named name) params)) _
  | containsArrow rt, countProbParams params == 0, allParamsMeasurable params =
  refuse cn ("'" ++ name ++ "' here yields a value containing a function (" ++ show rt ++ "), selected some"
             ++ " other way than by a lambda, an if, or a call the compiler can see through; a function value"
             ++ " is not compared against a query sample, so no probability or cumulative closure can be built for it")
toIRInference meta False e@(Expr TypeInfo {tags=_, rType=rt} (InjF (Named _) params)) sample
  | countProbParams params == 0 && allParamsMeasurable params = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is equal to the sample
  expr <- toIRGenerate meta e
  -- Leaf resolution, one branch -- see the leaf-anchor note on the
  -- 'Var'-is-a-local-variable case below.
  return (indicatorP (semiringOf meta) (equalityGuard rt expr sample))
toIRInference meta True e@(Expr TypeInfo {tags=_, rType=rt} (InjF (Named _) params)) sample
  | countProbParams params == 0 && allParamsMeasurable params = do
  -- There is no probabilistic parameter
  -- Check whether the value of the function is less than the sample
  expr <- toIRGenerate meta e
  return (mass (compareValueExpr (semiringOf meta) rt expr sample))
-- Exactly one probabilistic operand, as 'theProbIndex' presumes: a
-- comparison of two random operands, or of a deterministic one against an
-- unmeasurable (Bottom) one -- @False == (Uniform > Uniform)@ -- is left to
-- the arms below, and was an uncaught 'error' here (task
-- single-prob-param-injf-with-no-probabilistic-operand).
toIRInference meta cumulative (Expr TypeInfo {tags=_, chainName=cnAE} (InjF (Named name) params)) sample
  | hasAnyExcept (adtDecls meta) name
  , countProbParams params == 1 = do
  -- FPair of the InjF with unique names
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) name
  let inVars = inputVars fwd
  let v1 = soleOutputVar fwd
  -- Index of the deterministic and the probabilistic parameter (Left -> 0, Right -> 1)
  let probIdx = theProbIndex name params
  let detIdxs = [0..length params - 1] \\ [probIdx]
  -- Find the inversion with all deterministic input parameters
  let invDecl = inversionFor name (inVars !! probIdx) inversions
  let FDecl {inputVars=invVars, body=invExpr, applicability=appTest, deconstructing=decons, derivatives=invDerivs} = invDecl
  -- All deterministic variable names
  let detVars = filter (v1 /=) invVars
  let detEs = map (params !!) detIdxs

  (v1', invPosExpr, invNegExpr) <- case invExpr of
        IRIf (IRVar v) pos neg -> return (v, pos, neg)
        _ -> refuse cnAE ("Form of InjF is not supported, its inverse must be an if on the sample: " ++ name)
  when (v1 /= v1') $ refuse cnAE ("Form of InjF is not supported, sample has to be the condition: " ++ name)
  (isPosAny, nonAnyExpr, exceptExpr) <-
        case (invPosExpr, invNegExpr) of
          (IRConst (VAnyExcept [expt]), non) -> return (True, non, expt)
          (non, IRConst (VAnyExcept [expt])) -> return (False, non, expt)
          _ -> refuse cnAE ("AnyExcept in InjF must be the first expression inside the if: " ++ name)

  -- Find the relevant derivative of the inversion
  let invDeriv = inverseDerivative name v1 invDerivs
  -- Generate the probabilistic sub expressions
  mapM_ (\(eVar, e) -> toIRGenerate meta e >>= \x -> setVariables [(eVar, x)]) (zip detVars detEs)
  setVariables [(v1, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Get the probabilistic inference expression of the non-deterministic
  -- subexpression. Both 'nonAnyRes' and 'exceptRes' are compiled here
  -- unconditionally and only later selected between at runtime by
  -- 'ifSample'/'zipResult' below -- so, mirroring that selection exactly,
  -- each is isolated and re-guarded on the condition under which it is the
  -- one actually read (see 'guardedSubInference'): a shared let-in block
  -- from inside either's own compilation (e.g. a deconstructing inverse
  -- crashing on the untaken arm, or a self-recursive call) must not run
  -- when that arm is not selected.
  let subResGuard = if isPosAny then IRVar v1 else notIR (IRVar v1)
  let nonAnyGuard = notIR subResGuard
  -- The subtraction's operands are compiled 'unpruned' (a pruned excepted
  -- mass inflates the difference); the plain arm only needs that when the
  -- cumulative CoV below may flip it through a complement.
  let metaNon = covOperandMeta cumulative invDeriv meta
  let metaSub = unpruned meta
  nonAnyRes <- guardedSubInference metaNon [nonAnyGuard] (probF metaNon cumulative (params !! probIdx) nonAnyExpr)
  anyRes    <- anyMarginal metaSub cumulative (params !! probIdx)
  exceptRes <- guardedSubInference metaSub [subResGuard] (probF metaSub cumulative (params !! probIdx) exceptExpr)
  let ifSample a na = if isPosAny then IRIf (IRVar v1) a na else IRIf (IRVar v1) na a
  -- The ANY arm is the marginal minus the excepted value's mass; its branch count
  -- is the excepted value's, not a sum (this is a select between the two arms).
  subRes <- mixSubP (semiringOf meta) (rBranches exceptRes) anyRes exceptRes
  let ifRes = zipResult ifSample subRes nonAnyRes
  -- Add a test whether the inversion is applicable. Scale the result according to the CoV formula if dim > 0
  return (guardP (semiringOf meta) [appTest] (scaleCoV (semiringOf meta) cumulative invDeriv ifRes))
-- Single-operand enumeration for forward-only binary InjFs (and/or) when exactly
-- one operand is deterministic and the other is a single tractable random Bool
-- (Integrate/PNormal/PLogNormal). Forward-only ops (see 'isForwardOnly') declare
-- no inversions, so the generic single-inversion clause below has nothing to
-- invert and crashes with "Non-exhaustive patterns in [invDecl]" on exactly this
-- shape (found by TestFuzz's typed generator, e.g. @(Uniform < 0.4) and True@).
-- Mirrors the two-operand enumerate-both case further down: the deterministic
-- side doesn't depend on the enum variable, so it's evaluated once outside the
-- loop; the random side's own (already-tractable) enum is then looped, keeping
-- cells where forward(l,r) == sample.
toIRInference meta False (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | isForwardOnly (adtDecls meta) (resolveInjF rt name)
    && (pType (getTypeInfo left) == Deterministic || pType (getTypeInfo right) == Deterministic)
    && countProbParams [left, right] == 1
    && isEnumerable (tags (getTypeInfo (if pType (getTypeInfo left) == Deterministic then right else left))) = do
  let resolvedName = resolveInjF rt name
  let leftDet = pType (getTypeInfo left) == Deterministic
  let (detExprSrc, randExprSrc) = if leftDet then (left, right) else (right, left)
  let enumList = head [x | DiscreteValues x <- tags (getTypeInfo randExprSrc)]
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let (v1, v2) = binaryInputVars resolvedName fwd
  let f = body fwd
  let (detVar, randVar) = if leftDet then (v1, v2) else (v2, v1)
  detIR <- toIRGenerate meta detExprSrc
  setVariables [(detVar, detIR)]
  let sr = semiringOf meta
  mTblRand <- materializeOperandTable meta randExprSrc
  returnO <- scoped $ do
    pRand <- operandProb meta mTblRand randExprSrc (IRVar randVar)
    return (IRIf (IROp OpEq f sample) pRand (srZero sr))
  let (outerBinds, body') = hoistInvariantBindings randVar (closeExpr returnO id)
  setVariables outerBinds
  opaqueMass sr (enumSumNode sr randVar enumList body') const0
-- Cumulative (cdf) counterpart of the single-operand enumeration case above.
toIRInference meta True (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | isForwardOnly (adtDecls meta) (resolveInjF rt name)
    && (pType (getTypeInfo left) == Deterministic || pType (getTypeInfo right) == Deterministic)
    && countProbParams [left, right] == 1
    && isEnumerable (tags (getTypeInfo (if pType (getTypeInfo left) == Deterministic then right else left))) = do
  let resolvedName = resolveInjF rt name
  let leftDet = pType (getTypeInfo left) == Deterministic
  let (detExprSrc, randExprSrc) = if leftDet then (left, right) else (right, left)
  let enumList = head [x | DiscreteValues x <- tags (getTypeInfo randExprSrc)]
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let (v1, v2) = binaryInputVars resolvedName fwd
  let f = body fwd
  let (detVar, randVar) = if leftDet then (v1, v2) else (v2, v1)
  detIR <- toIRGenerate meta detExprSrc
  setVariables [(detVar, detIR)]
  let sr = semiringOf meta
  mTblRand <- materializeOperandTable meta randExprSrc
  returnO <- scoped $ do
    pRand <- operandProb meta mTblRand randExprSrc (IRVar randVar)
    return (IRIf (IROp OpLessThan sample f) (srZero sr) pRand)
  let (outerBinds, body') = hoistInvariantBindings randVar (closeExpr returnO id)
  setVariables outerBinds
  opaqueMass sr (enumSumNode sr randVar enumList body') const0
-- A Boolean connective with one deterministic operand: @d || b@ is True where
-- @d@ holds and @b@ elsewhere, and @d && b@ dually. The connective has no
-- inverse (the arm below would need one), and before this a random operand
-- without an enumerable tag had no rule at all (fuzz-let-witness-bugs item 4,
-- @False || isLeft (left Uniform)@).
toIRInference meta cumulative (Expr _ (InjF (Named name) [a, b])) sample
  | name `elem` ["and", "or"]
  , countProbParams [a, b] == 1 && allParamsMeasurable [a, b] = do
  let sr = semiringOf meta
  let (detE, randE) = if pType (getTypeInfo a) == Deterministic then (a, b) else (b, a)
  d <- toIRGenerate meta detE
  r <- toIRInference meta cumulative randE sample
  let absorbing = name == "or"
  let absorbed = if cumulative
        then mass (compareValueExpr sr TBool (IRConst (VBool absorbing)) sample)
        else indicatorP sr (equalityGuard TBool (IRConst (VBool absorbing)) sample)
  -- The deterministic operand selects every field, so it is bound once rather
  -- than copied into each ('zipResult'); a literal stays inline and folds.
  dv <- case d of
    IRConst _ -> return d
    IRVar _   -> return d
    _ -> do
      v <- mkVariable "and_or_det"
      setVariables [(v, d)]
      return (IRVar v)
  let decides = if absorbing then dv else IRUnaryOp OpNot dv
  return (zipResult (IRIf decides) absorbed r)
--
-- Not for a forward-only InjF (@and@/@or@): it has no inverse to solve for the
-- probabilistic operand, and asking 'inversionFor' for one was an uncaught
-- error (fuzz-let-witness-bugs item 4, @False || isLeft (left Uniform)@).
toIRInference meta cumulative (Expr TypeInfo {tags=_, rType=rt} (InjF (Named name) params)) sample
  | countProbParams params == 1 && allParamsMeasurable params
  , not (isForwardOnly (adtDecls meta) (resolveInjF rt name)) = do
  let resolvedName = resolveInjF rt name
  -- FPair of the InjF with unique names
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) resolvedName
  let inVars = inputVars fwd
  let v1 = soleOutputVar fwd
  -- Index of the deterministic and the probabilistic parameter (Left -> 0, Right -> 1)
  let probIdx = theProbIndex name params
  let detIdxs = [0..length params - 1] \\ [probIdx]
  -- Find the inversion with all deterministic input parameters
  let invDecl = inversionFor name (inVars !! probIdx) inversions
  let FDecl {inputVars=invVars, deconstructing=decons, derivatives=invDerivs} = invDecl
  -- All deterministic variable names
  let detVars = filter (v1 /=) invVars
  let detEs = map (params !!) detIdxs

  -- Find the relevant derivative of the inversion
  let invDeriv = inverseDerivative name v1 invDerivs
  -- The bound to invert through, rounded for a cumulative integer quotient
  -- ('modeInverse').
  let (invExpr, appTest) = modeInverse cumulative invDecl invDeriv
  -- Generate the probabilistic sub expressions
  mapM_ (\(eVar, e) -> toIRGenerate meta e >>= \x -> setVariables [(eVar, x)]) (zip detVars detEs)
  setVariables [(v1, sample)]
  -- Use the save probabilistic inference in case the InjF decustructs types (for Any checks)
  let probF = if decons then toIRInferenceSave else toIRInference
  -- Get the probabilistic inference expression of the non-deterministic
  -- subexpression, isolated and re-guarded on appTest (see
  -- 'guardedSubInference') so a shared let-in block cannot escape the
  -- applicability test 'guardP' applies below.
  -- Unpruned when the cumulative CoV below may flip it through a complement.
  let metaOp = covOperandMeta cumulative invDeriv meta
  let operandAt c = guardedSubInference metaOp [appTest] (probF metaOp c (params !! probIdx) invExpr)
  paramRes <- operandAt cumulative
  -- Scale the result according to the CoV formula (the point mass at the
  -- bound joins a decreasing CDF flip), then test whether the inversion is
  -- applicable.
  scaled <- pointInverseCoV meta cumulative invDeriv paramRes (operandAt False)
  return (guardP (semiringOf meta) [appTest] scaled)
-- Enumerate-both discrete path for forward-only binary InjFs (and/or). No point
-- inverse exists, so loop the |L|x|R| grid and keep cells where forward(l,r) == sample,
-- accumulating pLeft(l) * pRight(r). Mirrors the cumulative double-enum path below.
--
-- Also for @==@ of two random enumerable operands (@camNN img == depthNN
-- depth@): its inverse on the False polarity is the 'VAnyExcept' set, which
-- the invertible grid below would hand to 'IRIsPossible' and the text
-- backends cannot render, so it is compared forward here instead. Before the
-- 'hasAnyExcept' arm above required one probabilistic operand, this shape died
-- there ("More than one probabilistic argument", task
-- bare-equality-of-two-neural-reads-crashes, whose O(V) agreement fusion this
-- O(V^2) grid is not).
toIRInference meta False (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | (isForwardOnly (adtDecls meta) (resolveInjF rt name) || hasAnyExcept (adtDecls meta) name)
    && isEnumerable (tags (getTypeInfo left)) && isEnumerable (tags (getTypeInfo right))
    && pType (getTypeInfo left) /= Deterministic && pType (getTypeInfo right) /= Deterministic = do
  let resolvedName = resolveInjF rt name
  let enumListL = head [x | DiscreteValues x <- tags (getTypeInfo left)]
  let enumListR = head [x | DiscreteValues x <- tags (getTypeInfo right)]
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let (v1, v2) = binaryInputVars resolvedName fwd
  let f = body fwd
  let sr = semiringOf meta
  mTblL <- materializeOperandTable meta left
  mTblR <- materializeOperandTable meta right
  returnO <- scoped $ do
    pLeft <- operandProb meta mTblL left (IRVar v1)
    pRight <- operandProb meta mTblR right (IRVar v2)
    return (IRIf (IROp OpEq f sample) (srTimes sr pLeft pRight) (srZero sr))
  let (v2InvBinds, v2Body) = hoistInvariantBindings v2 (closeExpr returnO id)
  let innerSum = buildLetIns v2InvBinds (enumSumNode sr v2 enumListR v2Body)
  let (outerBinds, v1Body) = hoistInvariantBindings v1 innerSum
  setVariables outerBinds
  opaqueMass sr (enumSumNode sr v1 enumListL v1Body) const0
toIRInference meta False (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | isEnumerable (tags (getTypeInfo left)) && isEnumerable (tags (getTypeInfo right))
    && pType (getTypeInfo left) /= Deterministic && pType (getTypeInfo right) /= Deterministic = do
  let resolvedName = resolveInjF rt name
  -- Get all possible values for subexpressions
  let extrasLeft = tags $ getTypeInfo left
  let extrasRight = tags $ getTypeInfo right
  let enumListL = head [x | DiscreteValues x <- extrasLeft]
  let enumListR = head [x | DiscreteValues x <- extrasRight]
  -- mult/multI's own absorbing element, in this node's type -- see the
  -- zero-atom mix below.
  let zeroValL = zeroValueOf rt

  fPair <- instantiate mkVariable (adtDecls meta) resolvedName -- FPair of the InjF with unique names
  let FPair fwd inversions = fPair
  let (_, v3) = binaryInputVars resolvedName fwd
  -- We get the inversion to the right side
  let invDecl = inversionFor resolvedName v3 inversions
  let (x2, x3) = binaryInputVars resolvedName invDecl
  let invExpr = body invDecl
  let appTest = applicability invDecl

  -- We now compute
  -- for each e in leftEnum:
  --   sum += if invExpr(e, sample) in rightEnum then pLeft(e) * pRight(sample - e) else 0
  -- For that we name e like the lhs of
  -- We need to unfold the monad stack, because the EnumSum Works like a lambda expression and has a local scope
  let sr = semiringOf meta
  -- Materialized operand marginals, when the operand is itself a nested
  -- enumerable chain: built here, in the enclosing scope, so their cells are
  -- computed once instead of once per iteration of the enumeration below.
  mTblL <- materializeOperandTable meta left
  mTblR <- materializeOperandTable meta right
  irTuple <- scoped (do
    -- the subexpr in the loop must compute p(enumVar| left) * p(inverse | right)
    setVariables [(x3, sample)]
    -- The inversion's own applicability (task mult-enumerable-zero-divisor-crash):
    -- 'invExpr' (e.g. mult's c/e) is undefined at some enumerated values (e.g.
    -- e=0), and it sits as an argument to 'IRIsPossible', so it must be
    -- evaluated before any membership test can run. Gating via 'IRIf' rather
    -- than 'OpAnd' matters here: both operands of an IR boolean op are
    -- evaluated, so an 'OpAnd' would still divide by zero.
    let possibleExpr = IRIf appTest (IRIsPossible (multiValueToIR enumListR) invExpr) (IRConst (VBool False))
    -- Without topK, pLeft is read once, inside the 'possible' arm below, and the
    -- optimizer's let-inlining moves its bindings there: a cell whose inverted
    -- value lies outside the right-hand domain never descends into @left@.
    -- Under topK the cutoff test reads pLeft a second time, so its bindings
    -- stayed in front of the guard and every cell descended into @left@
    -- whether or not it was possible. On a left-nested chain that eager
    -- descent compounds per level into a product of the domain sizes, where
    -- the guarded one only walks the possible splits (task
    -- topk-compiled-scene-count-query-exponential-in-slots: p(0) on a 7-slot
    -- scene count took 34 s against 0.1 s topK-off). So under topK pLeft is
    -- bound once, behind 'possible', and reads as zero elsewhere -- a value
    -- nothing consumes there, since the cutoff test is conjoined with
    -- 'possible'. Its pure loop-invariant bindings (a network call) are
    -- released into the writer first, as pRight's are below, so hoisting
    -- still lifts them out of the loop.
    (pLeft, leftNames, possible) <- case topKThreshold (compilerConfig meta) of
      Nothing -> do
        oL <- scoped (operandProb meta mTblL left (IRVar x2))
        pL <- inline oL
        return (pL, openNames oL, possibleExpr)
      Just _ -> do
        oL <- scoped (operandProb meta mTblL left (IRVar x2))
        let (lFree, lGuarded) = splitOpen (splitHoistable [x2, x3]) oL
        inline lFree
        possibleV <- mkVariable "possible"
        pLeftV <- mkVariable "pLeft"
        setVariables [ (possibleV, possibleExpr)
                     , (pLeftV, IRIf (IRVar possibleV) (closeExpr lGuarded id) (srZero sr)) ]
        return (IRVar pLeftV, openNames lGuarded ++ [possibleV, pLeftV], IRVar possibleV)
    -- pRight is computed in a nested writer so its bindings can be guarded by the topK check,
    -- avoiding the inner right-side inference work whenever acc_prob * pLeft is already below cutoff.
    -- The right-hand key is the INVERTED value, an expression rather than an
    -- enumeration variable, so a table read has to bind it first: the lookup
    -- reads its key once per arm.
    pRightO <- scoped $ case mTblR of
          Just tbl -> do
            keyName <- mkVariable "mat_key"
            setVariables [(keyName, invExpr)]
            return (mass (lookupMarginal meta tbl (IRVar keyName)))
          Nothing -> toIRInference meta False right invExpr
    -- The guard below keeps pRight's per-cell work out of cells that fail it,
    -- but it also used to trap pRight's loop-invariant bindings -- a neural
    -- operand's raw network call, @nn_raw = n(b)@ -- inside the loop body,
    -- where 'hoistInvariantBindings' below never sees them. pLeft's matching
    -- call is in this writer and so was hoisted: @n(a) ++ n(b)@ ran the
    -- network once for @a@ and once per enumerated cell for @b@ (task
    -- plusi-second-operand-oracle-not-hoisted: 1 vs 1900 on the two-digit
    -- MNIST sum). Pure bindings that read no loop variable and nothing bound
    -- per iteration are released into this writer instead, so they are
    -- hoisted exactly like pLeft's; everything else stays guarded.
    let (rFree, rGuarded) = splitOpen (splitHoistable (x2 : x3 : leftNames)) pRightO
    inline rFree
    -- accProb * pLeft is a semiring product (srTimes): under logSpace both
    -- operands are log-probabilities, so a hardcoded OpMult here silently
    -- pruned every branch (task topk-logspace-unsound). The comparison against
    -- the cutoff stays OpGreaterThan either way -- log is monotone, and the
    -- runtime cutoff parameter is passed in the matching space.
    let cutoffOk = case topKThreshold (compilerConfig meta) of
          Nothing -> possible
          Just _  -> IROp OpAnd possible
                       (IROp OpGreaterThan
                          (srTimes sr (accProb meta) pLeft)
                          (IRVar topKCutoffParamName))
    let returnExpr   = IRIf cutoffOk (closeExpr rGuarded (srTimes sr pLeft . unP . rProb)) (srZero sr)
    let branchesExpr = IRIf cutoffOk (IRConst (VFloat 1)) (IRConst (VFloat 0))
    return (mkPResult (sealP returnExpr) dim0 branchesExpr (notIR cutoffOk))
    ) <&> generateLetInBlock meta
  uniquePrefix <- mkVariable ""
  let applyUnique = irMap (uniqueify [x2, x3] uniquePrefix)
  let (outerBinds, innerTuple) = hoistInvariantBindings x2 irTuple
  let renameHoisted (n, v) = (if n `elem` [x2, x3] then uniquePrefix ++ n else n, applyUnique v)
  setVariables (map renameHoisted outerBinds)
  summed <- enumSumP (semiringOf meta) (countBranches (compilerConfig meta)) applyUnique x2 enumListL innerTuple
  -- mult(0, y) = 0 for every y: the applicability guard above correctly drops
  -- that enumerated cell (a=0 is not point-invertible -- its fiber is the
  -- whole right-hand domain, not a point), but dropping it silently
  -- under-reports p(sample=0) by exactly P(a=0) (task
  -- mult-inverse-unguarded-zero-division: "the marginal should be trivially
  -- 1" for that cell). Mixed back in the same way an explicit
  -- `if coinflip then ... else 0` mixture already is: as its own alternative,
  -- picked by 'mixP' (lower dim / possibility wins) rather than folded into
  -- the enumerated sum, which assumes every term is a point-invertible
  -- density/mass of the same shape.
  if resolvedName `elem` ["mult", "multI"] && zeroValL `elem` multiValueToValueList enumListL
    then do
      pLeftZero <- operandProb meta mTblL left (IRConst (valueToIR zeroValL))
      let zeroAtom = prodP sr (mass pLeftZero) (indicatorP sr (equalityGuard rt sample (IRConst (valueToIR zeroValL))))
      mixP sr (IROp OpPlus (rBranches summed) (rBranches zeroAtom)) zeroAtom summed
    else return summed
-- For the cumulative case we cant get around two enum sums
toIRInference meta True (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | isEnumerable (tags (getTypeInfo left)) && isEnumerable (tags (getTypeInfo right))
    && pType (getTypeInfo left) /= Deterministic && pType (getTypeInfo right) /= Deterministic = do
  let resolvedName = resolveInjF rt name
  -- Get all possible values for subexpressions
  let extrasLeft = tags $ getTypeInfo left
  let extrasRight = tags $ getTypeInfo right
  let enumListL = head [x | DiscreteValues x <- extrasLeft]
  let enumListR = head [x | DiscreteValues x <- extrasRight]

  fPair <- instantiate mkVariable (adtDecls meta) resolvedName -- FPair of the InjF with unique names
  let FPair fwd _ = fPair
  let (v1, v2) = binaryInputVars resolvedName fwd
  let f = body fwd
  let sr = semiringOf meta
  -- Compute the loop body in a nested writer so its bindings can be captured rather
  -- than leaking to the enclosing function scope: those bindings reference the enum
  -- variables v1/v2 (the coin_prob calls) and must be scoped *inside* the matching
  -- enumSum, not above it.
  mTblL <- materializeOperandTable meta left
  mTblR <- materializeOperandTable meta right
  returnO <- scoped $ do
    pLeft <- operandProb meta mTblL left (IRVar v1)
    pRight <- operandProb meta mTblR right (IRVar v2)
    return (IRIf (IROp OpLessThan sample f) (srZero sr) (srTimes sr pLeft pRight))
  -- Place each binding at the outermost scope where it remains well-formed: fully
  -- invariant bindings are hoisted to the function top level, bindings depending only
  -- on v1 sit between the two enumSums, and bindings depending on v2 stay innermost.
  let (v2InvBinds, v2Body) = hoistInvariantBindings v2 (closeExpr returnO id)
  let innerSum = buildLetIns v2InvBinds (enumSumNode sr v2 enumListR v2Body)
  let (outerBinds, v1Body) = hoistInvariantBindings v1 innerSum
  setVariables outerBinds
  opaqueMass sr (enumSumNode sr v1 enumListL v1Body) const0
toIRInference meta cumulative (Expr TypeInfo {rType=rt} (Var n)) sample = do
  -- Variable might be a function
  case lookup n (typeEnv meta) of
    -- Var is a function
    Just(TArrow _ _, hasInference) -> do
      var <- mkVariable "call"
      name <- if hasInference then calleeInferenceName meta cumulative n else return n
      let callExpr = if hasInference
            then inferenceCall meta cumulative (IRVar name) sample
            else IRApply (IRVar name) sample
      setVariables [(var, callExpr)]
      -- The return value is still a function. No need to do dim and branch counting here
      return (detP (IRVar var))
    -- Var is a top level declaration (an therefor has a _prob function)
    Just (_, True) -> do
      var <- mkVariable "call"
      calleeName <- calleeInferenceName meta cumulative n
      let callExpr = inferenceCall meta cumulative (IRVar calleeName) sample
      setVariables [(var, callExpr)]
      return (unpackResult var)
    -- Var is a local variable
    -- A bound parameter used directly as a return value is a LEAF resolution:
    -- it compares a deterministically-known value against the sample and stops,
    -- the identical operation the 'Constant'/'ThetaI' cases perform. It
    -- therefore counts as one branch like they do -- 'mass'/'indicatorP', not
    -- 'detP'. The branch-count anchor is "every terminal leaf counts 1,
    -- deterministic or random", so which AST constructor happens to carry the
    -- same value into the same comparison must not change the count (task
    -- bc-recursive-prob-divergence; pinned by prop_BCLeafSpellingIndependence).
    -- 'detP' -- zero branches -- stays for results that resolve to no value at
    -- all: closures, lambdas, the TArrow arms above.
    Just (_, False) ->
      if cumulative then
        return (mass (compareValueExpr (semiringOf meta) rt (IRVar n) sample))
      else
        return (indicatorP (semiringOf meta) (equalityGuard rt (IRVar n) sample))
    -- Invariant, not a refusal (task static-refusals-become-absent-variants): every bound name is in the type env (a miss is filed: fuzz-admission-oracle-bugs item 7).
    Nothing -> error ("Could not find name in TypeEnv: " ++ n)
-- Mixed enumerate-and-shift/scale convolution: exactly ONE operand is a
-- finite-discrete enumerable (a `DiscreteValues`-tagged mixture of point
-- masses), the other is a continuous scalar with a density. The marginal
--
--   f_Z(z) = sum_e p_X(e) * f_Y(g^-1_y(e, z)) * |d g^-1_y / dz|
--
-- is exactly what 'marginalize's `keepD` guard promises for this shape (a
-- finite mixture convolved with a Normal/LogNormal has a closed-form density),
-- and until task marginalize-keepd-overclaims-density-for-generic-plus-mult
-- nothing here built it: the node typed 'Integrate', matched no equation, and
-- fell through to the catch-all `error` below.
--
-- It is the composition of the two clauses either side of it: the
-- both-enumerable path's `enumSumP` loop over the finite operand's support,
-- with the generic single-inversion path's body (invert to the continuous
-- operand, evaluate its density there, apply the change-of-variables Jacobian)
-- as the loop body. The `IRIsPossible` membership test the both-enumerable
-- path applies to the inverted value is absent here on purpose: the other
-- operand is continuous, so every inverted point is in its support.
--
-- The result's `dim` cannot come through 'enumSumP', which packs only
-- (prob, branches) and hardcodes dim 0 for the discrete mass it normally
-- builds. It is supplied here instead, and it is a static property rather
-- than a per-iteration one: the enumerated side contributes dim 0, the
-- change of variables is dimension-preserving, so the node's dim is the
-- continuous operand's. In probability mode that is dim 1, ANY-guarded on
-- this node's own sample; in cumulative mode a CDF value is a mass, so it is
-- dim 0 (what the continuous operand's own cumulative result reports). The
-- guard's `rType` test is what earns reading that off statically: a
-- non-'Deterministic', non-enumerable 'TFloat' operand under
-- 'allParamsMeasurable' is a continuous scalar.
--
-- The override happens outside the loop and so does not disturb 'scaleCoV',
-- which reads the per-iteration operand's own `rDim` inside it.
toIRInference meta cumulative (Expr TypeInfo {rType=rt} (InjF (Named name) [left, right])) sample
  | rt == TFloat
  , not (isForwardOnly (adtDecls meta) (resolveInjF rt name))
  , pType (getTypeInfo left) /= Deterministic
  , pType (getTypeInfo right) /= Deterministic
  , isEnumerable (tags (getTypeInfo left)) /= isEnumerable (tags (getTypeInfo right))
  , rType (getTypeInfo (if isEnumerable (tags (getTypeInfo left)) then right else left)) == TFloat
  , allParamsMeasurable [left, right] = do
  let resolvedName = resolveInjF rt name
  let leftEnum = isEnumerable (tags (getTypeInfo left))
  let (enumE, contE) = if leftEnum then (left, right) else (right, left)
  let enumList = head [x | DiscreteValues x <- tags (getTypeInfo enumE)]
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) resolvedName
  let (vL, vR) = binaryInputVars resolvedName fwd
  let contVar = if leftEnum then vR else vL
  -- The inversion that solves for the CONTINUOUS operand; its two inputs are
  -- the enumerated operand's value and this node's observation.
  let invDecl = inversionFor resolvedName contVar inversions
  let FDecl {body=invExpr, applicability=appTest, deconstructing=decons, derivatives=invDerivs} = invDecl
  let (xEnum, xSample) = binaryInputVars resolvedName invDecl
  -- d(inverse)/d(observation), keyed by the forward declaration's output var
  -- (for `mult` this is the 1/e that makes the scaled mixture integrate to 1).
  let invDeriv = inverseDerivative resolvedName (soleOutputVar fwd) invDerivs
  let sr = semiringOf meta
  let probF = if decons then toIRInferenceSave else toIRInference
  let metaOp = covOperandMeta cumulative invDeriv meta
  mTblEnum <- materializeOperandTable meta enumE
  -- With no table for the enumerated operand, the loop below re-derives
  -- p(enumE = e) for every value e of its domain, and that is a full
  -- enumeration of the draws it is a function of: |dom(enumE)| x 10^N cells
  -- for N digit reads (task noisy-observation-mixes-over-result-value-domain).
  -- When the operand is such a function, sum over its draws' cells directly
  -- instead ('latentCellSum'): one term per cell, at the cell's forward value.
  let cellDraws = latentCellBinders meta enumE
  perCell <- case (mTblEnum, cellDraws) of
    (Nothing, ds@(_:_)) | not (any (`Set.member` freeVarsExpr contE) ds) -> do
      uniquePrefix <- mkVariable ""
      let un = irMap (uniqueify [xEnum, xSample] uniquePrefix)
          metaOpU = covOperandMeta cumulative (un invDeriv) meta
      -- Built in a scope of its own: a leaf that turns out to draw fresh
      -- randomness declines the whole attempt, and its bindings are dropped.
      attemptO <- scoped $
        latentCellSum meta cumulative (anyGuardedDim sample) enumE (\fv -> fmap Just $ do
          setVariables [(uniquePrefix ++ xSample, sample), (uniquePrefix ++ xEnum, fv)]
          contRes <- guardedSubInference metaOpU [un appTest]
                       (probF metaOpU cumulative contE (un invExpr))
          return (guardP sr [un appTest] (scaleCoV sr cumulative (un invDeriv) contRes)))
      inlineIfJust attemptO
    _ -> return Nothing
  summedTyped <- case perCell of
   Just r -> return r
   Nothing -> do
    irTuple <- scoped (do
      setVariables [(xSample, sample)]
      pEnumRaw <- operandProb meta mTblEnum enumE (IRVar xEnum)
      pEnumVar <- mkVariable "p_enum"
      setVariables [(pEnumVar, pEnumRaw)]
      let pEnum = IRVar pEnumVar
      contRes <- guardedSubInference metaOp [appTest]
                   (probF metaOp cumulative contE invExpr)
      let scaled = guardP sr [appTest] (scaleCoV sr cumulative invDeriv contRes)
      -- A value of the enumerated operand's domain with no mass is an
      -- impossible term, not a possible zero: 'enumMixP' below lets the
      -- lowest-dim possible term decide the result's dim, and a zero-weight
      -- atom must not outvote a real density. The tag over-approximates the
      -- support, so such values are ordinary. Exact zero is sound here for the
      -- reason 'opaqueMass' gives: this is a discrete mass.
      return (prodP sr (impossibleWhen (IROp OpEq pEnum (srZero sr)) (mass pEnum)) scaled)
      ) <&> generateLetInBlock meta
    uniquePrefix <- mkVariable ""
    let applyUnique = irMap (uniqueify [xEnum, xSample] uniquePrefix)
    let (outerBinds, innerTuple) = hoistInvariantBindings xEnum irTuple
    let renameHoisted (n, v) = (if n `elem` [xEnum, xSample] then uniquePrefix ++ n else n, applyUnique v)
    setVariables (map renameHoisted outerBinds)
    -- The "continuous" operand is only known to be a real scalar (its rType),
    -- not to have a density: an operand no tag reaches -- a fold through a
    -- recursive helper, which Analysis refuses to look through -- may be a
    -- discrete count the plan path answers as a mass, or a mixture of atoms and
    -- a density. So in probability mode each term keeps the dim its own
    -- inference reports, and 'enumMixP' combines them as a mixture (possible
    -- atoms outvote densities), instead of stamping dim 1 on the sum (task
    -- plan-sum-with-sunk-discrete-draw-reports-density). A term that is a true
    -- density reports 'anyGuardedDim', so a genuinely continuous operand gets
    -- exactly the result it did before. Cumulative mode is a CDF, dim 0,
    -- whatever the terms are.
    if cumulative
      then enumSumP sr (countBranches (compilerConfig meta)) applyUnique xEnum enumList innerTuple
      else enumMixP sr (countBranches (compilerConfig meta)) applyUnique (anyGuardedDim sample) xEnum enumList innerTuple
  -- mult(0, y) = 0 for every y (task mult-inversion-unguarded-at-zero, symptom
  -- 3): 'appTest' above already keeps the guarded scaling from dividing by
  -- e=0, but that just drops the term -- the true contribution of that
  -- enumerated cell is the DEGENERATE law "the result is deterministically 0",
  -- an atom the density sum can't represent (it has no Lebesgue density).
  -- Mixed back in exactly the way an explicit `if coinflip then 0 else 2*Normal`
  -- already is: as its own alternative, picked by 'mixP' (lower dim wins) in
  -- probability mode, or added in cumulative mode where both sides are dim 0
  -- CDF contributions anyway.
  if resolvedName == "mult" && VFloat 0 `elem` multiValueToValueList enumList
    then do
      pEnumZero <- operandProb meta mTblEnum enumE (IRConst (VFloat 0))
      let zeroIndicator = if cumulative
                            then mass (compareValueExpr sr rt (IRConst (VFloat 0)) sample)
                            else indicatorP sr (equalityGuard rt sample (IRConst (VFloat 0)))
      let zeroAtom = prodP sr (mass pEnumZero) zeroIndicator
      mixP sr (IROp OpPlus (rBranches summedTyped) (rBranches zeroAtom)) zeroAtom summedTyped
    else return summedTyped
toIRInference _ _ (Expr ti (Subtree _ _)) _ = refuse (chainName ti) "Cannot infer prob on subtree expression. Please check your syntax"
-- The catch-all: no inference equation covers this node. Reached only when
-- the modality engine admitted a shape no IR equation builds (an over-promise,
-- design pipeline-coherence F2); it is a refusal of the variant, not a crash.
toIRInference _ cumulative x _ = refuse (chainName (getTypeInfo x))
  ("found no way to convert to IR in " ++ (if cumulative then "cumulative" else "probability")
   ++ " mode (pType " ++ show (pType (getTypeInfo x)) ++ "): " ++ show x)

createHOInverse :: CompilerMetadata -> (String, Expr) -> CompilerMonad (IRExpr -> IRExpr)
createHOInverse meta (fVar, f) = do
  let fcData' = fcData meta
  let localAdts = adtDecls meta
  -- NB: the applicability guard (3rd component, see observe-partials-umbrella
  -- N1b) is not threaded through the higher-order inverse path yet -- a
  -- deconstructing InjF crossed while inverting a user-defined function passed
  -- through createHOInverse can still crash. Not hit by any current test case;
  -- tracked as follow-up alongside the other HO-inverse gaps.
  let InvChain{invValue = inverseF0, invCoV = inverseCoV0} = toInvExpr fcData' localAdts (chainName $ getTypeInfo f)
  inverseF   <- materializeAnchors meta inverseF0
  inverseCoV <- materializeAnchors meta inverseCoV0
  let (_, _, lBodyChainName, tag) = equivalentLambda "createHOInverse" fcData' (chainName $ getTypeInfo f)
  let inverseLambdaProb = IRLambda (lBodyChainName ++ tag) inverseF
  let inverseLambdaCoV = IRLambda (lBodyChainName ++ tag) inverseCoV
  -- Rename all occurances of f^-1 from the definition to f_prob
  let renVar = renameVar (fVar ++ "^-1") (fVar ++ "_prob")
  let renDeriv = renameVar (fVar ++ "^-1'") (fVar ++ "_prob_deriv")
  setVariables [(fVar ++ "_prob", inverseLambdaProb), (fVar ++ "_prob_deriv", inverseLambdaCoV)]
  return (renVar . renDeriv)

countProbParams :: [Expr] -> Int
countProbParams es = length probParams
  where
    probParams = filter (\p -> p == Integrate || p == PNormal || p == PLogNormal) pTypes
    pt x = pType (getTypeInfo x)
    pTypes = map pt es

-- True when no parameter is 'Bottom' -- i.e. every parameter is either
-- 'Deterministic' or one of the three tractable probabilistic rungs
-- (Integrate/PNormal/PLogNormal). A 'countProbParams params == k' guard by
-- itself only counts the tractable rungs, so a 'Bottom' parameter (no
-- measurable distribution at all -- "nothing better than sampling is
-- available") is silently indistinguishable from an absent one: a clause
-- guarded by 'countProbParams params == 0' would treat "every parameter is
-- Deterministic" and "one parameter is Bottom, the rest Deterministic" as
-- the same case, and fall through to 'toIRGenerate' on the Bottom
-- parameter -- a fresh random draw compared against the query sample,
-- silently wrong rather than refused (task
-- projection-discards-intractable-sibling-generate-backed, reached via
-- 'fst'/'snd' projecting away an intractable sibling: 'fst (Uniform,
-- Uniform * Uniform)'). Every 'countProbParams params == k' guard on an
-- InjF clause must therefore also assert this.
allParamsMeasurable :: [Expr] -> Bool
allParamsMeasurable = all ((/= Bottom) . pType . getTypeInfo)

-- | 'mult'/'multI's absorbing element, in a given return type -- shared by the
-- zero-multiplier InjF clause above and the enumerable-domain zero-atom fixes
-- below (tasks mult-inversion-unguarded-at-zero,
-- mult-enumerable-zero-divisor-crash, mult-inverse-unguarded-zero-division).
zeroValueOf :: RType -> Value
zeroValueOf TInt = VInt 0
zeroValueOf _    = VFloat 0

-- | The factor of a product that is deterministic, may be zero at run time,
-- and multiplies a random operand -- the one 'mult' must branch on (see the
-- run-time zero-factor clause). Not a factor that is statically zero (the
-- static clauses take it) or statically nonzero (a nonzero literal, or a
-- 'DiscreteValues' set without zero), nor a product of two random operands.
runtimeZeroFactor :: Expr -> Expr -> Maybe Expr
runtimeZeroFactor a b = case (det a, det b) of
  (True, False) | mayBeZero a -> Just a
  (False, True) | mayBeZero b -> Just b
  _ -> Nothing
  where
    det x = pType (getTypeInfo x) == Deterministic
    mayBeZero x@(Expr ti nd)
      | isStaticZero x = False
      | Constant _ <- nd = False
      | (MultiDiscretes vs : _) <- [ mv | DiscreteValues mv <- tags ti ] = any isZeroLit vs
      | otherwise = True
    isZeroLit (VFloat 0) = True
    isZeroLit (VInt 0) = True
    isZeroLit _ = False

-- | Whether a value of this type has a function anywhere inside it.
containsArrow :: RType -> Bool
containsArrow (TArrow _ _)      = True
containsArrow (ListOf t)        = containsArrow t
containsArrow (Tuple a b)       = containsArrow a || containsArrow b
containsArrow (TEither a b)     = containsArrow a || containsArrow b
containsArrow (TTensor _ t)     = containsArrow t
containsArrow (GreaterType a b) = containsArrow a || containsArrow b
-- Spelled out rather than a catch-all, so a new 'RType' constructor is a
-- compile error here instead of a silent False.
containsArrow TBool       = False
containsArrow TInt        = False
containsArrow TSymbol     = False
containsArrow TFloat      = False
containsArrow TUnit       = False
containsArrow TThetaTree  = False
containsArrow (TADT _)    = False
containsArrow NullList    = False
containsArrow BottomTuple = False
containsArrow (TVarR _)   = False
containsArrow SPLL.Typing.RType.NotSetYet = False

--folding detGen and Gen into one, as the distinction is one to make sure things that are det are indeed det.
-- That's what the type system is for though.
toIRGenerate :: CompilerMetadata -> Expr -> CompilerMonad  IRExpr
toIRGenerate meta (Expr _ (IfThenElse cond left right)) = do
  c <- toIRGenerate meta cond
  l <- toIRGenerate meta left
  r <- toIRGenerate meta right
  return $ IRIf c l r
toIRGenerate meta (Expr _ (ThetaI a ix)) = do
  a' <- toIRGenerate meta a
  return $ IRDestruct (AcTheta ix) a'
toIRGenerate meta (Expr _ (Subtree a ix)) = do
  a' <- toIRGenerate meta a
  return $ IRDestruct (AcSubtree ix) a'
toIRGenerate _ (Expr _ (Constant (VError e))) = return $ IRError e
toIRGenerate _ (Expr _ (Constant x)) = return (IRConst (fmap failConversion x))
-- Distribution primitives (reserved-name Vars): each occurrence is a fresh draw.
toIRGenerate _ (Expr _ (Var "Uniform")) = return $ IRSample IRUniform
toIRGenerate _ (Expr _ (Var "Normal")) = return $ IRSample IRNormal
-- A product with a statically-zero factor is zero whatever the other factor
-- draws (its law is a point, 'lawPoint'). Emitting the
-- other factor would put its unread draw into every generate-and-compare
-- probability over the product, which the generate-backed guard then refused
-- (fuzz-admission-oracle-bugs item 6).
toIRGenerate meta e@(Expr _ (InjF (Named name) [_, _]))
  | name `elem` ["mult", "multI"], Just v <- lawPoint meta e =
  return (IRConst (valueToIR v))
-- A random 'collapse' draws from the Gaussian of its operand's moments, not
-- from the operand; a point operand is the point, which the generic equation
-- below gives through the identity forward. The moments' bindings are scoped
-- to the draw: generate code closes no block of its own.
toIRGenerate meta (Expr ti (InjF (Named name) [a]))
  | isCollapse name, pType ti /= Deterministic = do
  moments <- scoped (momentsOf meta a)
  return (closeExpr moments (\(mu, sigma) -> IROp OpPlus mu (IROp OpMult sigma (IRSample IRNormal))))
toIRGenerate meta (Expr ti (InjF (Named name) params)) = do
  -- Assuming that the logic within packParamsIntoLetinsGen typeEnv is correct.
  -- You will need to process vars and params, followed by recursive calls to fwdExpr.
  let resolvedName = resolveInjF (rType ti) name
  fPair <- instantiate mkVariable (adtDecls meta) resolvedName
  let FPair fwd _ = fPair
  let FDecl {inputVars=vars, body=fwdExpr} = fwd
  prefix <- mkVariable ""
  letInBlock <- packParamsIntoLetinsGen meta vars params fwdExpr
  return $ irMap (uniqueify vars prefix) letInBlock
toIRGenerate meta (Expr _ (Var name)) = do
  case lookup name (typeEnv meta) of
    -- Var is a function
    Just (TArrow _ _, hasInference) ->
      let fullName = if hasInference then name ++ "_gen" else name in
        return $ IRVar fullName
    -- Var is a top level declaration (an therefor has a _gen function)
    Just (_, True) -> do
      return $ IRVar (name ++ "_gen")
    -- Var is a local variable
    Just (_, False) -> do
      return $ IRVar name
    -- Invariant, not a refusal (task static-refusals-become-absent-variants): every bound name is in the type env.
    Nothing -> error ("Could not find name in TypeEnv: " ++ name)
toIRGenerate meta (Expr t (Lambda name subExpr)) =
  IRLambda name <$> toIRGenerate (extendMetaForLambda meta t name) subExpr
-- A dead binding draws nothing anyone reads, so its argument is not emitted:
-- the value is the body's either way. Beyond saving the work, this is what
-- keeps a Deterministic expression's generate-and-compare probability free of
-- a sample -- @(\a -> (\b -> a) (if Uniform < 0.5 then 2 else 1)) 0.0@ is
-- typed Deterministic, and its probability function used to carry the unread
-- draw and be refused as generate-backed (fuzz-admission-oracle-bugs item 7).
toIRGenerate meta (Expr _ (Apply (Expr t (Lambda x deadBody)) _))
  | not (x `Set.member` freeVarsExpr deadBody) =
  toIRGenerate (extendMetaForLambda meta t x) deadBody
toIRGenerate meta (Expr _ (Apply l v)) = do
  l' <- toIRGenerate meta l
  v' <- toIRGenerate meta v
  return $ IRApply l' v'
toIRGenerate meta (Expr _ (ReadNN name subexpr)) = do
  sub <- toIRGenerate meta subexpr
  return $ IRApply (IRVar (name ++ "_auto_gen")) sub


packParamsIntoLetinsGen :: CompilerMetadata -> [String] -> [Expr] -> IRExpr -> CompilerMonad  IRExpr
packParamsIntoLetinsGen _ [] [] expr = return $ expr
-- Invariant, not a refusal (task static-refusals-become-absent-variants): an InjF's declared input variables match its arity.
packParamsIntoLetinsGen _ [] _ _ = error "More parameters than variables"
packParamsIntoLetinsGen _ _ [] _ = error "More variables than parameters"
packParamsIntoLetinsGen meta (v:vars) (p:params) expr = do
  pExpr <- toIRGenerate meta p
  e <- packParamsIntoLetinsGen meta vars params expr
  return $ IRLetIn v pExpr e

-- | Enumerate the application of a conditional/enumerable lambda to a discrete
-- argument. Computes sum over the argument's discrete support of
-- P(arg = value) * P_enum(body | bound = value). Shared by the top-level inference
-- rule and by toIREnumerate, so that nested enumerable `let`s
-- (`let c = .. in let d = .. in ..`) enumerate at every level instead of generating
-- the inner draws forward.
enumerateAppliedLambda :: CompilerMetadata -> Bool -> Expr -> Expr -> IRExpr -> CompilerMonad PResult
enumerateAppliedLambda meta cumulative l v sample =
  enumerateBinding meta l v Nothing (\bodyMeta lBodyExpr -> toIREnumerate bodyMeta cumulative lBodyExpr sample)

-- | 'enumerateAppliedLambda' with the body's compilation handed in: the sum
-- over the argument's support of P(arg = value) times what @body@ returns,
-- given the meta with the bound variable fixed and the lambda's body (renamed
-- if its parameter clashed with a variable the argument reads).
-- 'factoredDrawStack' passes a body of its own, the operands of one
-- independent component, and may pass the argument's measure already
-- tabulated ('drawMeasureTable').
enumerateBinding :: CompilerMetadata -> Expr -> Expr -> Maybe MarginalTable
                 -> (CompilerMetadata -> Expr -> CompilerMonad PResult) -> CompilerMonad PResult
enumerateBinding meta l v preTable compileBody = do
  let lCn = chainName (getTypeInfo l)
  let (_, paramVar, bodyCn, _) = equivalentLambda "enumerateAppliedLambda" (fcData meta) lCn
  let fExprs = map snd (functions (compilingProgram meta))
  -- The loop binds the lambda's parameter around both the body and the
  -- argument's own measure, so an argument mentioning a variable of the same
  -- name -- @h b = ..@ called as @h b@ from inside an enclosing @draw b@ --
  -- would read the loop variable instead: its measure became @b == b@, always
  -- true, and the draw's weight vanished from the sum. Such a parameter is
  -- renamed to a fresh name first (task
  -- rewrite-invariance-net-draw-apply-helper-alias). A name the argument
  -- binds clashes as well: the measure is compiled at the loop variable, so a
  -- binder of the same name inside the argument (@observe .. (\m -> m > 0)@
  -- passed to @f m = ..@) shadows it, and the measure compared the argument's
  -- own value with itself (task callee-body-name-sensitive-across-call).
  (boundVar, lBodyExpr) <-
    if paramVar `Set.member` allNamesExpr v
      then do
        fresh <- mkVariable paramVar
        return (fresh, renameFreeVar paramVar fresh (findExprWithCN fExprs bodyCn))
      else return (paramVar, findExprWithCN fExprs bodyCn)
  let newTypeEnv = (boundVar, (rType (getTypeInfo v), False)):typeEnv meta
  let discreteVVals = head [x | DiscreteValues x <- tags (getTypeInfo v)]
  -- Inside an enclosing enumeration, the argument's measure is tabulated once
  -- per domain value ahead of this loop rather than recomputed in it (task
  -- split-read-field-leaf-rebuilt-per-world). The cells depend on this loop's
  -- variable only through the constant key each is compiled at, so they land
  -- in the enclosing scope, and every enclosing loop whose variable they do
  -- not read hoists them out in turn ('hoistInvariantBindings'). A field read
  -- of a split neural record at enumeration depth @k@ is then measured @2k@
  -- times instead of @2^(k+1) - 2@. At the outermost loop the table would
  -- only rearrange the same @|domain|@ measures, so it is not built there.
  -- Under --batched, 'SPLL.IRLeafTablePass' tabulates a nested neural leaf
  -- after optimization instead, as one gathered table ('nestedDrawTables').
  table <- case preTable of
    Just t -> return (Just t)
    Nothing
      | not (nestedDrawTables meta) -> return Nothing
      | otherwise -> drawMeasureTable meta v
  irTuple <- scoped (do
    pBranch <- case table of
      Just tbl -> return (lookupMarginal meta tbl (IRVar boundVar))
      Nothing  -> (unP . rProb) <$> toIRInference meta False (drawMeasured meta v) (IRVar boundVar)
    -- Inside the loop the bound variable holds one fixed domain value, so it is
    -- recorded as recovered, exactly as 'residueFactor' records a variable fixed
    -- at its witness. Only a body that leaves the enumeration for 'toIRInference'
    -- reads this (the over-budget nested application in 'toIREnumerate'); there
    -- the plan traversal must see the loop variable as fixed, not as an enclosing
    -- random binding shared across factors ('planFactorExternals').
    let bodyMeta = recoverVars [boundVar] meta{ typeEnv=newTypeEnv
                       , fixedLatents = Set.insert (chainName (getTypeInfo v)) (fixedLatents meta)
                       , dimAwareEnum = keepsDims }
    bodyRes <- compileBody bodyMeta lBodyExpr
    return (pBranch, bodyRes))
  enumSumTerms meta dimBound boundVar discreteVVals irTuple
  where
    (keepsDims, dimBound) = enumSumDims meta (rType (getTypeInfo l))

-- | A draw's argument as 'enumerateBinding' measures it: with the enclosing
-- enumerated latents fixed. Inside their loops each holds one value, and a
-- curried helper call such as @contrib u 1@ (u enumerated outside) is only
-- measurable as a call with deterministic arguments once @u@ reads as one.
drawMeasured :: CompilerMetadata -> Expr -> Expr
drawMeasured meta v = reinferRecovered meta (recoveredVars meta) v

-- | Whether 'enumerateBinding' tabulates a draw's measure ahead of its loop:
-- inside an enclosing enumeration, and not under --batched.
nestedDrawTables :: CompilerMetadata -> Bool
nestedDrawTables meta = not (Set.null (fixedLatents meta)) && not (batched (compilerConfig meta))

-- | The measure of a draw's argument at each value of its domain, one
-- let-bound cell per value, bound in the current scope ('pointQueryTable',
-- which declines a domain or a measure too large to unroll).
drawMeasureTable :: CompilerMetadata -> Expr -> CompilerMonad (Maybe MarginalTable)
drawMeasureTable meta v =
  pointQueryTable meta (drawMeasured meta v)
    (multiValueToValueList (head [x | DiscreteValues x <- tags (getTypeInfo v)]))

-- | A stack of enumerable @draw@s directly over a field constructor, with its
-- operands split into the groups that share nothing random (task
-- answer-record-shared-fields-enumerated-jointly).
--
-- > draw a1 = .. in draw b1 = .. in draw a2 = .. in draw b2 = .. in
-- > Ans a1 b1 (a1 && b1) a2 b2 (a2 && b2)
--
-- is what 'SPLL.DrawSinking' leaves of a record of answers over one split
-- neural read: @a1@ is read by two operands, so it cannot sink into either,
-- and the stack enumerates every field jointly, @2^(2N)@ worlds at @N@ groups.
-- Given the scope the stack sits in, a draw is an independent sample of the
-- variables its value reads, and a constructor's probability is the product
-- of its fields' ('isFieldConstructor'). So operands that share no draw,
-- transitively through the draws' own values, and no random enclosing local,
-- are independent, and the probability is the product over the groups of
-- each group's own sum over its own draws: @N * 4@ worlds here.
--
-- A group is a component of the graph linking an operand to each stack draw
-- it reads, a draw to each earlier draw its value reads, and anything that
-- reads a random enclosing local to every other reader of it. A local counts
-- as random unless an enclosing enumeration or witness fixed it
-- ('recoveredVars') or every occurrence of it is typed 'Deterministic' (a
-- query argument, @img@ above). Taken only when that yields two groups or
-- more, and declined when a draw is read by no operand at all: such a draw is
-- a factor of its own, which this would have to prove sums to one.
data DrawStack = DrawStack
  { dsBinds :: [(Expr, Expr)]
    -- ^ each draw's lambda and value, outermost first
  , dsCtor  :: (RType, String, [Expr])
    -- ^ the constructor's type, name and operands
  , dsComps :: [([Int], [Int])]
    -- ^ per group, its draws (indices into 'dsBinds', in stack order) and its
    -- operands (indices into the constructor's operands)
  }

drawStack :: CompilerMetadata -> Expr -> Maybe DrawStack
drawStack meta e0 = do
  (binds, (rt, c, ops)) <- peel e0
  if null binds then Nothing else Just ()
  let k = length binds
      stackVars = Set.fromList [ x | (Expr _ (Lambda x _), _) <- binds ]
      bindReads = [ freeVarsExpr v | (_, v) <- binds ]
      opReads = map freeVarsExpr ops
      nodeExprs = map snd binds ++ ops
      nodeReads = bindReads ++ opReads
      linkingOuter i = Set.toList (Set.filter isRandomLocal (randomReads (nodeExprs !! i)
                                     `Set.intersection` (nodeReads !! i)))
      isRandomLocal u = not (u `Set.member` stackVars) && u `notElem` recoveredVars meta
                        && case lookup u (typeEnv meta) of
                             Just (t, False) -> not (isTArrowType t)
                             _ -> False
      bindIdx = Map.fromList [ (x, j) | (j, (Expr _ (Lambda x _), _)) <- zip [0 :: Int ..] binds ]
      outerNames = nub (concatMap linkingOuter [0 .. length nodeExprs - 1])
      outerIdx u = length nodeExprs + fromJust (elemIndex u outerNames)
      edges i = [ j | x <- Set.toList (nodeReads !! i), Just j <- [Map.lookup x bindIdx] ]
                ++ map outerIdx (linkingOuter i)
      directed = [ (i, j) | i <- [0 .. length nodeExprs - 1], j <- edges i ]
      undirected = directed ++ [ (j, i) | (i, j) <- directed ]
      allNodes = [0 .. length nodeExprs + length outerNames - 1]
      graph = [ (n, n, [ j | (i, j) <- undirected, i == n ]) | n <- allNodes ]
      comps = [ (sort [ n | n <- ns, n < k ], sort [ n - k | n <- ns, n >= k, n < k + length ops ])
              | scc <- stronglyConnComp graph, let ns = flattenSCC scc ]
      groups = filter (\(bs, os) -> not (null bs && null os)) comps
  if length (filter (not . null . snd) groups) < 2 then Nothing else Just ()
  if any (null . snd) groups then Nothing else Just ()
  return (DrawStack binds (rt, c, ops) groups)
  where
    peel (Expr _ (Apply l@(Expr _ (Lambda x b)) v))
      | isEnumerableApplication meta l v
      , enumerationWithinMaterializationBudget meta (tags (getTypeInfo v))
      , calleeBodyInScope meta l
      , isNothing (agreementShape meta l v)
      , not (x `Set.member` freeVarsExpr v)
      , not (isRecoveredVar v) = do
          (rest, ctor) <- peel b
          return ((l, v) : rest, ctor)
    peel (Expr ti (InjF (Named c) ops))
      | isFieldConstructor (adtDecls meta) c = Just ([], (rType ti, c, ops))
    peel _ = Nothing
    isRecoveredVar (Expr _ (Var x)) = x `elem` recoveredVars meta
    isRecoveredVar _ = False
    randomReads ex = Set.fromList [ n | Expr ti (Var n) <- subtreesOf ex, pType ti /= Deterministic ]
    subtreesOf ex = ex : concatMap subtreesOf (getSubExprs ex)

-- | The probability of a 'DrawStack': the product over its groups of each
-- group's sum over its own draws, nested in stack order with
-- 'enumerateBinding' exactly as 'enumerateAppliedLambda' nests them, of the
-- product of its operands' fields. Inside the loops an operand is compiled as
-- 'toIREnumerate' compiles the whole constructor (forward and compare, or
-- handed to inference where it draws fresh randomness); a group without draws
-- is plain inference, as in the field-constructor rule.
factoredDrawStack :: CompilerMetadata -> Bool -> DrawStack -> IRExpr -> CompilerMonad PResult
factoredDrawStack meta cumulative ds sample = do
  let (rt, c, ops) = dsCtor ds
      resolvedName = resolveInjF rt c
  FPair fwd inversions <- instantiate mkVariable (adtDecls meta) resolvedName
  let outV = soleOutputVar fwd
      inlineSample = irMap (\e -> case e of IRVar n | n == outV -> sample; _ -> e)
      fields = [ (inlineSample invBody, inlineSample appT, decons)
               | inV <- inputVars fwd
               , let FDecl {body=invBody, applicability=appT, deconstructing=decons} = inversionFor resolvedName inV inversions ]
  -- The conjunction of the fields' applicability tests guards every group and
  -- the product, so it is bound once rather than copied into each.
  applicable <- case foldr1 (IROp OpAnd) [ a | (_, a, _) <- fields ] of
    c'@(IRConst _) -> return c'
    conj -> do
      v <- mkVariable "applicable"
      setVariables [(v, conj)]
      return (IRVar v)
  -- Nested in an enclosing enumeration, a draw whose value reads no other
  -- draw of the stack is tabulated here, outside the guard below: inside it
  -- the cells could not leave the guarded block, which reads the enclosing
  -- loop's variable, and would be rebuilt at every enclosing world (task
  -- split-read-field-leaf-rebuilt-per-world). Out here the enclosing loops
  -- hoist them as they hoist any invariant binding. The cells read no part of
  -- the sample, which is all the guard protects.
  let stackVars = Set.fromList [ x | (Expr _ (Lambda x _), _) <- dsBinds ds ]
  tables <- if not (nestedDrawTables meta) then return [] else
    fmap catMaybes $ forM (zip [0 :: Int ..] (dsBinds ds)) $ \(j, (_, v)) ->
      if Set.null (freeVarsExpr v `Set.intersection` stackVars)
        then fmap (\t -> (j, t)) <$> drawMeasureTable meta v
        else return Nothing
  groupRes <- forM (dsComps ds) $ \(bis, ois) ->
    guardedSubInference meta [applicable]
      (group meta [ (dsBinds ds !! j, lookup j tables) | j <- bis ] [ (ops !! i, fields !! i) | i <- ois ])
  return (guardP sr [applicable] (foldl1 (prodP sr) groupRes))
  where
    sr = semiringOf meta
    group m [] opFs = productOf <$> mapM (\(op, (fs, _, decons)) ->
                        (if decons then toIRInferenceSave else toIRInference) m cumulative op fs) opFs
    group m binds opFs = inLoops m binds opFs
    inLoops m [] opFs = productOf <$> mapM (\(op, (fs, _, _)) -> leaf m op fs) opFs
    inLoops m (((l, v), tbl) : rest) opFs = enumerateBinding m l v tbl (\bm _ -> inLoops bm rest opFs)
    -- An ANY field matches anything, which the whole-constructor comparison
    -- this replaces got from comparing ADT values; the operand's own term is
    -- compiled only for a field that is not ANY.
    leaf m op fs = do
      let anyField = IRUnaryOp OpIsAny fs
      res <- guardedSubInference m [notIR anyField] (operandTerm m op fs)
      return (zipResult (IRIf anyField) (detP (srOne sr)) res)
    -- A bare draw: compare its value to the field.
    operandTerm m op@(Expr _ (Var _)) fs = do
      opIR <- toIRGenerate m op
      let rt = rType (getTypeInfo op)
      forwardOrInfer m cumulative op fs [("operand", op, opIR)] $ return $
        if cumulative
          then mass (compareValueExpr sr rt opIR fs)
          else indicatorP sr (leafEqIR rt fs opIR)
    operandTerm m op fs = toIREnumerate m cumulative op fs
    productOf = foldl1 (prodP sr)


-- | A conjunction of Boolean clauses over enumerable draws, compiled by
-- variable elimination (task grid-constraint-network-enumerated-jointly).
--
-- > draw x1 = readD a in .. draw x9 = readD i in
-- > diff3 x1 x2 x3 && diff3 x4 x5 x6 && .. && diff3 x3 x6 x9
--
-- Every draw sits in two clauses (a row and a column), so after
-- 'SPLL.DrawSinking' most of them still sit above the whole conjunction, and
-- the nested enumeration walks close to the joint of all nine reads: @10^9@
-- terms per call, more than ten minutes. The probability that the conjunction
-- holds is a sum over the draws of a product of factors, one per draw (its
-- measure) and one indicator per clause, which variable elimination sums one
-- draw at a time: summing out a draw multiplies the factors that mention it
-- into a table over the draws they also mention ('eliminationOrder' picks the
-- draw whose table is smallest). The tables are nested rank-1 tensors indexed
-- by domain position ('BIota'), built at run time, so the code stays linear in
-- the program and the cost is the sum of the table sizes times the eliminated
-- domain.
--
-- The shape is a tree of @&&@ whose inner nodes may carry draws (where
-- sinking left them) and whose leaves are the clauses. It is sound to hoist
-- every draw to the top: each is still one sample covering every use of its
-- name, which the checks below make unique and not captured; and a draw's
-- measure is a factor of the joint whether or not the clause that reads it is
-- evaluated. The leaves must be deterministic given the draws (re-inferred
-- with the draws pinned), and no draw may read another draw or a random
-- enclosing local, so the draws are independent and their factors unary.
--
-- @P(False)@ is the total measure (the product of the draws' own totals)
-- minus @P(True)@, a subtraction on exact sums, which is why the rule is
-- declined under topK (and under branch counting, whose counts it does not
-- reproduce) and under a semiring that has no subtraction (max-product). It is
-- taken only where it pays: the clause hypergraph has a cycle (an acyclic
-- network is what sinking already factorises) and the elimination costs less
-- than a quarter of the joint enumeration.
data ConstraintNet = ConstraintNet
  { cnDraws   :: [(String, Expr)]
    -- ^ each draw's binder and value, in the order the walk met them
  , cnClauses :: [(Expr, [Int])]
    -- ^ each clause and the draws it reads (indices into 'cnDraws')
  , cnOrder   :: [Int]
    -- ^ the elimination order
  }

constraintNet :: CompilerMetadata -> Expr -> Maybe ConstraintNet
constraintNet meta e0 = do
  let conf = compilerConfig meta
      sr = semiringOf meta
  need (not (countBranches conf) && isNothing (topKThreshold conf))
  need (srReduceOp sr `elem` [ROpAdd, ROpLogSumExp])
  need (rType (getTypeInfo e0) == TBool && rootShape e0)
  (draws, leaves) <- collect e0
  let names = map fst draws
      nameSet = Set.fromList names
      domains = [ take 1 [ mv | DiscreteValues mv <- tags (getTypeInfo v) ] | (_, v) <- draws ]
  need (length draws >= 2 && Set.size nameSet == length names)
  need (Set.null (nameSet `Set.intersection` freeVarsExpr e0))
  need (all ((== 1) . length) domains)
  need (all (Set.null . Set.intersection nameSet . freeVarsExpr . snd) draws)
  let sizes = [ length (multiValueToValueList mv) | [mv] <- domains ]
      idx = Map.fromList (zip names [0 :: Int ..])
      clauses = [ (c, sort [ j | x <- Set.toList (freeVarsExpr c), Just j <- [Map.lookup x idx] ]) | c <- leaves ]
  need (all ((== TBool) . rType . getTypeInfo) leaves)
  -- a pruned observation's hole is a unit factor, not a value to compare
  need (null [ () | Expr _ (Constant VAny) <- concatMap subtreesOf leaves ])
  need (cyclicIncidence (length draws) (map snd clauses))
  let (order, veCost) = eliminationOrder sizes (map snd clauses)
  need (4 * veCost < product (map toInteger sizes))
  -- The semantic checks last: they re-run modality inference.
  need (not (any (readsRandomLocal nameSet) (map snd draws ++ leaves)))
  let pins = names ++ recoveredVars meta
  need (all (\c -> pType (getTypeInfo (reinferRecovered meta pins c)) == Deterministic) leaves)
  return (ConstraintNet draws clauses order)
  where
    need b = if b then Just () else Nothing
    rootShape (Expr _ (Apply (Expr _ (Lambda _ _)) _)) = True
    rootShape (Expr _ (InjF (Named "and") [_, _])) = True
    rootShape _ = False
    collect (Expr _ (Apply l@(Expr _ (Lambda x b)) v))
      | isDraw l v = do
          (ds, cs) <- collect b
          return ((x, v) : ds, cs)
    collect (Expr _ (InjF (Named "and") [p, q])) = do
      (d1, c1) <- collect p
      (d2, c2) <- collect q
      return (d1 ++ d2, c1 ++ c2)
    collect leaf = Just ([], [leaf])
    -- The lambda is literal, and its body is walked here rather than
    -- resolved through chain names, so 'calleeBodyInScope' does not apply
    -- (it would see the names the enclosing draws of the net bind as unbound).
    isDraw l v = pType (getTypeInfo v) /= Deterministic
      && isEnumerableApplication meta l v
      && enumerationWithinMaterializationBudget meta (tags (getTypeInfo v))
      && isNothing (agreementShape meta l v)
    -- as in 'drawStack': a local neither fixed by an enclosing engine nor
    -- typed 'Deterministic' at every occurrence couples what reads it
    readsRandomLocal netVars ex = any (isRandomLocal netVars) (Set.toList (randomReads ex))
    isRandomLocal netVars u = not (u `Set.member` netVars) && u `notElem` recoveredVars meta
      && case lookup u (typeEnv meta) of
           Just (t, False) -> not (isTArrowType t)
           _ -> False
    randomReads ex = Set.fromList [ n | Expr ti (Var n) <- subtreesOf ex, pType ti /= Deterministic ]
    subtreesOf ex = ex : concatMap subtreesOf (getSubExprs ex)

-- | Whether the incidence graph of @n@ variables and the clauses over them
-- (each a list of variables) has a cycle: more edges than a forest on its
-- nodes could hold.
cyclicIncidence :: Int -> [[Int]] -> Bool
cyclicIncidence n scopes0 =
  let scopes = filter (not . null) scopes0
      nodes = n + length scopes
      edges = [ (n + c, v) | (c, s) <- zip [0 ..] scopes, v <- s ]
      adj = Map.fromListWith (++) (concat [ [(a, [b]), (b, [a])] | (a, b) <- edges ])
      graph = [ (u, u, Map.findWithDefault [] u adj) | u <- [0 .. nodes - 1] ]
      comps = length (stronglyConnComp graph)
  in length edges > nodes - comps

-- | A greedy elimination order for variables of the given domain sizes under
-- factors over the given scopes (one unary factor per variable is implied),
-- and its cost: the sum, over the eliminations, of the size of the table
-- built times the eliminated domain. Each step eliminates the variable whose
-- factors span the fewest assignments.
eliminationOrder :: [Int] -> [[Int]] -> ([Int], Integer)
eliminationOrder sizes scopes0 =
  go (Set.fromList [0 .. n - 1]) (map Set.fromList (filter (not . null) scopes0)) [] 0
  where
    n = length sizes
    sz v = toInteger (sizes !! v)
    span' fs v = Set.insert v (Set.unions [ s | s <- fs, v `Set.member` s ])
    weight fs v = product (map sz (Set.toList (span' fs v)))
    go remaining fs acc cost
      | Set.null remaining = (reverse acc, cost)
      | otherwise =
          let v = snd (minimum [ (weight fs u, u) | u <- Set.toList remaining ])
              (touch, rest) = partition (Set.member v) fs
              merged = Set.delete v (Set.unions touch)
              fs' = if Set.null merged then rest else merged : rest
          in go (Set.delete v remaining) fs' (v : acc) (cost + weight fs v)

-- | A factor of a 'ConstraintNet' during elimination.
data NetFactor
  = NFUnary Int            -- ^ a draw's measure, indexed by its position
  | NFClause IRExpr [Int]  -- ^ a clause, reading the draws by name
  | NFTable Varname [Int]  -- ^ a table built by an elimination, nested in scope order

netFactorScope :: NetFactor -> [Int]
netFactorScope (NFUnary k) = [k]
netFactorScope (NFClause _ s) = s
netFactorScope (NFTable _ s) = s

-- | The probability of a 'ConstraintNet' by variable elimination; see
-- 'ConstraintNet'. Every table is let-bound in the current scope, ahead of
-- the result, which reads the sample only at its root.
compileConstraintNet :: CompilerMetadata -> ConstraintNet -> IRExpr -> CompilerMonad PResult
compileConstraintNet meta net sample = do
  let draws = cnDraws net
      doms = [ head [ mv | DiscreteValues mv <- tags (getTypeInfo v) ] | (_, v) <- draws ]
      sizes = map (length . multiValueToValueList) doms
      reduceSum t = IRBuiltin (BReduce (srReduceOp sr) 0) [t]
      iota k = IRBuiltin (BIota [EFixed (sizes !! k)]) []
  domVars <- forM draws (const (mkVariable "net_dom"))
  setVariables (zip domVars (map tensorDomainSR doms))
  unaryVars <- forM (zip draws doms) $ \((_, v), mv) -> do
    xv <- mkVariable "net_val"
    o <- scoped (unP . rProb <$> toIRInference meta False (drawMeasured meta v) (IRVar xv))
    u <- mkVariable "net_unary"
    setVariables [(u, IRBuiltin BMap [IRLambda xv (closeExpr o id), tensorDomainSR mv])]
    return u
  let metaC = recoverVars (map fst draws) meta { typeEnv = [ (x, (rType (getTypeInfo v), False)) | (x, v) <- draws ] ++ typeEnv meta }
  clauseIRs <- mapM (toIRGenerate metaC . fst) (cnClauses net)
  let eliminate fs k = do
        let (touch, rest) = partition (elem k . netFactorScope) fs
            newScope = sort (nub (concatMap netFactorScope touch)) \\ [k]
        ivs <- Map.fromList <$> forM (k : newScope) (\v -> (,) v <$> mkVariable "net_i")
        let ix v = IRVar (ivs Map.! v)
            weightOf (NFUnary j) = Just (IRBuiltin (BIndex 0) [IRVar (unaryVars !! j), ix j])
            weightOf (NFTable t s) = Just (foldl (\acc v -> IRBuiltin (BIndex 0) [acc, ix v]) (IRVar t) s)
            weightOf NFClause{} = Nothing
            conds = [ c | NFClause c _ <- touch ]
            prod = foldl1 (srTimes sr) (mapMaybe weightOf touch)
            guarded = if null conds then prod else IRIf (foldr1 andIR conds) prod (srZero sr)
            -- the clauses read the draws by name: bound from the indices
            readVars = nub (concat [ s | NFClause _ s <- touch ])
            summand = foldr (\v acc -> IRLetIn (fst (draws !! v)) (IRBuiltin (BIndex 0) [IRVar (domVars !! v), ix v]) acc)
                            guarded readVars
            inner = reduceSum (IRBuiltin BMap [IRLambda (ivs Map.! k) summand, iota k])
            table = foldr (\v acc -> IRBuiltin BMap [IRLambda (ivs Map.! v) acc, iota v]) inner newScope
        t <- mkVariable "net_table"
        setVariables [(t, table)]
        return (NFTable t newScope : rest)
  final <- foldM eliminate ([ NFUnary k | k <- [0 .. length draws - 1] ]
                            ++ [ NFClause c s | (c, (_, s)) <- zip clauseIRs (cnClauses net) ])
                   (cnOrder net)
  let constConds = [ c | NFClause c [] <- final ]
      scalars = [ IRVar t | NFTable t [] <- final ]
      holds = foldl1 (srTimes sr) scalars
      truth = if null constConds then holds else IRIf (foldr1 andIR constConds) holds (srZero sr)
  tVar <- mkVariable "net_true"
  zVar <- mkVariable "net_total"
  setVariables [ (tVar, truth)
               , (zVar, foldl1 (srTimes sr) [ reduceSum (IRVar u) | u <- unaryVars ]) ]
  opaqueMass sr (IRIf (IRUnaryOp OpIsAny sample) (IRVar zVar)
                   (IRIf sample (IRVar tVar) (measureDiffSR sr (IRVar zVar) (IRVar tVar))))
             const0
  where
    sr = semiringOf meta

-- | The enumerable @draw@s an expression reads through the shapes
-- 'latentCellSum' walks: a draw (an applied literal lambda whose argument is
-- random and enumerable within the dense budget given the draws above it),
-- and an 'InjF' over such operands. Whatever else is reached is a leaf, which
-- 'latentCellSum' generates forward and declines if it draws fresh
-- randomness. That is the shape 'DrawSinking' leaves the enumerated operand
-- of a noisy observation in: @(draw x = r1 in draw y = r2 in f x y) + Normal
-- * s@, or with the draws sunk further into @f@'s operands.
--
-- Purely structural on purpose: whether a leaf is deterministic given the
-- draws is asked of its generated IR ('randomDrawSites', the test
-- 'toIREnumerate' applies to an enumerated body), not by re-inferring the
-- leaf -- a re-inference is a whole modality pass, and on the 1090-value
-- operator fold it cost several times the rest of the compile.
latentCellBinders :: CompilerMetadata -> Expr -> [String]
latentCellBinders meta = go (recoveredVars meta)
  where
    go fixed e
      | Expr _ (Apply (Expr _ (Lambda x b)) v) <- e
      , latentCellDraw meta fixed v = x : go (x : fixed) b
      | Expr _ (InjF (Named _) ops) <- e = concatMap (go fixed) ops
      | otherwise = []

-- | Is @v@, the value of a @draw@ with @fixed@ already enumerated, one
-- 'latentCellSum' loops over: random given them, with a finite domain within
-- the dense-enumeration budget ('enumerateAppliedLambda''s own gate).
latentCellDraw :: CompilerMetadata -> [String] -> Expr -> Bool
latentCellDraw meta fixed v =
  enumerationWithinMaterializationBudget meta (tags (getTypeInfo v))
  && pType (getTypeInfo (reinferReading meta fixed v)) /= Deterministic

-- | 'reinferRecovered' over only the recovered names @e@ reads. The others
-- cannot change its typing, and with none left there is no re-inference at
-- all -- a draw over a neural read of an argument, the common case, is typed
-- as it stands. A re-inference re-runs the modality engine, which costs a
-- tenth of a second per call on the operator fold of
-- 'latentCellBinders''s note, however small @e@ is.
reinferReading :: CompilerMetadata -> [String] -> Expr -> Expr
reinferReading meta names e = reinferRecovered meta (filter (`Set.member` freeVarsExpr e) names) e

-- | @sum_cells p(cell) * k(value(cell))@ over the joint cells of the draws
-- 'latentCellBinders' finds in @e@, one nested loop per draw, where @k@
-- compiles the term for one forward value of @e@ (an 'IRExpr' over the loop
-- variables). The terms keep their own dims and are combined as a mixture
-- ('enumMixP', @densityDim@ being the density terms' dim) in probability mode
-- and summed as CDF masses ('enumSumP') in cumulative mode -- the sums the
-- value-domain loop of the mixed enumerate-and-shift equation builds, over
-- cells instead of values. A cell with no mass is an impossible term, as a
-- value with none is there.
--
-- @k@ runs once, inside the innermost loop, and binds what it needs through
-- the writer, so its loop-invariant bindings are hoisted like any loop body's.
-- 'Nothing' (from @k@, or) when a leaf is not deterministic given the draws; the caller
-- then discards the scope this ran in.
latentCellSum :: CompilerMetadata -> Bool -> IRExpr -> Expr -> (IRExpr -> CompilerMonad (Maybe PResult)) -> CompilerMonad (Maybe PResult)
latentCellSum meta cumulative densityDim e k
  | Expr _ (Apply (Expr _ (Lambda x b)) v) <- e
  , latentCellDraw meta (recoveredVars meta) v = do
      -- As in 'enumerateAppliedLambda': the loop binds @x@ around the draw's
      -- own measure too, so a value reading another @x@ is renamed apart.
      (boundVar, drawBody) <-
        if x `Set.member` freeVarsExpr v
          then do
            fresh <- mkVariable x
            return (fresh, renameFreeVar x fresh b)
          else return (x, b)
      let sr = semiringOf meta
          bodyMeta = recoverVars [boundVar] meta{ typeEnv = (boundVar, (rType (getTypeInfo v), False)) : typeEnv meta
                         , fixedLatents = Set.insert (chainName (getTypeInfo v)) (fixedLatents meta) }
      innerO <- scoped (do
        pRaw <- (unP . rProb) <$> toIRInference meta False (reinferReading meta (recoveredVars meta) v) (IRVar boundVar)
        pVar <- mkVariable "cell_p"
        setVariables [(pVar, pRaw)]
        bodyRes <- latentCellSum bodyMeta cumulative densityDim drawBody k
        return (prodP sr (impossibleWhen (IROp OpEq (IRVar pVar) (srZero sr)) (mass (IRVar pVar))) <$> bodyRes))
      forM (openValue innerO) $ \res -> do
        let irTuple = generateLetInBlock meta (res <$ innerO)
            (outerBinds, innerTuple) = hoistInvariantBindings boundVar irTuple
            dom = head [mv | DiscreteValues mv <- tags (getTypeInfo v)]
            bc = countBranches (compilerConfig meta)
        setVariables outerBinds
        if cumulative
          then enumSumP sr bc id boundVar dom innerTuple
          else enumMixP sr bc id densityDim boundVar dom innerTuple
  | Expr ti (InjF (Named name) ops) <- e = do
      let go acc [] = do
            FPair fwd _ <- instantiate mkVariable (adtDecls meta) (resolveInjF (rType ti) name)
            let FDecl {inputVars=vars, body=fwdExpr} = fwd
            prefix <- mkVariable ""
            k (irMap (uniqueify vars prefix) (buildLetIns (zip vars (reverse acc)) fwdExpr))
          go acc (o : os) = latentCellSum meta cumulative densityDim o (\val -> go (val : acc) os)
      go [] ops
  | otherwise = do
      ir <- toIRGenerate meta e
      if null (randomDrawSites (detGenNames meta) ir)
        then k ir
        else return Nothing

-- | The partial application @f a1 .. ak@ (k >= 1) of 'Apply' @l v@, retyped
-- with the enclosing enumerated latents fixed, when the application should be
-- compiled by enumerating @v@: @f@ is a conditional top-level function, every
-- @ai@ is deterministic given the enclosing latents, the application is
-- saturated, and @v@ is a probabilistic enumerable draw. The one-argument case
-- is 'isEnumerableApplication''s; this is its curried generalisation, which
-- 'SPLL.Analysis.applyTags' tags since the same task.
--
-- A random /leading/ argument is not handled here -- 'enumerateCurriedArgument'
-- marginalises the last argument only -- and declines, leaving the node to the
-- equations that follow, exactly as before.
curriedEnumerableCallee :: CompilerMetadata -> Expr -> Expr -> Maybe Expr
curriedEnumerableCallee meta l v
  | (hd@(Expr _ (Var f)), args@(_:_)) <- flattenApplySpine l'
  , headIsConditional (fcData meta) (compilingProgram meta) hd
  , Just (TArrow _ _, True) <- lookup f (typeEnv meta)
  , all ((== Deterministic) . pType . getTypeInfo) args
  , isEnumerable (tags (getTypeInfo v))
  , pType (getTypeInfo v) /= Deterministic
  , not (returnsFunction (rType (getTypeInfo l)))
  = Just l'
  | otherwise = Nothing
  where
    l' = reinferRecovered meta (recoveredVars meta) l
    returnsFunction (TArrow _ (TArrow _ _)) = True
    returnsFunction _ = False

-- | A saturated call @f a1 .. an@ of a conditional top-level function whose
-- one non-deterministic argument @ai@ is enumerable and is not the last one
-- (that case is 'curriedEnumerableCallee''s): every other argument is
-- deterministic given the enclosing latents. Answers the call with @ai@
-- replaced by a given expression, and @ai@ itself. Two or more random
-- arguments decline, leaving the call to 'leadingArgBinding'.
leadingEnumerableArgument :: CompilerMetadata -> Expr -> Maybe (Expr -> Expr, Expr)
leadingEnumerableArgument meta expr0
  | not (isTArrowType (rType (getTypeInfo expr)))
  , (hd@(Expr _ (Var f)), args@(_:_:_)) <- flattenApplySpine expr
  , Just (TArrow _ _, True) <- lookup f (typeEnv meta)
  , [i] <- [ k | (k, a) <- zip [0 ..] args, pType (getTypeInfo a) /= Deterministic ]
  , i < length args - 1
  , ai <- args !! i
  , isEnumerable (tags (getTypeInfo ai))
  , headIsConditional (fcData meta) (compilingProgram meta) hd
  = Just (\x -> replaceSpineArg (length args - 1 - i) x expr, ai)
  | otherwise = Nothing
  where
    expr = reinferRecovered meta (recoveredVars meta) expr0

-- | @sum_x P(v = x) * P(body x = sample)@ over @v@'s domain, where @body x@ is
-- the call with @v@'s position fixed at @x@: for the curried spine
-- 'curriedEnumerableCallee' accepted, @l x@; for a leading argument,
-- 'leadingEnumerableArgument''s spine. The counterpart of
-- 'enumerateAppliedLambda', which marginalises a 'let'-bound argument through
-- its lambda body; a partial application has no lambda body of its own to
-- resolve, so the loop body is the application itself with a fresh loop
-- variable in the argument position. Inside the loop every argument is fixed,
-- so 'toIREnumerate' compiles it forward and compares (or, for a helper that
-- draws fresh randomness, hands it to the ordinary inference rules).
enumerateCurriedArgument :: CompilerMetadata -> Bool -> (Expr -> Expr) -> Expr -> IRExpr -> CompilerMonad PResult
enumerateCurriedArgument meta cumulative mkBody v sample = do
  boundVar <- mkVariable "enum_arg"
  let vTi = getTypeInfo v
      loopVar = Expr (vTi {pType = Deterministic, tags = []}) (Var boundVar)
      loopBody = mkBody loopVar
      (keepsDims, dimBound) = enumSumDims meta (rType (getTypeInfo loopBody))
      bodyMeta = recoverVars [boundVar] meta { typeEnv = (boundVar, (rType vTi, False)) : typeEnv meta
                      , dimAwareEnum = keepsDims }
  irTuple <- scoped (do
    pBranch <- (unP . rProb) <$> toIRInference meta False (reinferRecovered meta (recoveredVars meta) v) (IRVar boundVar)
    bodyRes <- toIREnumerate bodyMeta cumulative loopBody sample
    return (pBranch, bodyRes))
  let discreteVVals = head [x | DiscreteValues x <- tags vTi]
  enumSumTerms meta dimBound boundVar discreteVVals irTuple

-- | How an enumerated sum whose body measures a value of type @rt@ combines
-- its terms (task enumerated-sum-over-density-body). The first component is
-- 'dimAwareEnum' for the body: whether this sum, and every one enclosing it,
-- reports the body's dim faithfully. The second is the static dim bound the
-- dim-aware sum ('enumMinDimP') is built with, 'Nothing' when every term is
-- a mass anyway (a float-free type, which 'floatFree' covers).
--
-- A type with no static bound ('floatLeafBound' 'Nothing': a list of reals)
-- keeps the old sum, which reports a mass: there 'forwardOrInfer''s run-time
-- guard stays, and raises on a density rather than mislabelling it.
enumSumDims :: CompilerMetadata -> RType -> (Bool, Maybe Int)
enumSumDims meta rt = case floatLeafBound (adtDecls meta) (resultOf rt) of
  Nothing -> (False, Nothing)
  Just d -> (dimAwareEnum meta, if d > 0 then Just d else Nothing)
  where
    -- The bound is taken on what the enumerated body returns, which for a
    -- lambda being applied is its codomain.
    resultOf (TArrow _ b) = b
    resultOf t = t

-- | Sum the scoped terms of an enumerated variable's domain, each the body's
-- result and the mass @pBranch@ of its value, over the domain: the body
-- weighted by that mass. With a dim bound ('enumSumDims') and a body whose
-- dim is not statically 0 ('packedStaticDim') the sum keeps the terms' dims
-- ('enumMinDimP'); otherwise it is the plain mass sum 'enumSumP'. A
-- forward-and-compare indicator's dim is always statically 0, so those sums
-- emit what they did before. In the dim-aware sum a value with no mass is an
-- impossible term rather than a possible zero: the lowest possible dim
-- decides the sum's dim, and a zero-weight atom must not outvote a real
-- density (the tag over-approximates the support).
enumSumTerms :: CompilerMetadata -> Maybe Int -> Varname -> MultiValue -> Open (IRExpr, PResult) -> CompilerMonad PResult
enumSumTerms meta dimBound boundVar vals o = do
  let sr = semiringOf meta
      bc = countBranches (compilerConfig meta)
      weighted (pBranch, r) = onProb (\p -> srTimes sr p pBranch) r
      sumWith f o' = do
        let irTuple = generateLetInBlock meta o'
            (outerBinds, innerTuple) = hoistInvariantBindings boundVar irTuple
        setVariables outerBinds
        f boundVar vals innerTuple
  case dimBound of
    Just d | packedStaticDim (generateLetInBlock meta (snd <$> o)) /= Just 0 -> do
      o' <- scoped (do
        (pBranch, r) <- inline o
        w <- mkVariable "enum_weight"
        setVariables [(w, pBranch)]
        return (impossibleWhen (IROp OpEq (IRVar w) (srZero sr)) (weighted (IRVar w, r))))
      sumWith (enumMinDimP sr bc id d) o'
    _ -> sumWith (enumSumP sr bc id) (weighted <$> o)

-- | The dim of a packed result ('packResult' under its let block) when it is
-- a compile-time constant: read through the block's bindings, tuple
-- projections of constructed tuples (and of both arms of a guarded block), an
-- @if@ whose arms agree and a sum of dims. 'Nothing' when the dim depends on anything else (a run-time
-- projection of a call, a binding outside the block, an @ANY@ test).
packedStaticDim :: IRExpr -> Maybe Int
packedStaticDim e = case flattenLetIns e of
  (binds, IRConstruct TgTuple [_, IRConstruct TgTuple [d, _]]) -> staticInt (Map.fromList binds) d
  _ -> Nothing
  where
    staticInt env x = case resolve env x of
      IRConst (VInt n) -> Just n
      IRIf _ a b -> do
        n <- staticInt env a
        m <- staticInt env b
        if n == m then Just n else Nothing
      IROp OpPlus a b -> (+) <$> staticInt env a <*> staticInt env b
      _ -> Nothing
    resolve env x = case x of
      IRVar v | Just b <- Map.lookup v env -> resolve (Map.delete v env) b
      IRLetIn v b rest -> resolve (Map.insert v b env) rest
      IRDestruct AcFst t | IRConstruct TgTuple [a, _] <- resolve env t -> resolve env a
      IRDestruct AcSnd t | IRConstruct TgTuple [_, b] <- resolve env t -> resolve env b
      -- a projection of a guarded block ('closeResult'): project both arms
      IRDestruct acc t | IRIf c a b <- resolve env t -> IRIf c (IRDestruct acc a) (IRDestruct acc b)
      _ -> x


-- ===== Agreement fusion (task categorical-product-ov-fusion) =====
--
-- Two categorical variables combined by /agreement/ -- @let a = .. in let b =
-- .. in if a == b then X else Y@ -- are the product-of-experts shape: the kept
-- mass is @P_a(k) * P_b(k)@ per class, and @sum_k P_a(k) * P_b(k)@ is the
-- fusion evidence. The corpus spells it as @showcase_poe_discrete@ and
-- @observeDiscretePoE@.
--
-- Compiled by the ordinary path this is a /joint/ enumeration: the outer
-- 'enumerateAppliedLambda' loops over @a@'s domain and, inside that loop,
-- 'toIREnumerate' reaches the inner @let@ and loops over @b@'s domain again,
-- evaluating @b@'s marginal V times per outer value. That is O(V^2) and it
-- calls the second network V^2 times. At the vocabulary scale this exists for
-- (V in the tens of thousands) V^2 is four to five orders of magnitude too
-- slow, so the complexity bound is the feature, not an optimisation of it.
--
-- The fusion rewrites the double sum into dense vector algebra over the shared
-- domain. Writing @pa@/@pb@ for the two marginals, @T@/@E@ for the two arms'
-- masses against the query, and @Sb = sum_k pb(k)@:
--
-- @
--   sum_j pa(j) * sum_k pb(k) * ( [j==k] * T(j) + [j/=k] * E(j) )
--     = sum_j pa(j) * pb(j) * T(j)          -- the diagonal
--     + sum_j pa(j) * (Sb - pb(j)) * E(j)   -- everything off it
-- @
--
-- Both lines are O(V): four 'BMap's build the @[V]@ vectors, a 'BZip' with the
-- semiring's own multiply is the elementwise product the task is named for,
-- and a 'BReduce' sums. @Sb@ is one reduction of a vector that is built once.
--
-- The off-diagonal line is a /subtraction/, and that is forced rather than
-- chosen: any O(V) form of "sum over everything but the diagonal" is the total
-- minus the diagonal, because summing the off-diagonal terms directly is the
-- O(V^2) we are removing. It loses precision exactly when the agreement mass
-- approaches @Sa*Sb@ (near-certain agreement), which is the same cancellation
-- the existing @AnyExcept@ marginal-minus-one-branch site already accepts, and
-- is why 'srMinus' rather than a hand-rolled @-@ is used: log space needs
-- 'logSubExpIR'.
--
-- WHAT IS NOT FUSED, and why each refusal is cheap. Every one of them falls
-- back to 'enumerateAppliedLambda', so the behaviour is exactly today's:
--
--   * __branch counting__ (@-c@). The fused artifact really does traverse
--     fewer leaves, so its branch count is not the enumerated path's -- and
--     'bc' is documented as a measure of the compiled artifact rather than an
--     invariant of the distribution, so it /should/ differ. Refusing under
--     @-c@ keeps every existing @-c@ number exactly as it was and, better,
--     turns the corpus's own "branch counting does not change the
--     probability" property into a differential test of the fused path
--     against the unfused one.
--   * __topK__. Pruning is a per-branch decision inside the enumeration
--     loop, and the fused form has no per-branch site to hang it on. A fused
--     result would silently ignore the cutoff.
--   * __the max-product semiring__. The algebra above distributes a product
--     over a /sum/ and takes a complement; neither is valid for max, whose
--     'srMinus' is 'mapHasNoExcept' for the same reason.
--   * __an arm that reads the inner variable__. Then @E@ is @E(j,k)@, the
--     off-diagonal sum does not factor, and there is no O(V) form at all.
--   * __unequal domains__, which would make the elementwise product a
--     shape error.
--   * __operands that may share an enumerated latent__. This is the
--     correctness gate, not a performance one: @sum_k pa(k) * pb(k)@ is the
--     right joint only when the two subexpressions are independent. It is
--     answered by the decomposability analysis ('latentVerdicts'), which is
--     keyed by binary-'InjF' chain name and scope-correct -- and the
--     agreement condition @a == b@ /is/ a binary 'InjF', so the verdict for
--     exactly this node's two operands is already computed. That analysis was
--     built (design materialize-discrete-marginals) with no consumer; this is
--     its consumer. @let a = camNN i in let b = f a in if a == b then ..@ is
--     the shape it refuses.
data AgreementShape = AgreementShape
  { agVar    :: Varname     -- ^ the outer bound variable, reused as the loop variable of every emitted 'BMap'
  , agInner  :: Varname     -- ^ the inner bound variable, which the arms must not read
  , agOpA    :: Expr        -- ^ the outer operand, whose marginal is the left factor
  , agOpB    :: Expr        -- ^ the inner operand, whose marginal is the right factor
  , agDomain :: MultiValue  -- ^ the shared enumerated domain
  , agThen   :: Expr        -- ^ the arm taken when the two agree
  , agElse   :: Expr        -- ^ the arm taken when they do not
  , agRType  :: RType       -- ^ the conditional's return type, picking the query comparison
  }

-- | Recognise the agreement shape at an enumerable application, or answer
-- 'Nothing' so the caller takes the ordinary enumeration.
--
-- Recognition is at the surface-language level -- it matches the SPLL AST
-- (a nested enumerable @let@ whose body is an @if@ over an @InjF (Named "eq")@ of the
-- two bound variables), not an IR peephole. An IR-level rewrite would have to
-- prove that an arbitrary loop body is affine in an equality indicator, which
-- is symbolic algebra over IR; the source shape states it outright.
--
-- Callable only where 'enumerateAppliedLambda' is, since it resolves chain
-- names with the same partial 'equivalentLambda'.
-- | 'Control.Monad.guard' for 'Maybe', spelled locally: this module already
-- binds @guard@ as a local name for an IR guard expression in two unrelated
-- places, and importing the 'Alternative' one would shadow them.
require :: Bool -> Maybe ()
require True  = Just ()
require False = Nothing

agreementShape :: CompilerMetadata -> Expr -> Expr -> Maybe AgreementShape
agreementShape meta l v = do
  let cfg = compilerConfig meta
  -- Refusals that do not depend on the shape at all, checked first so the
  -- common non-fusing compile does no AST walking.
  require (not (countBranches cfg))
  require (topKThreshold cfg == Nothing)
  require (srReduceOp (semiringOf meta) /= ROpMax)
  let fcd = fcData meta
      fExprs = map snd (functions (compilingProgram meta))
      (_, vOuter, bodyACN, _) = equivalentLambda "agreementShape" fcd (chainName (getTypeInfo l))
      bodyA = findExprWithCN fExprs bodyACN
  (l2, v2) <- case node bodyA of
    Apply a b | isEnumerableApplication meta a b -> Just (a, b)
    _ -> Nothing
  let (_, vInner, bodyBCN, _) = equivalentLambda "agreementShape/inner" fcd (chainName (getTypeInfo l2))
      bodyB = findExprWithCN fExprs bodyBCN
  (cond, thenE, elseE) <- case node bodyB of
    IfThenElse c t e -> Just (c, t, e)
    _ -> Nothing
  -- The condition must be exactly the two bound variables compared for
  -- equality, in either order.
  case node cond of
    InjF (Named "eq") [Expr _ (Var x), Expr _ (Var y)]
      | (x, y) == (vOuter, vInner) || (x, y) == (vInner, vOuter) -> Just ()
    _ -> Nothing
  -- Neither arm may read the inner variable: the off-diagonal sum only
  -- factors because the arms are constant in it. Anywhere in the arm, not
  -- just at its root -- 'varsOfExpr' alone sees only the root node, so
  -- @left (b + 10)@ used to pass and the fused body read an unbound @b@
  -- (test/cases/neural/agreementArmReadsInnerNested).
  require (Set.notMember vInner (containedVars varsOfExpr thenE))
  require (Set.notMember vInner (containedVars varsOfExpr elseE))
  -- Independence, from the decomposability analysis keyed by this very node.
  require (Map.lookup (chainName (getTypeInfo cond)) (latentVerdicts meta) == Just False)
  domA <- enumeratedDomain v
  domB <- enumeratedDomain v2
  require (domA == domB)
  return AgreementShape
    { agVar = vOuter, agInner = vInner, agOpA = v, agOpB = v2
    , agDomain = domA, agThen = thenE, agElse = elseE
    , agRType = rType (getTypeInfo bodyB) }

-- | A node's single 'DiscreteValues' domain, if it has exactly one. Total
-- where 'enumerateAppliedLambda' uses a @head@ on the same list, because a
-- missing tag here means "do not fuse" rather than a compiler bug.
enumeratedDomain :: Expr -> Maybe MultiValue
enumeratedDomain e = case [x | DiscreteValues x <- tags (getTypeInfo e)] of
  (d:_) -> Just d
  []    -> Nothing

-- | Emit the fused O(V) form for a recognised 'AgreementShape'. See the
-- commentary on 'AgreementShape' for the algebra this implements.
enumerateAgreement :: CompilerMetadata -> Bool -> AgreementShape -> IRExpr -> CompilerMonad PResult
enumerateAgreement meta cumulative ag sample = do
  let sr    = semiringOf meta
      v     = agVar ag
      dom   = agDomain ag
      rt    = agRType ag
      -- Both bound variables enter the type environment exactly as the nested
      -- enumeration would have bound them, so the arms and the operands are
      -- compiled in the scope they were written in.
      metaV = meta { typeEnv = (agVar ag,   (rType (getTypeInfo (agOpA ag)), False))
                            : (agInner ag, (rType (getTypeInfo (agOpB ag)), False))
                            : typeEnv meta }
      -- One compiled body, as a function of the shared loop variable.
      -- Bindings the sub-compilation floated are bound INSIDE the body, since
      -- it becomes a 'BMap' lambda and a loop-variable read must not escape
      -- its binder -- except for those that do not mention the loop variable
      -- at all, which are lifted out by 'hoistInvariantBindings' exactly as
      -- 'enumerateAppliedLambda' lifts them. That split is not cosmetic: the
      -- raw network call (@camNN(img)@) is loop-invariant, and leaving it
      -- inside would run the network once per class instead of once, turning
      -- an O(V) probability computation back into O(V) *network invocations*
      -- -- which at vocabulary scale is the whole cost.
      closeOver m = do
        o <- m
        let (invariant, inner) = hoistInvariantBindings v (closeExpr o id)
        setVariables invariant
        return inner
  paBody <- closeOver (scoped ((unP . rProb) <$> toIRInference metaV False (agOpA ag) (IRVar v)))
  pbBody <- closeOver (scoped ((unP . rProb) <$> toIRInference metaV False (agOpB ag) (IRVar v)))
  -- The arms are generated forward and compared against the query, exactly as
  -- 'toIREnumerate's 'IfThenElse' equation does -- including its premise
  -- check, since the fused form generates the same operands it does.
  let armMass e = do
        eIR <- toIRGenerate metaV e
        requireDeterministicUnderEnum metaV "agreement arm" e eIR
        return (eIR, if cumulative then compareValueExpr sr rt eIR sample
                                   else maskSR sr (leafEqIR rt sample eIR))
      -- 'closeOver' for an arm, also handing back the arm's generated value so
      -- 'armSum' can recognise a constructor of the loop variable.
      closeOverArm m = do
        o <- m
        let (invariant, inner) = hoistInvariantBindings v (closeExpr o snd)
        setVariables invariant
        return (fst (openValue o), inner)
  (thenIR, thenBody) <- closeOverArm (scoped (armMass (agThen ag)))
  (elseIR, elseBody) <- closeOverArm (scoped (armMass (agElse ag)))
  let mkMap b = IRBuiltin BMap [IRLambda v b, tensorDomainSR dom]
      zipSR a b  = IRBuiltin (BZip (srTimesOp sr)) [a, b]
      reduceSR t = IRBuiltin (BReduce (srReduceOp sr) 0) [t]
      -- @sum_j w(j) * M(j)@ for a weight vector @w@ and an arm's mass @M@
      -- against the query (task agreement-enumeration-point-collapse). Three
      -- forms, cheapest first; each is exactly the generic scan's value.
      --
      --   * __the arm is a constructor of the loop variable__ (@right a@) over a
      --     contiguous Int domain, for a point query: @M(j)@ is the indicator
      --     @[sample == Tag j]@, which is nonzero for at most one @j@ -- the
      --     sample's payload. So the sum is a tag test on the sample and one
      --     'BIndex' at the payload's position, O(1) after the vectors exist,
      --     where the scan built a second @[V]@ indicator vector against the
      --     query. A payload of ANY matches every @j@ (it is the plain sum of
      --     @w@), as does a top-level ANY sample; a payload outside the domain
      --     matches none. Contiguity is what makes the position arithmetic
      --     (@k - lo@) rather than a lookup; a non-contiguous domain keeps the
      --     scan, since finding the position there is itself the O(V) search.
      --   * __the arm does not read the loop variable__ (@left ()@): @M@ is a
      --     constant of the loop, so it factors out of the sum as one
      --     indicator times @sum_j w(j)@.
      --   * otherwise, the scan.
      armSum w eIR armBody
        | not cumulative
        , Just (isTag, fromTag) <- constructorOfLoopVar eIR
        , Just (lo, n) <- contiguousIntDomain dom = do
            wV <- mkVariable "agree_arm_weights"
            kV <- mkVariable "agree_key"
            setVariables [(wV, w)]
            let k = IRVar kV
                inDomain = IROp OpAnd (notIR (IROp OpLessThan k (IRConst (VInt lo))))
                                      (IROp OpLessThan k (IRConst (VInt (lo + n))))
                position = IRBuiltin (BIndex 0) [IRVar wV, IROp OpSub k (IRConst (VInt lo))]
            return $
              IRIf (IRUnaryOp OpIsAny sample) (reduceSR (IRVar wV)) $
              IRIf (IRDestruct isTag sample)
                (IRLetIn kV (IRDestruct fromTag sample)
                  (IRIf (IRUnaryOp OpIsAny k) (reduceSR (IRVar wV))
                    (IRIf inDomain position (srZero sr))))
                (srZero sr)
        | not (v `freeInIR` armBody) = return (srTimes sr armBody (reduceSR w))
        | otherwise = return (reduceSR (zipSR w (mkMap armBody)))
      -- @Tag v@, seen through the let-aliases the arm's generate compilation
      -- wraps a variable read in (@let a' = v in Right a'@).
      constructorOfLoopVar = conOf [v]
      conOf vs (IRLetIn x (IRVar y) b) | y `elem` vs = conOf (x : vs) b
      conOf vs (IRConstruct TgRight [IRVar x]) | x `elem` vs = Just (AcIsRight, AcFromRight)
      conOf vs (IRConstruct TgLeft  [IRVar x]) | x `elem` vs = Just (AcIsLeft,  AcFromLeft)
      conOf _ _ = Nothing
  -- The two marginal vectors are each read twice (the diagonal and the
  -- off-diagonal line), so they are bound once rather than rebuilt.
  paV <- mkVariable "agree_pa"
  pbV <- mkVariable "agree_pb"
  sbV <- mkVariable "agree_pb_total"
  cV  <- mkVariable "agree_complement"
  setVariables [ (paV, mkMap paBody)
               , (pbV, mkMap pbBody)
               , (sbV, reduceSR (IRVar pbV)) ]
  let -- the elementwise product of the two [V] marginals: the whole point
      product' = zipSR (IRVar paV) (IRVar pbV)
      -- (Sb - pb(j)) per element. A BMap rather than a second BZip because
      -- 'srMinus' is 'logSubExpIR' under log space, which is not an Operand.
      complement = IRBuiltin BMap [IRLambda cV (srMinus sr (IRVar sbV) (IRVar cV)), IRVar pbV]
  diagonal    <- armSum product' thenIR thenBody
  offDiagonal <- armSum (zipSR (IRVar paV) complement) elseIR elseBody
  opaqueMass sr (srPlus sr diagonal offDiagonal) const0

-- | A domain whose enumeration order ('multiValueToValueList', the order
-- 'tensorDomainSR' lays a @[V]@ vector out in) is @lo, lo+1, .., lo+n-1@, as
-- @(lo, n)@ -- so a value's position in the vector is plain subtraction.
contiguousIntDomain :: MultiValue -> Maybe (Int, Int)
contiguousIntDomain mv = case multiValueToValueList mv of
  vals@(VInt lo : _)
    | vals == map VInt [lo .. lo + length vals - 1] -> Just (lo, length vals)
  _ -> Nothing

-- | Refuse a generate-backed probability. 'toIREnumerate' compiles its operands
-- /forward/ on the premise stated at its fallback equation: with the enclosing
-- discrete latents pinned to concrete enumerated values, the operand is
-- deterministic, so generating it and comparing the result against the sample is
-- an exact indicator. When that premise does not hold the same code emits a
-- fresh random draw compared against the query value -- which is not a
-- probability at all, but a number that differs on every call with the same
-- argument, with no crash and no diagnostic on the Python and Julia backends
-- (task @self-recursive-prob-nondeterministic-fallback@).
--
-- The shape that reaches it is an unbounded self-recursive branch with no
-- decreasing argument (@main = ... if a == b then a else main@): @main@'s own
-- @_gen@ call is spliced into @main_prob@. NeST does exact inference, so this is
-- refused at compile time rather than emitted -- matching the sibling
-- witness-construction failures, which fail loudly. Solving the resulting
-- fixed-point equation algebraically was considered and declined: it would make
-- \"does my program infer?\" unpredictable from the source.
--
-- This is the local guard for the enumeration path only; the central \"no
-- generate call in any probability-mode body\" invariant is investigation
-- @generate-backed-inference-sweep@.
requireDeterministicUnderEnum :: CompilerMetadata -> String -> Expr -> IRExpr -> CompilerMonad ()
requireDeterministicUnderEnum meta what src ir =
  case nub (recursiveDrawCalls (cyclicGenNames meta Set.\\ detGenNames meta) (enclosingFunction meta src) ir) of
    [] -> return ()
    gens -> refuse cn $ init $ unlines
      [ "probability-mode compilation reached a generate-backed fallback."
      , "The " ++ what ++ " of an enumerated conditional (chain name " ++ cn ++ ") draws fresh"
      , "randomness by calling " ++ intercalate ", " gens ++ ", which is on a recursive call cycle."
      , "Measuring that call means re-entering the same enumeration with an unchanged argument,"
      , "which does not terminate, and generating it forward instead would produce a probability"
      , "function that returns a different number on every call with the same query value."
      , "NeST does exact inference, so this is refused. This is the shape of an unbounded"
      , "self-recursive branch (`... else main`), or of a call through another function on the"
      , "cycle, where no argument of a direct self-call changes. Rewrite the recursion so that"
      , "it calls itself directly with a changed argument (a counter, `tail xs`), or use the"
      , "program in generate mode only."
      , "(task self-recursive-prob-nondeterministic-fallback)" ]
  where cn = chainName (getTypeInfo src)

-- | The function whose body contains the node, with its parameter names; the
-- context 'recursiveDrawCalls' needs to tell a self-call that changes an
-- argument from one that does not. 'Nothing' when no declaration contains it.
enclosingFunction :: CompilerMetadata -> Expr -> Maybe (Varname, [Varname])
enclosingFunction meta src =
  listToMaybe [ (n ++ "_gen", params b)
              | (n, b) <- functions (compilingProgram meta), contains b ]
  where
    cn = chainName (getTypeInfo src)
    contains e = chainName (getTypeInfo e) == cn || any contains (getSubExprs e)
    params (Expr _ (Lambda x rest)) = x : params rest
    params _ = []

-- | The random calls in a generate-mode IR expression that go to a function on
-- a call cycle -- the subset of 'randomDrawSites' 'requireDeterministicUnderEnum'
-- still refuses.
--
-- A direct self-call that changes an argument is not one of them (task
-- decreasing-recursion-refused-as-generate-fallback): the call is made with a
-- different argument than the enclosing invocation received (@loop (r - 1)@,
-- @walk (tail xs)@), so its probability function is a different invocation,
-- not the same enumeration re-entered, and the callee's own probability
-- function measures it. What stays refused is a call whose every argument is
-- the enclosing function's own parameter in its own position (@... else main@),
-- any call to a different function on the cycle (mutual recursion: the
-- argument comparison says nothing there), and a bare or partial reference.
recursiveDrawCalls :: Set.Set Varname -> Maybe (Varname, [Varname]) -> IRExpr -> [String]
recursiveDrawCalls cyc encl = go
  where
    go ir = case collectApplyChain ir of
      (IRVar n, args)
        | Set.member n cyc, not (null args) ->
            [ n | not (changesArgument n args) ] ++ concatMap go args
      (IRVar n, _) | Set.member n cyc -> [n]
      _ -> concatMap go (getIRSubExprs ir)
    changesArgument n args = case encl of
      Just (self, ps) | self == n, length args == length ps ->
        or (zipWith (\p a -> a /= IRVar p) ps args)
      _ -> False

-- | The randomness sources in a generate-mode IR expression, named for a
-- diagnostic; empty exactly when 'isPureGiven' would call the expression pure.
-- The two are the optimizer's own notions of effect: an 'IRSample', and a
-- reference to a generate function not proven deterministic.
randomDrawSites :: Set.Set Varname -> IRExpr -> [String]
randomDrawSites det ir = case ir of
  IRSample d -> ["from " ++ show d]
  IRVar n | isEffectfulVar n && not (Set.member n det) -> ["by calling " ++ n]
  _ -> concatMap (randomDrawSites det) (getIRSubExprs ir)

toIREnumerate :: CompilerMetadata -> Bool -> Expr -> IRExpr -> CompilerMonad PResult
-- Nested enumerable application (e.g. an inner `let` binding a fresh discrete draw):
-- recurse with enumeration + weighting rather than generating the draw forward.
--
-- Gated on the same materialization budget as 'toIRInference''s enumerable
-- 'Apply' equation (task enumeration-budget-gate-misses-nested-application):
-- without it a small outer enumeration passes that gate and then materializes
-- an over-budget inner one densely, one level down. Over budget, the inner
-- application is handed to 'toIRInference' rather than falling through here --
-- the remaining 'toIREnumerate' equations have no plan path, and the catch-all
-- compiles the node forward and refuses it as a generate-backed fallback. In
-- 'toIRInference' the same gate declines again and dispatch reaches the
-- plan-guided arm. That is sound for the same reason 'enumerateAppliedLambda'
-- calls 'toIRInference' on its own argument: the enclosing bound variables are
-- already in 'typeEnv' as locals, so P(application = sample) there is exactly
-- the conditional this equation would otherwise have enumerated.
--
-- Not for an argument that is itself a variable this enumeration already
-- fixed (@hit x@ inside the loop over @x@): its measure is the indicator
-- @o == x@, so enumerating it again walks the whole domain for the one value
-- it keeps -- a 97-fold loop per cell on a CLEVR object slot (task
-- product-scene-discrete-count-enumerates-slot-patterns). The application is
-- deterministic given the loop, and the forward equations below compile it.
toIREnumerate meta cumulative e@(Expr _ (Apply l v)) sample
  | isEnumerableApplication meta l v
  , not (isRecoveredVar v) =
  if not (enumerationWithinMaterializationBudget meta (tags (getTypeInfo v)))
    then toIRInference meta cumulative (reinferRecovered meta (recoveredVars meta) e) sample
    else case agreementShape meta l v of
      Just ag -> enumerateAgreement meta cumulative ag sample
      Nothing
        | not cumulative, Just net <- constraintNet meta e -> compileConstraintNet meta net sample
        | Just ds <- drawStack meta e -> factoredDrawStack meta cumulative ds sample
        | otherwise -> enumerateAppliedLambda meta cumulative l v sample
  where
    isRecoveredVar (Expr _ (Var x)) = x `elem` recoveredVars meta
    isRecoveredVar _ = False
toIREnumerate meta cumulative (Expr TypeInfo{chainName=cn} (Var _)) sample = do
  let equivCN = equivalentChainName "toIREnumerate/Var" (fcData meta) cn
  let fs = map snd (functions (compilingProgram meta))
  let equivExpr = findExprWithCN fs equivCN
  toIREnumerate meta cumulative equivExpr sample
toIREnumerate meta cumulative whole@(Expr TypeInfo{rType=rt} (IfThenElse c t e)) sample = do
  let sr = semiringOf meta
  cIR <- toIRGenerate meta c
  tIR <- toIRGenerate meta t
  eIR <- toIRGenerate meta e
  forwardOrInfer meta cumulative whole sample
    [("condition", c, cIR), ("then branch", t, tIR), ("else branch", e, eIR)] $ do
    --(pBranch, _, _) <- toIRInference meta False distr elem
    -- Due to eager evaluation, we must make sure, that the wrong branch is not executed
    let condSelector resultExpr = IRIf cIR resultExpr (srZero sr)
    let notCondSelector resultExpr = IRIf (IRUnaryOp OpNot cIR) resultExpr (srZero sr)
    let thenSelector = if cumulative then compareValueExpr sr rt tIR sample else maskSR sr (leafEqIR rt sample tIR)
    let elseSelector = if cumulative then compareValueExpr sr rt eIR sample else maskSR sr (leafEqIR rt sample eIR)
    let thenRes = condSelector thenSelector
    let elseRes = notCondSelector elseSelector
    -- The two selectors are mutually exclusive (exactly one is ever "live", the
    -- other is the semiring zero), so this is a mixture-sum, not a plain add:
    -- in log space 'srZero' is negative infinity, and OpPlus-ing that against a
    -- finite log-probability would wrongly zero the whole result out.
    let returnExpr = srPlus sr thenRes elseRes
    return (mass returnExpr)
-- Fallback: under enumeration the bound variable carries a concrete enumerated value,
-- so the body is deterministic and can be generated forward and compared to the sample.
-- This covers shapes whose root is not an if, e.g. an InjF sum of conditional terms.
toIREnumerate meta cumulative e sample = do
  eIR <- toIRGenerate meta e
  forwardOrInfer meta cumulative e sample [("expression", e, eIR)] $ do
    let rt = rType (getTypeInfo e)
    if cumulative
      then return (mass (compareValueExpr (semiringOf meta) rt eIR sample))
      else return (indicatorP (semiringOf meta) (leafEqIR rt sample eIR))

-- | The premise check of 'toIREnumerate's forward-and-compare equations, with
-- the way out it used to lack (task enum-let-latent-gates-fresh-draw).
--
-- When every forward-compiled operand is deterministic given the enumerated
-- latents, the forward-and-compare body (the last argument) is exact and is
-- used. When one of them draws fresh randomness, the node is not refused but
-- handed to 'toIRInference' -- with every enclosing enumerated variable retyped
-- 'Deterministic' ('reinferRecovered' over 'recoveredVars'), since inside the
-- enumeration loop each holds one fixed domain value. That is the same step the
-- over-budget nested application in this function already takes, and it is
-- sound for the same reason: the enumerated variables are 'typeEnv' locals, so
-- P(node = sample) under the ordinary rules is exactly the conditional the
-- enumeration needs. A fresh draw then meets its usual machinery -- an @if@
-- over a fixed latent selects an arm and measures it, an @if@ over a fresh
-- Bernoulli is the ordinary mixture, a tuple factorizes -- instead of being
-- generated and compared against the query. The canonical shape is the noisy
-- observation of a shared latent,
-- @draw b = Uniform < 0.5 in (b, if b then Uniform < 0.9 else Uniform < 0.1)@,
-- which used to be refused although hoisting the noise into its own enumerable
-- binding compiled.
--
-- The refusal stays for a draw through a function on a call cycle: handing
-- that to 'toIRInference' turns @... else main@ into a @main_prob@ call with an
-- unchanged argument, which re-enters this same enumeration and never returns.
-- That is the shape 'requireDeterministicUnderEnum' was written for (task
-- self-recursive-prob-nondeterministic-fallback). A call to any recursive
-- function is refused, not only one reaching back into the function being
-- compiled: 'CompilerMetadata' does not know which one that is, and refusing
-- more keeps the old verdict rather than risking a non-terminating body.
forwardOrInfer :: CompilerMetadata -> Bool -> Expr -> IRExpr
               -> [(String, Expr, IRExpr)] -> CompilerMonad PResult -> CompilerMonad PResult
forwardOrInfer meta cumulative whole sample operands forward
  | all (null . randomDrawSites (detGenNames meta) . thd3) operands = forward
  | otherwise = do
      mapM_ (\(what, src, ir) -> requireDeterministicUnderEnum meta what src ir) operands
      res <- toIRInference meta cumulative (reinferRecovered meta (recoveredVars meta) whole) sample
      -- A delegated body can be a density (@if b then Normal else Normal +
      -- 3.0@), and whether it is one is in general a RUNTIME fact: @(x,
      -- Uniform)@ is a mass exactly when the query marginalises the second
      -- slot with @ANY@ (the fuzz-found @enumDeadLetFreshDrawTuple@ reaches
      -- this through @fst@), and topK pruning makes the dim a runtime choice
      -- even where it would otherwise fold. The enclosing enumerated sums
      -- keep their terms' dims ('enumTerm', 'enumMinDimP'; task
      -- enumerated-sum-over-density-body), so the result is returned as it
      -- is -- unless one of them sums its terms as masses ('dimAwareEnum'
      -- off: its body's type has no static dim bound, a list of reals). Then
      -- the probability is guarded at run time: a possible result with a
      -- non-zero dim raises instead of being summed as a mass. The guard is
      -- also skipped where it is statically true -- a cumulative result (a
      -- CDF value is a mass by construction), or a type with no 'TFloat'
      -- leaf, which no density ever measures -- and the optimizer folds it
      -- away where the dim is a literal 0.
      if cumulative || floatFree (adtDecls meta) (rType (getTypeInfo whole)) || dimAwareEnum meta
        then return res
        else do
          let isMass = orIR (rImposs res) (IROp OpEq (rDim res) dim0)
              refusal = IRError $ "probability-mode inference of an enumerated conditional (chain name "
                          ++ chainName (getTypeInfo whole) ++ ") met a continuous density: given the"
                          ++ " enumerated latents the query measures a fresh continuous draw, and an"
                          ++ " enumerated sum over density-valued terms of a type with no static dim bound"
                          ++ " (a list of reals) is not implemented (tasks enum-let-latent-gates-fresh-draw,"
                          ++ " enumerated-sum-over-density-body)"
          return (onProb (\p -> IRIf isMass p refusal) res)
  where thd3 (_, _, x) = x

-- | A static upper bound on the dim of a point probability of a value of the
-- type: its number of real leaves, the larger alternative for a sum type.
-- 'Nothing' when there is none (a list or tensor of reals, a recursive ADT
-- with a real field) or the type is not recognised. Used by the enumerated
-- sums ('enumSumTerms') to find the lowest dim among their terms
-- ('enumMinDimP'), which needs the bound to build its ladder.
floatLeafBound :: [ADTDecl] -> RType -> Maybe Int
floatLeafBound decls = go Set.empty
  where
    go seen t
      | floatFree decls t = Just 0
      | otherwise = case t of
          TFloat -> Just 1
          Tuple a b -> (+) <$> go seen a <*> go seen b
          TEither a b -> max <$> go seen a <*> go seen b
          TADT n
            | Set.member n seen -> Nothing
            | otherwise -> case find ((== n) . dataName) decls of
                Just d -> fmap (maximum . (0 :)) $ sequence
                            [ sum <$> mapM (go (Set.insert n seen) . snd) fs | (_, fs) <- constructors d ]
                Nothing -> Nothing
          _ -> Nothing

-- | True when no value of the type contains a 'TFloat' leaf, so a point
-- probability of it is always a mass (dim 0). Conservative: anything it does
-- not recognise (arrows, type variables, an unknown ADT) answers 'False'.
floatFree :: [ADTDecl] -> RType -> Bool
floatFree decls = go Set.empty
  where
    go seen t = case t of
      TBool -> True
      TInt -> True
      TSymbol -> True
      TUnit -> True
      ListOf a -> go seen a
      TTensor _ a -> go seen a
      Tuple a b -> go seen a && go seen b
      TEither a b -> go seen a && go seen b
      TADT n
        | Set.member n seen -> True
        | otherwise -> case find ((== n) . dataName) decls of
            Just d -> and [ go (Set.insert n seen) ft | (_, fs) <- constructors d, (_, ft) <- fs ]
            Nothing -> False
      _ -> False

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
      IRApply _ _      -> isCall v
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


-- | The 'Recur' every compile's 'CompilerMetadata' carries: the translators
-- themselves, for the engine modules below this one to call back into.
knot :: Recur
knot = Recur
  { recInference     = toIRInference
  , recInferenceSave = toIRInferenceSave
  , recGenerate      = toIRGenerate
  }
