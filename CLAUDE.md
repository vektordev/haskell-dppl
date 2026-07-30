# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository. If ever you notice that information here is outdated or substantially incomplete, you are requested to edit this file.

## Project

NeST (Neuro-Symbolic Transpiler) — a compiler for SPLL (Sum-Product Loop Programming), a probabilistic programming language. Compiles probabilistic programs to Python or Julia, supporting neural network integration and probabilistic inference (sampling, exact probability, integration).

## Build & Run

```bash
stack build                    # Build
stack test                     # Run all tests
stack run -- -i file.spll compile -o output.py -l python   # Compile to Python
stack run -- -i file.spll compile -l julia                  # Compile to Julia
stack run -- -i file.spll generate                          # Forward sampling
stack run -- -i file.spll probability -x 0.5                # Query P(X=0.5)
stack run -- -i file.spll cumulative -x 0.5                 # CDF query P(X<=0.5)
# Test selection (tasty patterns; top-level groups: Spec, Corpus, Parser, Internals, Rejection, Encode, Showcase, End2End):
stack test --ta '-p Spec'                # run one group
stack test --ta '-p "!/End2End/"'        # everything except a group
stack test --ta '-p TopK'                # any test whose name matches a substring
stack test --ta '-p "/End2End.Interpreter/ && /dice/"'   # one .ppl test case
stack test --ta '-l'                     # list all test names
# Output is quiet-on-success by default; show every test (with per-test timings) via:
TASTY_HIDE_SUCCESSES=false stack test
```


CLI flags: `-v` verbosity, `-O LEVEL` optimization (0-2), `-k CUTOFF` top-K threshold, `-c` count branches, `-t` truncate boilerplate, `-d` debug intermediates (see below).

To prevent having to run `stack test` repeatedly, e.g. to grep for specific failures, always store the test output to temporary file and grep that.

## Compilation Pipeline

```
SPLL source (.spll/.ppl)
  → Parser.hs (megaparsec)
  → AST (Lang/Lang.hs, Lang/Types.hs)
  → Type inference (Typing/RInfer.hs for return types, Typing/ModalityInfer.hs for probabilistic types)
  → IRCompiler.hs → IR (IntermediateRepresentation.hs)
     Three compilation branches: generate, probability, integrate
  → IROptimizer.hs (constant folding, CSE, let-in optimization, lambda→letIn refactoring)
  → CodeGenPyTorch.hs or CodeGenJulia.hs
```


Every SPLL program is compiled into three function variants:
1. **Generate** — forward sampling (draws random values)
2. **Probability** — computes probability density/mass at a given point
3. **Integrate** — integrates probability over a range

The availability of each depends on that inference being tractable, as determined by ModalityInfer.

Runtime execution: `IRInterpreter.hs` (`generateRand` for random sampling, `generateDet` for deterministic).

## Key Types

- **Expr** (`src/SPLL/Lang/Types.hs`): Main AST — includes `IfThenElse`, `LetIn`, `Lambda`, `Apply`, `Uniform`, `Normal`, `ReadNN`, `InjF` (injected functions like plus/mult), `Cons`, `TCons`, etc.
- **IRExpr** (`src/SPLL/IntermediateRepresentation.hs`): IR after compilation — `IRIf`, `IROp`, `IRLetIn`, `IRLambda`, `IRDensity`, `IRSample`, etc.
- **TypeInfo**: Bundle of RType (return type: `TFloat`, `TBool`, `TInt`, `ListOf`, `Tuple`, etc.), PType (probabilistic: `Deterministic`, `PNormal`, `PLogNormal`, `Integrate`, `Bottom`), and CType (constraints).
- **Value**: Runtime values — `VFloat`, `VInt`, `VBool`, `VList`, `VTuple`, `VEither`, `VClosure`, `VThetaTree`, `VSymbol`, `VBranch`, `VADT`, `VAny` (VAny is used only for marginal queries).
- **MultiValue**: Structured set of possible values for neural network output annotation — `MultiDiscretes [Value]`, `MultiTuple MultiValue MultiValue`, `MultiEither MultiValue MultiValue`, `MultiADT [(String, [MultiValue])]`, `MultiTypeRef String`.
- **CompilerConfig**: Controls verbosity, optimization level, top-K threshold, branch counting, plus flags `pruneAnyChecks`, `noIntegrate`, `noProbability`, `noGenerate`.

## Internal Details

Every AST node carries a `TypeInfo` record that accumulates annotations from successive passes:

```haskell
data TypeInfo = TypeInfo {
  rType            :: RType,           -- value structure (filled by RInfer, standard type annotations.)
  pType            :: PType,           -- probabilistic semantics (filled by ModalityInfer)
  chainName        :: ChainName,
  tags             :: [Tag]            -- enum ranges + chosen algorithm (filled by Analysis)
}
```

The annotation is held in a record wrapper around a parametric base functor, rather than
as a first field on each constructor:

```haskell
data Expr = Expr { ann :: TypeInfo, node :: ExprF Expr }
data ExprF a = IfThenElse a a a | InjF InjFName [a] | Var String | Constant Value | ...
               deriving (Show, Eq, Functor, Foldable, Traversable)
```

So a node is written and matched as `Expr ti (IfThenElse c t f)`. The derived
`Functor`/`Foldable`/`Traversable` are what let `SPLL.Lang.Lang`'s traversals
(`tMap`, `tMapM`, `tMapHead`, `getSubExprs`, `setSubExprs`, `getTypeInfo`, `setTypeInfo`)
be generic one-liners instead of per-constructor case blocks. `Constant` deliberately
holds a concrete `Value`, not a `GenericValue a`: a `Value` can embed `Expr`s inside a
`VClosure`, but those are not AST sub-expressions and must stay out of derived traversals.
`SPLL.Prelude`'s smart constructors build nodes through `mkExpr :: ExprF Expr -> Expr`.

`PType` classifies how uncertainty flows through a node, forming a partial order:

```
Deterministic  >  PNormal, PLogNormal  >  Integrate  >  Bottom
```
`PNormal` and `PLogNormal` are incomparable siblings (different distribution families); their meet is `Integrate`. Deterministic values are not affected by randomness and need no inference. `PNormal`/`PLogNormal` allow closed-form Gaussian inference shortcuts. Integrate values have a known CDF (evaluable via trusted special functions, e.g. `erf` — not necessarily closed-form). Bottom values can only be sampled from, not inferred. Each PType implies that the semantics of lower types are available. (There is deliberately no dens-only rung between `Integrate` and `Bottom`: a density whose CDF would need in-house quadrature is excluded by the language; the internal capability engine in `SPLL.Typing.Modality` still distinguishes that state and projects it to `Bottom`.)

A probabilistic `let x = v in body` whose observation cannot be point-inverted onto `x` (every path crosses a comparison or `if`) is compiled via **set-valued witnesses** (`setWitnessApply` in IRCompiler): the observation is inverted into guarded constraint-set worlds over `x` — intervals from comparisons (measured as CDF differences), case splits from conditionals, intersections across multiple occurrences — e.g. `let x = Normal in if x < 0.0 then 0.0 - x else x` yields the |Normal| density `2φ(y)`. Bodies drawing fresh randomness alongside such constraints are refused with a diagnostic.

When the bound value is a **neural network's structured output** (`let s = nn sym in <predicates over s>`), a sibling engine fires first: **plan-guided lazy enumeration** (`planWitnessApply` in IRCompiler; design plan-guided-lazy-enumeration, milestones 1–4). The NN's distribution factorizes per `PartitionPlan` slot, so the observation is inverted into worlds constraining individual plan *leaves* (allowed softmax slots per region, with per-slot runtime guards) and measured as products of logit-slice reads — no `of` clause and no support materialization needed (a 3^12-state scene compiles in O(slots); see `testCases/planEnumInline*`). M1 handles inline bodies built from accessors, `is<Ctor>`, `==`/`<`/`>` against deterministic values, boolean connectives, and `if` splits. M2 adds **recursive user-function specialization** (`testCases/planEnumRec*`): a saturated call to a top-level function whose arguments are plan slices (accessor chains) or deterministic values is specialized — its body traversed under a fresh parameter frame (`PlanEnv`) — with specializations memoized by `(body, plan offsets, det-arg IR)` and a strict-plan-descent stack guard; recursion bottoms out where the depth-unrolled plan prunes the recursive constructors (those branch worlds become statically unsatisfiable and the branch is never traversed). Value-valued folds compared against deterministic bounds (`numLarge scene > θ`) enumerate as (value, world) pairs via `planEnumValues`. M4 adds **value-grouped DP** (`planGroupValues`; `testCases/planEnumRecDeepCount`, depth-12 vs an independent oracle, and the `planEnumM4Polynomial` size test in TestInternals): the (value, world) pairs are a partition, so same-value worlds are collapsed into one world carrying their summed mass (`pwFactor` on `PlanWorld`, bound to a shared IR variable so nothing re-inlines), turning counting folds from 2^depth into O(depth²) IR — depth 30 now compiles in seconds. Two soundness guards: constraints shared identically by every world of a group (the recursion's own SCons/Obj accessor flags) stay *live* on the collapsed world (`commonDiscreteCons`) so the enclosing `if isEmpty` re-constraint still dedups rather than squaring the flag; and merging fires only when the plan-bound variable occurs **once** in the observation (`psMerge`), because a multi-predicate chain (`existsRed … numLarge …`) shares structural flags across siblings that a baked mass could not deduplicate — such chains keep the M2 world-per-path path (`planEnumRecChain` pins lazy≡materialized). Scans and threaded-bool predicates stay polynomial independently (Bool path, no value enumeration). Untouched leaves (including continuous ones) integrate out as free marginals. M3 adds **continuous-leaf constraints** (`testCases/planEnumCont*`): comparisons of a continuous plan leaf (μ,σ logit pair) against deterministic bounds (theta included) become per-leaf intervals measured as Gaussian CDF differences (dim 0); monotone transform chains on the leaf side (`plus`/`neg`/`double`/`exp`/`log`, `mult` by a literal — the same static envelope as set-witness transport) are peeled structurally onto the bound (`planPeelSlice`); a single pairwise `X_a > X_b` between two bare leaves is closed-form via the difference Gaussian (`pwPairs`); and float equality / direct observation of a leaf is a dim-1 point density — the engine's only non-dim-0 measure, mixed across worlds via `addP` (min-dim mixture) while all-dim-0 world sets keep the plain sum. A world that couples the same continuous leaf twice, or couples it and also bounds it, refuses at compile time with an orthant-probability diagnostic (`pwOverCoupled`) — that boundary (e.g. `blueRightToCube`'s threaded continuous state) is permanent by design. The engine is tried *before* forward-chaining point inversion because FC's `VAnyExcept`-based `is<Ctor>`/accessor inverses produce runtime-crashing code for exactly these shapes; bodies the traversal declines keep their current path, and an `of` clause still routes to materializing enumeration (the `*Materialized` differential twins pin both paths to identical values). Structurally finite types (Bool, enum ADTs, tuples/Eithers thereof) are `Finite` in the modality engine regardless of `of` tags (`finiteRType` in ModalityInfer) — without this, such programs typed `Bottom` and got no prob function at all; the recursive M2 shapes need no further admission (their observable results are Bool/comparison-typed, which the existing rules already cover).

## Additional Features

### topK Branch Pruning

`topKThreshold :: Maybe Double` in `CompilerConfig` enables probability-based branch pruning during inference compilation. When set, the IRCompiler wraps each `IfThenElse` in probability mode with guards: if `p_cond < threshold` only the else branch is evaluated; if `p_cond > 1 - threshold` only the then branch; otherwise both. The threshold uses the global probability, accumulated through all branches during inference. The same threshold is applied to enumerable `InjF` branches, filtering out enum values whose left-parameter probability falls below the threshold. Pruned branches contribute zero to the result — this is a performance optimisation, not an approximation to the logic.

### Dimension Counting

Every probability-mode compilation result is a `PResult { rProb, rDim, rBranches, rImposs }` (see below) whose `rDim` is an `IRExpr` tracking the **dimensionality of the probability value**:

- `dim = 0` — discrete probability mass (indicator / PMF)
- `dim = 1` — univariate continuous density
- `dim = n` — multivariate density

Dimensionality determines whether the **change-of-variables correction** is applied when passing a value through an invertible function (`InjF`): if `dim > 0` the result is multiplied by `|derivative of inverse|`; if `dim = 0` no correction is needed. When combining two sub-expressions, dimensions **add** under multiplication (independent continuous variables), and under mixture addition the **smaller dimension wins** among the alternatives that are *possible* (see the impossibility flag below).

The base cases are: continuous distributions (`Normal`, `Uniform`) emit `dim = 1`; discrete and deterministic expressions emit `dim = 0`.

### PResult combinators

`dim` and the branch count are not hand-written per case. `toIRInference` / `toIRInferenceSave` / `toIREnumerate`, and the set-witness and plan-enum measurement functions, all return an opaque `PResult` built from a small combinator vocabulary (design presult-combinators, `IRCompiler.hs`): leaves are `density`/`mass`/`detP`, independent conjunction is `prodP` (a `Monoid` with unit `detP const1`), branches mix with `mixP`/`mixSubP`, enumeration sums with `enumSumP`, the change-of-variables correction is `scaleCoV` (which reads the result's own dim, so call sites never name it), and guards map over all three fields with `mapResult`/`zipResult` (single fields via `onProb`/`onDim`/`onBranches`). `shareResult` binds a sub-result's floated let-in block **once** and projects the fields off it, instead of re-wrapping the block around each field — see Benchmarks for why that distinction is the difference between linear and geometric IR growth, and for the two constraints (guards belong on the bound value; unread fields stay unprojected) that keep it correct and worthwhile. `mixP` takes the branch count as an explicit argument because no call site wants the operands' plain sum: `IfThenElse` shares one condition between its arms (`cond + left + right - 1`), the `AnyExcept` InjF selects one arm's count, and world sums add over all worlds. `packResult`/`unpackResult` are the only places that know the `IRTCons p (IRTCons d (IRTCons bc imposs))` encoding.

### Impossibility flag

The fourth field, `rImposs :: IRExpr`, is a Bool answering **"is this result a structurally impossible event?"** — the wrong `Either` arm, an indicator that did not match, a failed applicability guard, an arm whose condition cannot hold, a sample off a `Uniform`'s support. It exists because `mixP`/`mixSubP` need exactly that fact to decide which alternative wins, and used to *infer* it by comparing the computed probability to zero — which is wrong in both directions: a deep-tail density underflows to a true `0.0` while remaining possible (task addp-zero-check-non-total; `test_underflowedTailKeepsDimension`), and an approximate zero test additionally discarded merely-tiny densities (observe-partials-umbrella N4). `mixWith` now branches on the flag alone; no probability is compared against a float constant there.

Rules: leaves are possible (`density`/`mass`/`detP`); `indicatorP cond` sets `not cond`; `guardP` sets it where the guard fails; `prodP` ORs; `mixWith` consumes it (a mixture is impossible only if every alternative is). `impossibleWhen`/`guardP` spell the flag as an `IRIf`, never `IROp OpOr`/`OpAnd` — both operands of an IR boolean op are evaluated, and the conditions being guarded against are frequently what makes evaluating the other side safe or terminating (a zero-probability arm may contain the recursive call the zero-check exists to skip; a failed applicability guard means a deconstructing inverse would crash).

Two places derive the flag from the value instead of from structure, and only for a **discrete mass**, where an exact zero genuinely does mean "nothing contributed": `opaqueMass` (enumeration sums and plan-world sums — there is no boolean `IREnumSum` to fold over the support) and `AutoNeural.makeProb`'s decoder reader (assembled from logit reads, with no guard to take the fact from). A dim-1 density never derives its flag this way; that is the whole point.

The flag is **not stripped** from the emitted result (design inference-result-side-channels; deferred deliberately — stripping it would have to either drop it from called functions, losing the information exactly where the mixture is cross-function, or give callees and query targets different layouts). So the compiled prob/integ result shape is `(prob, (dim, imposs))`, or `(prob, (dim, (bc, imposs)))` with `countBranches`. Consumers match it through the `VProbDim`/`VProbDimBC` pattern synonyms and `resultImpossible` in `SPLL.IntermediateRepresentation` rather than on the tuple shape; those are the layout's only definition outside the compiler. The fourth field initially cost ~50% compile time on the set-witness-heavy benchmark; that turned out to be a multiplier on a pre-existing per-field block duplication rather than a cost of the flag itself, and compiling is now faster than it was before the flag (see Benchmarks).

### Branch Counting

`countBranches :: Bool` in `CompilerConfig` controls whether the compilation result's third field, `branchCount`, survives into the emitted code: compilation always produces all four fields (nested `IRTCons`), and `stripBranchCount` removes just the branch-count slot as a post-pass when the flag is off, leaving `(prob, (dim, imposs))`. The branch count records how many distinct enumerated branches were actually traversed during evaluation — leaves emit 0 or 1; branches sum their children's counts. When `countBranches` is enabled, all tuple-unpacking in the IRCompiler shifts position (`IRTFst`/`IRTSnd` chains extend by one level) to accommodate the extra element. `topKThreshold` and `countBranches` interact: a pruned branch contributes 0 to the branch count.

### Query-Type Guard

`checkQueryType :: Bool` in `CompilerConfig` (default `True`, CLI opt-out `--noTypeCheck`, independent of `-O`) wraps every prob/integ function root in a guard that checks the query value structurally conforms to the program's return type: `IRIf (IRConformsTo returnRType (IRVar "sample")) body (IRError "...")`. Without it, a wrong-typed query — e.g. `p(0.5)` against a `Bool`-returning program — either silently returns a bogus number (when the optimizer folds the sample check away, as with a symmetric coin `if sample then 0.5 else 0.5`) or hits a deep `Condition is not a boolean` panic; the guard turns both into one clear diagnostic. Because it references `sample` (a runtime input) it survives constant folding.

`IRConformsTo RType IRExpr` is a single IR node consumed by all three backends: the interpreter (`valueConformsTo` in `IRInterpreter`), Python (`pyConforms`), and Julia (`jlConforms`). All three are full-depth structural checks (recurse into tuple components, either arms, and every list element), precise for float/bool/int and permissive only for types with no cheap runtime tag, so they never falsely reject. The marginal-query wildcard (`isAny`/`VAny`) is accepted at every level and short-circuits before any component accessor. When emitted, the guarded function's doc comment (visible in generated code) points at `--noTypeCheck` — the intended workflow being to leave the guard on while smoke-testing on a dataset, then disable it for hot production runs. `stripBranchCount`'s `stripOuterTriple` and the guard's `guardUnderLambdas` both account for the interposed `IRIf` (peel through it; keep outer parameter lambdas at the function head).

### Debug: Intermediate Stage Dump (`-d`)

`showIntermediates :: Bool` in `CompilerConfig` (CLI flag `-d` / `--debugIntermediates`) prints the fully-annotated AST after each pipeline stage to stderr. Each stage is boxed with a label and rendered via `prettyPrintProg` (tree shape, one node per line). The output shows the progressive accumulation of annotations:

| Stage | What becomes visible |
|---|---|
| After Parsing | All fields `NotSetYet`, tags empty |
| After RType Inference | `rType` populated; `pType` still `NotSetYet` |
| After Enum Annotation | `DiscreteValues` tags appear |
| After Forward Chaining | `chainName` fields filled |
| After Modality Inference | `pType` populated |
| After Conditional Annotation | `IsConditional` tags appear on conditioned distributions |
| After IR Compilation (pre-optimization) | Pseudo-code IR before any optimizer passes |
| After Optimization | Pseudo-code IR after constant folding, CSE, let-in optimization |

Use this when a program compiles incorrectly to identify which stage introduced the defect. `IRCompiler` selects the inference algorithm per node directly from the `pType` and `DiscreteValues` annotations visible after Modality Inference (there is no separate algorithm-tag stage).

RType inference (`SPLL.Typing.RInfer.addRTypeInfo`) runs first, directly on the freshly parsed program — it needs no chain names or enum tags, only `PredefinedFunctions`' declared contracts, so it can reject ill-typed InjF applications (e.g. `fromRightPartial` on a non-`Either` value) with a clean `RTypeError` before enum annotation ever forward-evaluates them. `SPLL.Typing.Infer.addModalityInfo` then builds the `ForwardChaining` certificate and runs the modality (`pType`) pass on the already-RType'd, chain-named program; `addTypeInfo` remains as a thin composition of `addRTypeInfo` + `addModalityInfo` for callers (mainly tests) that still want the whole pipeline collapsed into one call on a chain-named program.

### Neural Declarations

Neural networks are declared separately as `NeuralDecl = (String, RType, Maybe MultiValue)` and enter the global type environment before inference. A `ReadNN name param` expression calls the named network at runtime. If the declaration carries a `MultiValue` annotation (the possible output values), Analysis propagates it through `ReadNN` nodes so that `InferenceRule` matching can select enum-aware algorithms for downstream comparisons. A `MultiValue` containing a continuous leaf (`Real`, incl. via `_` on a `Float` slot) is never tagged for enumeration — enumerating only its discrete residue would silently drop the continuous mass — so such declarations behave like unannotated ones for enum purposes (`multiValueContainsContinuous`, guarded in both `annotateEnumsProg` and `isEnumerable`).

The `of ...` clause mirrors the output `RType` and follows this grammar (each production names its `MultiValue` constructor):

```
multival ::= _     -- MultiAuto: auto-derive from RType
           |  Real -- Float leaf
           |  [value1, value2]'     -- MultiDiscretes: explicit enumeration
           |  (multival, multival)  -- MultiTuple
           |  '(' multival '|' multival ')'              -- MultiEither
           |  '{' ctor multival* ('|' ctor multival*)* '}' -- MultiADT
           |  ident                                      -- MultiTypeRef: recursive self-reference
           |  int ident '.' multival                     -- depth-limited recursion: unroll <int> levels, binding the self-reference name <ident> — e.g. `3x.{A [0,1,2] | B x}` (the `x` is the binder, not a keyword)
```

Auto-derivation (`_`, or an omitted `of ...` clause) fills these slots from the RType: `Float`→`Real`, `Bool`→`[True, False]`, `Tuple`/`Either`/non-recursive `ADT`→recurse per component/constructor. `Int`, `Symbol` (unbounded domains) cannot be auto-derived — give an explicit enumeration. A **recursive `ADT`** auto-derives only if its `data` declaration carries a default depth (`data T = … depth N`), which bounds the unrolling; otherwise give a depth-bounded `<depth><binder>.{...}` (e.g. `3x.{...}`) as a per-declaration override, or compilation errors. E.g. `(_, [0..10], _)` for `(Color, Int, Float)` only needs the `Int` slot spelled out.

Only *direct* self-recursion is auto-detected; nested (`ListOf (TADT name)`) or mutual recursion still needs an explicit `of`.

## Test Structure

The suite runs under tasty (`tasty-quickcheck` for properties, `tasty-hunit` for unit tests). Each module exports a `TestTree`; `Spec.hs` assembles them under the groups Spec / Corpus / Parser / Internals / Rejection / Encode / Showcase / End2End.

- `test/Spec.hs` — main entry (`defaultMain`), the static Spec QuickCheck properties, and the Corpus group: metamorphic properties (sampling-vs-PDF, topK, branch counting, P(ANY)=1, validation) whose generator pool is built from the interpreter-routed, non-neural prob cases of `testCases/` — there is no separate inline table of expected values
- `test/TestParser.hs` — parser unit tests (`parserTests`)
- `test/TestInternals.hs` — internal function tests (`internalsTests`)
- `test/TestRejection.hs` — unhappy-path tests (`rejectionTests`): per-program HUnit cases asserting that invalid programs (the `invalid*` family from `Examples.hs`, plus missing-`main`/`ANY`) are rejected by the validator with the expected reason, that `compile` propagates the rejection, and that ill-typed programs are rejected by type inference
- `test/TestEncodeProperties.hs` — AutoNeural encode tests (`encodeTests`), plus the corpus-driven `EncodeRoundtrip` group (`encodeRoundtripTests`): *LogitIdentity* (for every decoder-passthrough program `main sym = nn sym`, encode ∘ literal-mock-decode is the identity on valid logit vectors — pins slot layout) and *DensityAgreement* (for every `encode_len`/`encode_at` invocation in the corpus, the encoded vector read back through the standalone plan prob reader must match the endpoint's own prob function at forward-sampled points — pins slot semantics, e.g. the Gaussian density formula, since the two sides take independent compiler paths on transformed outputs). DensityAgreement assumes plan-representable output distributions (independent tuple slots); a future corpus program with correlated slots must be excluded there
- `test/TestShowcase.hs` — documentation drift guard (`showcaseTests`): parses the whole `examples/showcase.ppl`, forward-samples + prob/cdf-checks its `main` against `examples/showcase.tst`, freezes the inference result of individual documented definitions listed in `examples/showcase.freeze` (driven directly by name via `runProbNamedC`/`runIntegNamedC`, not through `main`), and parses+compiles every ` ```spll ` fenced block in `README.md` (with a count assertion so an untagged block can't slip through). A ` ```text ` block placed immediately after a ` ```spll ` block (only blank lines between) supplies expected `p()`/`cdf()` output in `showcase.tst` syntax, verified against that snippet — a doctest that keeps README examples' behaviour, not just their syntax, from rotting. `examples/showcase.freeze` is the opt-in list of definitions whose behaviour is frozen; definitions absent from it are guaranteed only to parse (some are intentionally generate-only/parse-only)
- `test/End2EndTesting.hs` — integration tests using `.ppl` + `.tst` files from `testCases/` (`end2endTests`; one test per program, Julia batched into a single test)
- `test/TestCaseParser.hs` — `.tst` parser and `TestCase`/`Backend` types
- `test/ArbitrarySPLL.hs` — QuickCheck Arbitrary instances for property testing

A `.tst` file may start with two optional header lines, in either order: a routing header `backends: interpreter, julia, python` (any non-empty subset; without it the file runs against all three scalar backends), and a standalone `slow` line. The `.tst` grammar has no comment syntax: a line the expectation parser cannot match silently ends the file (`pTestFile` has no `eof`), so a `--` line would quietly drop every expectation after it.

The header accepts a fourth, **opt-in** token, `batched`, which is *not* part of the no-header default (`defaultBackends` in `TestCaseParser`, deliberately distinct from `allBackends = [minBound .. maxBound]` — adding the constructor to the latter would have silently enrolled every corpus file). It declares that the program is expected to be **batched-mode eligible**, and the `BatchedPython` group *asserts* that (`declared-batched-eligible`: a batched `compile`, a `generateFunctionsBatched` emission, and batchable query samples) instead of filtering silently, naming the program and quoting the refusal diagnostic on failure. Those assertions are pure Haskell and run even where no torch-enabled Python exists, so a torch-less CI still guards batched eligibility. The reverse direction — a program that *is* eligible but does not declare it — is a stderr note only (`eligibility-gain-note`), since eligibility loss is the regression worth failing on while eligibility gain happens whenever an ordinary scalar program is added. Listing `batched` never removes a file from a scalar backend: spell the scalar ones out alongside it. `slow`-headered files stay out of batched coverage by construction.

Expected values are compared with `probTolerance` (1e-4). Integral convergence is encoded per program as an upper-tail `cdf(x)=(1.0, 0.0)` line rather than checked at a global probe point — no single finite bound suits both heavy-tailed lognormal products and log-domain programs whose inverse overflows.

A `p(...)`/`cdf(...)` expectation takes an optional **third component**, the expected **impossibility flag**: `p(x) = (prob, dim, imposs)` where `imposs` is `True`/`False` (the same boolean spelling `pValue` uses everywhere else). It is carried as a `Maybe Bool` on `ProbTestCase`/`CumulTestCase`, and a two-component expectation keeps its original meaning — check prob and dim only, do not check the flag — so the hundreds of pre-existing lines are unaffected. All three backends check it when it is declared: the interpreter through `resultImpossible` (never by matching the tuple shape in the test tree), Python via `tmp[1][1]` and Julia via `tmp[2][2]` of the emitted `(prob, (dim, imposs))` result. Note the three-component form is *not* an SPLL value — SPLL's own tuple syntax is strictly binary — so it is parsed by `pExpectedResult` in `TestCaseParser` rather than by `pValue`. Batched mode does not check the flag.

The corpus rows that pin the flag are deliberately chosen to pin its *structural* semantics rather than a zero test: `uniform` (in/out of support, both polarities on one program), `logNormal` (a negative sample of a strictly-positive support), `discreteFloats` `p(5.0)` and `either_both_cont` `p(Left 1.5)` (every alternative of a mixture impossible, so the mixture is — `mixWith`'s rule), `uniformIf` `p(3.0)` (both continuous arms off support), and — the load-bearing negative control — `normal` `p(40.0)`, a 40-sigma tail whose density underflows to a hard floating-point `0.0` while `imposs` must stay `False` (task addp-zero-check-non-total).

### Slow tests

**The `Slow` group is currently known-broken** — it is not green, and failures there are pre-existing rather than caused by whatever change you are making. Do not treat a red `NEST_SLOW_TESTS=1` run as a regression signal without first confirming the same failure on an untouched checkout. The default (non-slow) suite is the gate.

A handful of tests are expensive enough (multiple full compiles of a large/deep program) to noticeably slow day-to-day `stack test`, while being unlikely to catch regressions outside the specific feature they pin. These are skipped by default and only run with `NEST_SLOW_TESTS=1 stack test` (or `NEST_SLOW_TESTS=1 stack test --ta '-p Slow'` to run just that group) — CI or an occasional manual pass should still exercise them regularly. Two mechanisms feed the top-level `Slow` group built in `Spec.hs`:
- A `.tst` file's `slow` header (see above) routes its program out of `end2endTests`'s Interpreter/Interpreter-Unoptimized groups and into `End2EndTesting.slowEnd2EndTests` instead (e.g. `testCases/planEnumRecDeepOne.tst`, a depth-10 plan enumeration stress case).
- A few individual `TestInternals.hs` cases that redundantly recompile a corpus program under several `CompilerConfig`s (e.g. `test_planEnumRecTopKAndBC`, which compiles `planEnumRecChain.ppl` four more times to check topK/branch-counting interaction) live in `TestInternals.slowInternalsTests` instead of `internalsTests`.

Coverage should not otherwise decrease when adding to this group — reach for it only when a test is both measurably heavy and narrowly scoped to a feature that isn't touched by everyday changes elsewhere.

### Benchmarks

`benchmarks/` holds compiler-performance stress programs (`stressPlanEnum.ppl`, `stressContinuous.ppl`, added with the IROptimizer CSE fix `ebd46ab`). They pin no values and are not part of the test suite — they are run through the CLI and timed:

```bash
stack run -- -i benchmarks/stressContinuous.ppl compile -l python -o /tmp/b.py   # time this
```

Always run once to warm up before timing: the first invocation after a source change includes stack's rebuild-and-register, which dwarfs the compile itself (seconds vs. milliseconds) and has been mistaken for a regression. There is no tasty benchmark ingredient; for the test suite itself, `TASTY_HIDE_SUCCESSES=false` gives per-test timings and `--ta '-t 60'` (seconds) bounds each test, which is the quickest way to find a hang.

Reference timings on the two benchmarks, warm (2026-07-21): `stressPlanEnum` ~1.15 s, `stressContinuous` ~1.35 s at both -O0 and -O2.

`benchmarks/batched_vs_scalar.py` is a different kind of benchmark: it measures the *emitted code's* runtime, not the compiler's. It loads the scalar and `--batched` emissions of one `ReadNN` program (`mNistAdd`) with the same network weights, times a per-point scalar loop against one batched call across batch sizes, asserts the two agree elementwise, and runs the `torch.compile` graph-break check. It needs a torch-enabled Python (same lookup as the `BatchedPython` test group) and takes the two generated files as arguments — see the docstring for the exact `stack run` invocations. See the M5 paragraph under Batched Mode for the numbers.

`stressContinuous` briefly cost 3.3 s at -O2 and 25 s at -O0, when the impossibility flag added a fourth field to every inference result. The flag was not really the cause: compiling an `IfThenElse` arm wrapped the arm's whole let-in block around *each* result field separately, so every floated binding was duplicated once per field at every nesting level. IR size was therefore geometric in nesting depth — measured at ~2.16x per level with three fields and ~3.18x with four — which is why one more field cost 29x the IR. `shareResult` (see the PResult combinators above) binds the packed result once and projects the fields off it, which removed the exponent rather than the fourth field: pre-optimisation IR for `stressContinuous` went 207 MB → 461 KB, well under the 6.6 MB it had before the flag existed.

Two things about that fix are load-bearing and easy to undo by accident. The zero-probability check must be the *bound value's* guard, not a wrapper around each projection: a shared binding is eager, and an arm whose condition cannot hold may contain the very recursive call the check exists to skip (guarding the projections instead makes `dice` non-terminating). And sharing is skipped when fewer than two fields read the block, with unread fields kept as themselves rather than projected: dims and flags are usually static constants, and routing a constant through an opaque tuple hides it from constant folding — sharing every field unconditionally shrank -O0 400x while growing the -O2 *output* 2.7x.

What remains is a code-size gap, not a compile-time one: emitted -O2 code is ~1.9x larger than before the flag (105 KB → 200 KB on `stressContinuous`). The cause is **not** lost per-field dead-binding elimination — that was the intuitive explanation and it is measurably wrong, since the fields overlap heavily (at a typical 12-binding site the probability needs all 12, the dim 9, the flag 7, the branch count 0, so per-field slices would total 28 copies where sharing has 12).

The actual cost is a construct-then-immediately-destructure round trip. The emitted code builds the shared tuple out of scalar components that already exist as their own variables and then reads it straight back apart:

```python
l_18_armF = T(l_18_armF_0, l_18_armF_1)
l_20_pB   = l_18_armF[0]
l_22_dimB = l_18_armF[1][0]
```

That round trip is real but small: of the 1674 extra -O2 lines, 372 are tuple construction and 264 are projections. Removing it (`generateLetInStatement` already emits the components as `name_0`/`name_1` before packing them, so the Python backend could read those directly and drop the pack) recovers roughly 10%, not the 2x.

The rest is structural to sharing, and worth understanding before anyone tries to optimise it away. Four fields now travel through one guarded tuple, so every branch path of the block materialises all four — where previously each field was its own binding and the optimizer folded most dims and flags to constants and deleted them. Keeping unread fields unprojected (see `shareResult`) already claws back the cases where a field ignores the block; at the sites that dominate this benchmark it does not apply, because the fields genuinely overlap (12/9/7/0 of 12 bindings). Two candidate optimizer passes were measured and rejected: hoisting the block's bindings out of the binding cannot fire at all (the guard must not be hoisted past), and splitting per field costs more than it saves (28 binding-copies against 12). The -O2 size is the price of the compile-time fix, not a missing optimization.

### Fuzz tests

`test/TestFuzz.hs` runs randomly-generated SPLL programs (from `test/ArbitrarySPLL.hs`) against the same kind of metamorphic invariants the hand-written corpus checks in `Spec.hs`'s Corpus group, rather than against known expected values. Two generators feed it: `genRawFuzzProgram`/`genRawFuzzExpr` cover the full `Expr`/`Program` AST space (all 11 `Expr` constructors, wide `Value` leaves via `genValueWide`) and are only useful for crash-freedom, since almost every draw is ill-typed; `genTypedProgram`/`genTypedExpr` build well-typed-by-construction scalar (Float/Int/Bool) programs from the same combinators `SPLL.Prelude`/`SPLL.Examples` hand-write with, at a low discard rate, and drive the actual inference-invariant properties (P(ANY)=1, topK-threshold-0 reproduces exact inference, topK never inflates probability, branch counting doesn't change the probability value, probability is never negative). Each property caps structural size (`fuzzSize`) and wraps each case in a wall-clock timeout, since the compiler isn't known to terminate on arbitrary input.

Empirically (measured directly, not guessed): the raw generator passes `validateProgram` on ~7% of draws and never survives a full `compile`; the typed generator validates 100% by construction but only ~55% of draws compile without crashing (a single known bug — `and`/`or`'s missing inversions, see below — accounts for most of the other 45%), and of those only ~58% (so ~32% of all typed draws) end up with a probability function at all. A "no data to check" branch in an invariant property therefore counts for the *majority* of draws, not a rare edge case — every such branch returns `discardVacuous` (`False ==> True`, the same idiom `Spec.hs`'s `testSamplingProb` already uses) rather than a bare `property True`, so QuickCheck's own discard-ratio accounting (`N successes; M discarded`, or a hard "gave up" failure if the ratio gets extreme) reports this honestly instead of it being invisible inside an inflated success count.

The `Fuzz` group lives inside `Slow` (`NEST_SLOW_TESTS=1 stack test --ta '-p Fuzz'`). One property, `prop_Fuzz_SamplingMatchesPDF`, is central enough to be exported separately (`superSlowFuzzTests`) into its own further opt-in tier, `SuperSlow` (`NEST_SUPERSLOW_TESTS=1 stack test --ta '-p SuperSlow'`): it's the only fuzz property that cross-checks `generate` against `probability` independently (every other property only cross-checks different `CompilerConfig`s against each other on the same prob function). Per draw it checks `queryPointCount` (5) independent points, all reused against one shared batch of forward samples sized to the hardest (lowest-density) point among them (`dynamicSampleCount`/`drawQueryPoints`/`runSamplingCheck`) — sampling is the expensive part (each sample is a full interpreter draw), so batching turns one expensive compile+sample round into several checks instead of one. Each point's empirical hit rate is compared against the compiler's claimed rate via a proper statistical test rather than a fixed tolerance: a two-sided Wald z-test (`twoSidedPValue`) classifies it as `Different` (p < a Bonferroni-corrected alpha — a real failure) or, failing that, a TOST equivalence test (`isEquivalent`) classifies it as `Identical` (confirmed within a practical margin) or `Unclear` (underpowered — triggers a batch-doubling retry, clamped to `maxSamples`, up to `maxRetries` times). Discrete (dim 0) outputs are matched exactly; continuous (dim > 0) outputs use an epsilon-wide window whose probability is computed *exactly* via the compiler's own CDF (`windowP0`/`irInteg`, using `runIntegC`) rather than approximated as `density*width` — the approximation assumes locally-constant density, which is wrong right at a distribution's support boundary and was observed to produce spurious `Different` verdicts purely from the test's own geometry.

Because `Test.QuickCheck.All.allProperties` (the `$(allProperties)` TH splice used to build `fuzzTests`) scans the whole module for `prop_`-prefixed bindings regardless of where the splice sits, `prop_Fuzz_SamplingMatchesPDF` is wired into `superSlowFuzzTests` with a plain `testProperty` call instead of a second splice — a second `$(allProperties)` there would re-collect (and re-run) every property already in `fuzzTests` too.

Every `try`/`catch` in this module that runs inside a `withinBudget`/`withinSuperSlowBudget`-wrapped action must catch only *synchronous* exceptions (`trySync`, not a bare `try :: IO (Either SomeException a)`) — `System.Timeout.timeout` cancels an action by throwing an (async) exception into it, and a blanket `SomeException` handler inside that action will swallow the cancellation itself, silently defeating the per-case budget for exactly the slow cases it exists to bound. This was a real bug here: it let a handful of pathologically slow compiles run for many real seconds (once, combined with an uncapped retry-doubling loop, enough to OOM-kill the whole test process) before the fix.

The interpreter substitutes a mock for every declared neural network (`MockNN.hs`); the Symbol argument selects the mode: `(0, seed)` random logits, `(1, (spikeAt, seed))` a noisy spike at a value (what `argmax_p` queries auto-wrap), `(2, [logit0, ...])` a verbatim logit vector — the only mode with deterministic output, used to pin exact densities in `.tst` files (e.g. `autoNeuralProbGaussian.tst` passes `(2, [mu, sigma])` to check the decoder's Gaussian reader).

### Batched Mode (PyTorch tensorizer)

`batched :: Bool` in `CompilerConfig` (CLI `--batched`, design pytorch-tensorizer) opts into **batched inference**: instead of scalar Python evaluated one query point at a time, emit branch-free elementwise PyTorch that runs a whole `[B]`-shaped batch through at once (`torch.where` instead of data-dependent `if`, `torch.*` instead of `math.*`; broadcasting does the rest). Two pieces:

- **The IR select pass** (`SPLL.IRSelectPass`, M1) retags every data-dependent, elementwise-eligible `IRIf` in prob/integ bodies as a first-class `IRSelect` (both arms evaluated, combined by a mask). It runs before the optimizer, gated on `batched`. Scalar consumers lower `IRSelect` back to `IRIf` at entry (`desugarSelectEnv`; the interpreter delegates its case), so with a scalar backend it is a **behavioural no-op** — pinned by the `SelectPassNoOp` corpus differential test. A distinct node (not a flag on `IRIf`) keeps if-only optimizer rewrites from silently relabelling a select.
- **The batched backend** (`SPLL.CodeGenPyTorchBatched.generateFunctionsBatched`, M2a numeric + M2b neural) emits `torch.where` for selects and tensor formulas for everything else, over the **tensor fragment** only: float/int/bool leaves in fixed-shape tuples (structure-of-arrays: tuple structure stays a Python `T` object whose leaves are `[B]` tensors, so `dim`, the impossibility flag, and the branch count are per-element tensors too). **M2b** adds neural/enumerable programs: `IRApply` (network calls + cross-function decoder calls, reusing the scalar `_prob`→`.forward` LUT), `IRIndex` (a constant logit slice `out[..., i]` or a data-dependent gather `nn_gather(out, idx)`), `IREnumSum` (unrolled inline over the resolved `MultiValue`'s enum axis), and `IRIsPossible` (scalar-discrete membership → an `is_member` `[B]` mask) — reaching `mNistAdd`-style MNIST-addition inference. A **call-graph guard** (`checkCallGraph`) still refuses recursion (a cycle in the prob/integ call graph, e.g. `dice`) and calls reaching a non-emitted method (`generate`/`normal_params`, e.g. `factorial`/`flip`) — the refusals the old blanket `IRApply` refusal gave for free. **M3** adds **gradient hygiene**: every `OpLog`/`OpDiv` is routed through the double-`where` helpers `safe_log`/`safe_div` (mask the op's input to its safe domain so the local derivative stays finite; the enclosing `torch.where` discards the harmless value), because otherwise autograd flows `0·inf = NaN` back through the untaken (log-of-non-positive / divide-by-zero) arm of a select even though the forward *value* is correct — a defect the value differential can't see (`logNormal` is the canonical case). On in-domain elements the result is bit-identical to the plain op, so no expected value changes. `IRError` refusal arms are now emittable as a NaN `poison()` constant that the enclosing select masks away (a NaN *constant* has no gradient path, so it never itself NaNs a gradient; a surviving poison surfaces as NaN in the value differential — the poison-debug check without a separate flag), which admits set-witness programs carrying an `IRError` arm (e.g. `letProbIntervalPair`) into the fragment. The density/CDF twins need no masking (`exp`/`erf`/`clamp`, all grad-safe). Otherwise-outside-fragment programs (lists, `Either`, `IRLambda`, `VAny`/`VAnyExcept` marginal constants, composite-`MultiValue` `IREnumSum`/`IRIsPossible`) are refused with a diagnostic naming the offending construct. That refusal machinery has its own **torch-independent** coverage, in two tiers: the top-level `BatchedRefusal` group (`End2EndTesting.batchedRefusalTests`) is a table of `(corpus program, diagnostic substring)` rows, one per refused construct reachable from a real `.ppl` — each row asserts `compile` returns `Right` and only then that `generateFunctionsBatched` returns `Left` naming that construct, so a row can never pass off an unrelated earlier failure as a refusal; and `TestInternals.batchedRefusalUnitTests` covers the refusals no real program reaches, by calling `batchedGuard`/`generateFunctionsBatched` on hand-built `IRExpr`/`IREnv` values (list membership, `VAnyExcept`, a residual `IRConformsTo`/`OpIsAny`, a composite-`MultiValue` `IREnumSum`/`IRIsPossible`, and generate-only recursion — each blocked on real input by an earlier guard), including the *accepting* direction so a gate that refused everything would not pass. The composite-`MultiValue` gate on `IREnumSum` was itself a hole found this way (it was admitted unconditionally while the structurally identical `IRIsPossible` was gated, so a composite enumeration emitted Python naming scalar-`pythonLib.py`-only runtime constructors and died with a `NameError`); it changes no corpus program's eligibility. `VAny`/query-type-guard handling is stripped at the batched entry (`prepBatchedBody`), not represented. Runtime lib: `pythonLibBatched.py` (torch density/CDF twins, elementwise `T.__eq__`, `asmask`, M2b's `nn_gather`/`is_member`, plus M3's `safe_log`/`safe_div`/`poison`).

Batched output is tested by the `BatchedPython` group (`End2EndTesting.batchedPythonTests`). Participation is a `.tst` routing declaration — the `batched` token in the `backends:` header (see Test Structure) — and eligibility of every declaring program is asserted, not filtered; the neural special case that used to admit neural programs regardless of their Python routing header is gone (such a program lists `batched` itself). Each eligible corpus program's batched code is run over a batch of its query points in a **real torch interpreter** and compared per-element to the point's expected `.tst` value (as of M3: 92 programs, 461 points — M3's `IRError` poison admission added the extra program; after the neural-generate-parity task below: 91 programs, 457 points — `twiceApplication` dropped out of batched mode entirely, forward/integrate included, as the one accepted cost of that task's hard generate-refusal rule; 86 programs, 437 points — the `IRConst` non-scalar gate refuses five plan-enum programs whose bool enum-index lookup carries a `VList` constant, so they gave up the `batched` token, and M5 added one query point; **currently 101 programs, 483 points** — heterogeneous M1 added the list-valued `list`, `gaussList` and `gaussListTheta` — the 12 programs `eligibility-gain-note` had been reporting were enrolled on 2026-07-30 after a torch run confirmed their values, and the note now reports nothing). Those 101 programs are exactly the ones carrying the `batched` token today. The enrolled 12 (`constant`, `fstDiscrete`, `thetaTree`, `varAlias`, `uniformNeg`, `uniformMultNeg`, `normalMultPlus`, `uniformIf`, `injDouble`, `ltEnumerateBoth`, `lambdaThetaInverse`, `gtEnumerateBoth`) had been invisible to the pre-declaration selection condition because their `.tst` files do not route to scalar Python; ten already had a `backends: interpreter` header and just gained the token, while `ltEnumerateBoth`/`gtEnumerateBoth` had *no* header and so had to spell out the previous `defaultBackends` set alongside it (`interpreter, julia, python, batched`) — the trap the "listing `batched` never removes a file from a scalar backend" note in Test Structure warns about. A second property, `gradients-nan-free` (M3 acceptance), takes each eligible non-neural program whose code contains a `safe_log`/`safe_div` (currently 24 programs — the `logNormal` family and friends), runs its `forward` on a boundary-straddling batch with `requires_grad` on the sample, back-propagates, and asserts the sample gradient is NaN/Inf-free. It needs a torch-enabled Python — found via `NEST_TORCH_PYTHON` → a venv path → `python3` — and **skips with a visible note** if none imports torch, so a torch-less CI stays green. The driver runs from a temp file (deep neural logit literals exceed the `python -c` arg-length limit); for a neural program it batches each per-point `(2, [logits])` symbol into a `[B, n]` tensor and installs an identity mock (mode-2 verbatim logits) for every declared network. Marginal (`VAny`) queries remain a later milestone; topK is settled by M5 below.

**M5** adds perf evidence and settles the topK interaction. `benchmarks/batched_vs_scalar.py` times the scalar emission of `mNistAdd` in a per-point loop against one batched call with the same network weights, asserting both agree elementwise: **17x at B=512, 16x at B=4096** with a real 784→128→10 net, and **247x at B=4096** with the network replaced by a constant — the larger number, showing the win is mostly the *emitted inference code* (100 Python-level enumeration steps per point), not just the batched `ReadNN` call. Below B≈8 batched is a *loss* (fixed per-call tensor overhead). The batched forward traces to **1 torch.compile graph with 0 graph breaks** and compiles under `fullgraph=True`, as the select form predicts. **topK in batched mode is per element, not per batch**: under select semantics both arms are evaluated anyway, so pruning can only choose which already-computed value to keep — per element that is three extra `torch.where`s and is exactly value-identical to scalar mode, whereas per-batch pruning would need a `mask.any()` host synchronisation (and a graph break) at every branch to skip anything at all, and would make `p(x)` depend on which other points share the batch. This needs no compiler change — `accProb` is already a `[B]` tensor parameter and the cutoff comparison a `[B]` mask — so M5 adds the missing *evidence*: `BatchedPython`'s `topk-is-per-element` recompiles every `batched`-declaring program with prob query points at two thresholds (0.3, 0.6; 200 program/threshold pairs) and checks each batch element against the **interpreter's** value at the same threshold (not the `.tst` values, which are topK-off), asserting non-vacuity by reporting the pairs pruning actually changes (19 — the 2026-07-30 enrollment added `uniformIf`, `ltEnumerateBoth` and `gtEnumerateBoth` at k=0.6, heterogeneous M1 added `gaussList` at both, so structure-directed recursion under topK is covered). `autoNeuralProbMnistAdd` is the load-bearing witness: its batch mixes `[0.7, 0.3, …]` and `[0.5, 0.5, …]` logits, so at threshold 0.3 an enum slot is pruned for some elements and kept for others *within one call* — any per-batch rule fails it. The benchmark also found and fixed a latent defect: `nn_gather` did not clamp its index, and since both `torch.where` arms are evaluated, the masked-away residual `c - a` still reaches the gather — negative indices silently wrapped (harmless, discarded) but a realistic sum query indexed past the end and raised, killing the whole batch for a value nothing reads. It now clamps, like M3's `safe_log`/`safe_div` mask their inputs; `autoNeuralProbMnistAdd.tst`'s `p(12, …)` point is the regression.

**Heterogeneous batching (design heterogeneous-batch-inference, M1)** widens the
fragment to **list-valued samples**, via *shape-signature bucketing* rather than
anything inside the kernel: `pythonLibBatched.bucketed(fn, samples, *args)`
partitions a batch by structural signature (full skeleton — list lengths and
tuple shape, scalar leaves erased), structure-of-arrays-packs each bucket, calls
the kernel once per bucket, and scatters results back into input order. Within a
bucket every structural test has one answer for the whole batch, so
structure-directed control flow stays ordinary Python: `structural` classifies a
condition as shape-determined (comparison against the *empty-list* constant is
the primitive probe; a non-empty list constant is per-element data and stays
refused), `hoistStructural` lifts such `if`s out of expression position into
statement position (never *out of* an arm — the arm's guard is what makes
`head sample` legal), and they emit as real `if:`/`else:` blocks with a Python
(not tensor) condition. Structure-directed **recursion** is admitted on two
static conditions (`recOffenders`): every call to a cycle member is reached only
through a structural `if` — under eager select semantics a value-guarded
recursion would never terminate — and descends into a list tail; value-dependent
recursion (`dice`) keeps its refusal. The **dichotomy guard** refuses the other
half: a select (or residual value-dependent `if`) whose arms have different
structure, since `torch.where` cannot select between shapes. `IRHead`/`IRTail`/
`IRCons` and the empty-list constant joined the fragment. One narrow exception
to the hard generate-refusal rule: a *recursive list-building* generate emits a
`NotImplementedError` stub rather than refusing the whole program (its
per-element depth is the design's deferred Component 4, and a hard refusal would
take the program's bucketable prob/integ down too); a *fixed-shape* list
generate is fully batched. Acceptance witness: `gaussList` over three lengths,
one kernel call per length (the `BatchedPython` driver asserts the bucket count,
not just the values).

**M4** adds **batched generate** (`rand(n)`/`randn(n)` draw a whole `[n]`-shaped batch; a random `if` in generate mode renders exactly like a prob/integ select — `torch.where`, both arms drawing independently for the whole batch, so each element gets one arm's fresh draw and the result is the same mixture distribution as scalar generate, just with harmless extra randomness for the untaken arm). The batch-size parameter is a reserved-looking internal name (`_batchN`, matching the `_r0`/`cse_0` convention) rather than something public-facing like `n`, specifically to avoid colliding with a genuinely `n`-parameterised SPLL function. Originally scoped to the non-neural tensor fragment only (matching M2a), with a neural decoder group's own generate (categorical/Gaussian decoder sampling) out of scope and stubbed; **neural generate parity landed as a same-day follow-on** (task neural-generate-parity, haskell-dppl `e9dc4ab`): `AutoNeural.makeGenRec`'s decoder body — a sequential weighted-lottery categorical draw (`IRIf`/`IRSample IRUniform`/`IROp OpDiv` cascading over running normalised weight — mathematically a genuine categorical sample, not argmax, matching scalar `makeGenRec`'s own semantics) for a discrete leaf, Gaussian reparameterisation (`mu + sample*sigma`) for a continuous leaf, `IRTCons` composition for tuples — turned out to already lie entirely in the tensor fragment once M2b (`IRApply`/`IRIndex`) and M4 (`IRSample`) had landed, so removing the blanket neural-decoder exclusion was sufficient; no new IR nodes or `pythonLibBatched.py` primitives were needed. This reaches `mNistAdd`-style composed generate too (`readMNist_auto.generate(a, N) + readMNist_auto.generate(b, N)`). An `EitherPlan`/`ADTPlan`-shaped decoder output stays refused (`IRLeft`/`IRRight` have no tensor representation) — not a new gap, since such a decoder's *forward* function already fails to batch-compile for the same structural reason (`makeProbRec`'s `IRIsLeft`/`IRFromLeft`/`IRFromRight`). Generate ineligibility (recursion via `hasGenCycle`, or a residual non-fragment construct via the same `batchedGuard` forward/integrate uses) is now a **hard compile-time refusal**, exactly like forward/integrate — the `generateFunctionsBatched` pipeline is a single `Either` covering all three methods. (The original M4 design made generate ineligibility a **per-class, best-effort** stub — `raise NotImplementedError(...)`, accepting `*args, **kwargs` so a caller threading the batch-size parameter through a stubbed callee wouldn't itself fail on arity first — specifically because every neural decoder group unconditionally had a generate function that was, at the time, never eligible; a hard failure then would have broken batched compilation of every neural corpus program. That blanket exclusion is gone now that decoder generate is supported for the shapes that matter. Switching to a hard refusal has **one measured cost**, not zero: `twiceApplication` (`main = (\f -> f (f Uniform)) (\x -> x * 2.0)`, a nullary higher-order application) has a forward/integrate body the optimizer beta-reduces to plain arithmetic, but a *generate* body that still contains a literal, un-reduced `IRLambda`/`IRApply` unrelated to neural decoders; under the old stub it still contributed forward/integrate coverage, under the hard rule the whole program is refused. Accepted per Viktor (2026-07-22) rather than special-casing the stub back in for this one shape — see the `BatchedPython` count above.) Tested by a third `BatchedPython` property, `generate-density-matches-expected`: for every eligible non-neural program, a large fixed-seed batch from `main.generate(_batchN)` is checked against the program's *existing* prob query points via an epsilon-window empirical-density estimate (mirroring `Spec.hs`'s `testSamplingProb` idiom) compared to the `.tst`-declared density within `samplingTolerance`; for every eligible neural program, each query point instead gets its *own* `main.generate(sym, _batchN)` call (that point's own decoder symbol, sliced from the group's already-batched `[B, n]` symbol tensor and broadcast to a fresh `N`-sized batch), checked the same way — reusing corpus ground truth rather than needing a second sampling distribution to compare against (**90 non-neural + 4 neural = 94 of the 101 differential programs** checked; a list-valued program falls out naturally, its samples not being scalar — the rest need more than the batch-size parameter, e.g. a `ThetaTree` test override).

## Runtime Libraries

Generated Python code depends on `pythonLib.py` (scalar) or `pythonLibBatched.py` (batched mode, see above); generated Julia code depends on `juliaLib.jl`. These provide runtime helpers for the transpiled inference functions.
