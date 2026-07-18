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

`PType` classifies how uncertainty flows through a node, forming a partial order:

```
Deterministic  >  PNormal, PLogNormal  >  Integrate  >  Bottom
```
`PNormal` and `PLogNormal` are incomparable siblings (different distribution families); their meet is `Integrate`. Deterministic values are not affected by randomness and need no inference. `PNormal`/`PLogNormal` allow closed-form Gaussian inference shortcuts. Integrate values have a known CDF (evaluable via trusted special functions, e.g. `erf` — not necessarily closed-form). Bottom values can only be sampled from, not inferred. Each PType implies that the semantics of lower types are available. (There is deliberately no dens-only rung between `Integrate` and `Bottom`: a density whose CDF would need in-house quadrature is excluded by the language; the internal capability engine in `SPLL.Typing.Modality` still distinguishes that state and projects it to `Bottom`.)

A probabilistic `let x = v in body` whose observation cannot be point-inverted onto `x` (every path crosses a comparison or `if`) is compiled via **set-valued witnesses** (`setWitnessApply` in IRCompiler): the observation is inverted into guarded constraint-set worlds over `x` — intervals from comparisons (measured as CDF differences), case splits from conditionals, intersections across multiple occurrences — e.g. `let x = Normal in if x < 0.0 then 0.0 - x else x` yields the |Normal| density `2φ(y)`. Bodies drawing fresh randomness alongside such constraints are refused with a diagnostic.

## Additional Features

### topK Branch Pruning

`topKThreshold :: Maybe Double` in `CompilerConfig` enables probability-based branch pruning during inference compilation. When set, the IRCompiler wraps each `IfThenElse` in probability mode with guards: if `p_cond < threshold` only the else branch is evaluated; if `p_cond > 1 - threshold` only the then branch; otherwise both. The threshold uses the global probability, accumulated through all branches during inference. The same threshold is applied to enumerable `InjF` branches, filtering out enum values whose left-parameter probability falls below the threshold. Pruned branches contribute zero to the result — this is a performance optimisation, not an approximation to the logic.

### Dimension Counting

Every probability-mode compilation result is a pair `(prob, dim)` where `dim` is an `IRExpr` tracking the **dimensionality of the probability value**:

- `dim = 0` — discrete probability mass (indicator / PMF)
- `dim = 1` — univariate continuous density
- `dim = n` — multivariate density

Dimensionality determines whether the **change-of-variables correction** is applied when passing a value through an invertible function (`InjF`): if `dim > 0` the result is multiplied by `|derivative of inverse|`; if `dim = 0` no correction is needed. When combining two sub-expressions, dimensions **add** under multiplication (independent continuous variables), and the **smaller dimension wins** under mixture addition (whichever branch produced the non-zero probability).

The base cases are: continuous distributions (`Normal`, `Uniform`) emit `dim = 1`; discrete and deterministic expressions emit `dim = 0`.

### Branch Counting

`countBranches :: Bool` in `CompilerConfig` extends the compilation result from a pair to a triple `(prob, dim, branchCount)` via nested `IRTCons`. The branch count records how many distinct enumerated branches were actually traversed during evaluation — leaves emit 0 or 1; branches sum their children's counts. When `countBranches` is enabled, all tuple-unpacking in the IRCompiler shifts position (`IRTFst`/`IRTSnd` chains extend by one level) to accommodate the extra element. `topKThreshold` and `countBranches` interact: a pruned branch contributes 0 to the branch count.

### Query-Type Guard

`checkQueryType :: Bool` in `CompilerConfig` (default `True`, CLI opt-out `--noTypeCheck`, independent of `-O`) wraps every prob/integ function root in a guard that checks the query value structurally conforms to the program's return type: `IRIf (IRConformsTo returnRType (IRVar "sample")) body (IRError "...")`. Without it, a wrong-typed query — e.g. `p(0.5)` against a `Bool`-returning program — either silently returns a bogus number (when the optimizer folds the sample check away, as with a symmetric coin `if sample then 0.5 else 0.5`) or hits a deep `Condition is not a boolean` panic; the guard turns both into one clear diagnostic. Because it references `sample` (a runtime input) it survives constant folding.

`IRConformsTo RType IRExpr` is a single IR node consumed by all three backends: the interpreter (`valueConformsTo` in `IRInterpreter`), Python (`pyConforms`), and Julia (`jlConforms`). All three are full-depth structural checks (recurse into tuple components, either arms, and every list element), precise for float/bool/int and permissive only for types with no cheap runtime tag, so they never falsely reject. The marginal-query wildcard (`isAny`/`VAny`) is accepted at every level and short-circuits before any component accessor. When emitted, the guarded function's doc comment (visible in generated code) points at `--noTypeCheck` — the intended workflow being to leave the guard on while smoke-testing on a dataset, then disable it for hot production runs. `stripBranchCount`'s `stripOuterTriple` and the guard's `guardUnderLambdas` both account for the interposed `IRIf` (peel through it; keep outer parameter lambdas at the function head).

### Debug: Intermediate Stage Dump (`-d`)

`showIntermediates :: Bool` in `CompilerConfig` (CLI flag `-d` / `--debugIntermediates`) prints the fully-annotated AST after each pipeline stage to stderr. Each stage is boxed with a label and rendered via `prettyPrintProg` (tree shape, one node per line). The output shows the progressive accumulation of annotations:

| Stage | What becomes visible |
|---|---|
| After Parsing | All fields `NotSetYet`, tags empty |
| After Enum Annotation | `DiscreteValues` tags appear |
| After Forward Chaining | `chainName` fields filled |
| After Type Inference | `rType` and `pType` populated |
| After Conditional Annotation | `IsConditional` tags appear on conditioned distributions |
| After IR Compilation (pre-optimization) | Pseudo-code IR before any optimizer passes |
| After Optimization | Pseudo-code IR after constant folding, CSE, let-in optimization |

Use this when a program compiles incorrectly to identify which stage introduced the defect. `IRCompiler` selects the inference algorithm per node directly from the `pType` and `DiscreteValues` annotations visible after Type Inference (there is no separate algorithm-tag stage).

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

A `.tst` file may start with an optional routing header `backends: interpreter, julia, python` (any non-empty subset); without it the file runs against all three backends. Expected values are compared with `probTolerance` (1e-4). Integral convergence is encoded per program as an upper-tail `cdf(x)=(1.0, 0.0)` line rather than checked at a global probe point — no single finite bound suits both heavy-tailed lognormal products and log-domain programs whose inverse overflows.

The interpreter substitutes a mock for every declared neural network (`MockNN.hs`); the Symbol argument selects the mode: `(0, seed)` random logits, `(1, (spikeAt, seed))` a noisy spike at a value (what `argmax_p` queries auto-wrap), `(2, [logit0, ...])` a verbatim logit vector — the only mode with deterministic output, used to pin exact densities in `.tst` files (e.g. `autoNeuralProbGaussian.tst` passes `(2, [mu, sigma])` to check the decoder's Gaussian reader).

## Runtime Libraries

Generated Python code depends on `pythonLib.py`; generated Julia code depends on `juliaLib.jl`. These provide runtime helpers for the transpiled inference functions.
