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
stack run -- -i file.spll integrate -l 0 -h 1               # Integrate over range
# Disable specific test groups (no per-test name filtering available):
stack test --ta '-S'   # disable Spec tests
stack test --ta '-I'   # disable Internals tests
stack test --ta '-P'   # disable Parser tests
stack test --ta '-E'   # disable End2End tests
stack test --test-arguments "--show-timings"    # shows per-suite timing and cost center info, '-T' for short.
```


CLI flags: `-v` verbosity, `-O LEVEL` optimization (0-2), `-k CUTOFF` top-K threshold, `-c` count branches, `-t` truncate boilerplate, `-d` debug intermediates (see below).

To prevent having to run `stack test` repeatedly, e.g. to grep for specific failures, always store the test output to temporary file and grep that.

## Compilation Pipeline

```
SPLL source (.spll/.ppl)
  → Parser.hs (megaparsec)
  → AST (Lang/Lang.hs, Lang/Types.hs)
  → Type inference (Typing/RInfer.hs for return types, Typing/PInfer2.hs for probabilistic types)
  → IRCompiler.hs → IR (IntermediateRepresentation.hs)
     Three compilation branches: generate, probability, integrate
  → IROptimizer.hs (constant folding, CSE, let-in optimization, lambda→letIn refactoring)
  → CodeGenPyTorch.hs or CodeGenJulia.hs
```


Every SPLL program is compiled into three function variants:
1. **Generate** — forward sampling (draws random values)
2. **Probability** — computes probability density/mass at a given point
3. **Integrate** — integrates probability over a range

The availability of each depends on that inference being tractable, as determined by PInfer2.

Runtime execution: `IRInterpreter.hs` (`generateRand` for random sampling, `generateDet` for deterministic).

## Key Types

- **Expr** (`src/SPLL/Lang/Types.hs`): Main AST — includes `IfThenElse`, `LetIn`, `Lambda`, `Apply`, `Uniform`, `Normal`, `ReadNN`, `InjF` (injected functions like plus/mult), `Cons`, `TCons`, etc.
- **IRExpr** (`src/SPLL/IntermediateRepresentation.hs`): IR after compilation — `IRIf`, `IROp`, `IRLetIn`, `IRLambda`, `IRDensity`, `IRSample`, etc.
- **TypeInfo**: Bundle of RType (return type: `TFloat`, `TBool`, `TInt`, `ListOf`, `Tuple`, etc.), PType (probabilistic: `Deterministic`, `PNormal`, `PLogNormal`, `Integrate`, `Prob`, `Bottom`), and CType (constraints).
- **Value**: Runtime values — `VFloat`, `VInt`, `VBool`, `VList`, `VTuple`, `VEither`, `VClosure`, `VThetaTree`, `VSymbol`, `VBranch`, `VADT`, `VAny` (VAny is used only for marginal queries).
- **MultiValue**: Structured set of possible values for neural network output annotation — `MultiDiscretes [Value]`, `MultiTuple MultiValue MultiValue`, `MultiEither MultiValue MultiValue`, `MultiADT [(String, [MultiValue])]`, `MultiTypeRef String`.
- **CompilerConfig**: Controls verbosity, optimization level, top-K threshold, branch counting, plus flags `pruneAnyChecks`, `noIntegrate`, `noProbability`, `noGenerate`.

## Internal Details

Every AST node carries a `TypeInfo` record that accumulates annotations from successive passes:

```haskell
data TypeInfo = TypeInfo {
  rType            :: RType,           -- value structure (filled by RInfer, standard type annotations.)
  pType            :: PType,           -- probabilistic semantics (filled by PInfer2)
  chainName        :: ChainName,
  tags             :: [Tag]            -- enum ranges + chosen algorithm (filled by Analysis)
}
```

`PType` classifies how uncertainty flows through a node, forming a partial order:

```
Deterministic  >  PNormal, PLogNormal  >  Integrate  >  Prob  >  Bottom
```
`PNormal` and `PLogNormal` are incomparable siblings (different distribution families); their meet is `Integrate`. Deterministic values are not affected by randomness and need no inference. `PNormal`/`PLogNormal` allow closed-form Gaussian inference shortcuts. Integrate values have a known CDF. Prob values have a known PDF. Bottom values can only be sampled from, not inferred. Each PType implies that the semantics of lower types are available.

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

Neural networks are declared separately as `NeuralDecl = (String, RType, Maybe MultiValue)` and enter the global type environment before inference. A `ReadNN name param` expression calls the named network at runtime. If the declaration carries a `MultiValue` annotation (the possible output values), Analysis propagates it through `ReadNN` nodes so that `InferenceRule` matching can select enum-aware algorithms for downstream comparisons.

The `of ...` clause mirrors the output `RType` and follows this grammar (each production names its `MultiValue` constructor):

```
multival ::= _     -- MultiAuto: auto-derive from RType
           |  Real -- Float leaf
           |  [value1, value2]'     -- MultiDiscretes: explicit enumeration
           |  (multival, multival)  -- MultiTuple
           |  '(' multival '|' multival ')'              -- MultiEither
           |  '{' ctor multival* ('|' ctor multival*)* '}' -- MultiADT
           |  ident                                      -- MultiTypeRef: recursive self-reference
           |  int 'x' ident '.' multival                 -- depth-limited recursion (resolves MultiTypeRef)
```

Auto-derivation (`_`, or an omitted `of ...` clause) fills these slots from the RType: `Float`→`Real`, `Bool`→`[True, False]`, `Tuple`/`Either`/non-recursive `ADT`→recurse per component/constructor. `Int`, `Symbol` (unbounded domains) and recursive `ADT`s cannot be auto-derived — give an explicit enumeration or `<depth>x.Type.{...}`, or compilation errors. E.g. `(_, [0..10], _)` for `(Color, Int, Float)` only needs the `Int` slot spelled out.

## Test Structure

- `test/Spec.hs` — main entry, runs HUnit and QuickCheck tests
- `test/TestParser.hs` — parser unit tests
- `test/TestInternals.hs` — internal function tests
- `test/End2EndTesting.hs` — integration tests using `.ppl` + `.tst` files from `testCases/`
- `test/ArbitrarySPLL.hs` — QuickCheck Arbitrary instances for property testing

## Runtime Libraries

Generated Python code depends on `pythonLib.py`; generated Julia code depends on `juliaLib.jl`. These provide runtime helpers for the transpiled inference functions.
