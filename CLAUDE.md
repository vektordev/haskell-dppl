# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with
code in this repository. If ever you notice that information here is outdated
or substantially incomplete, you are requested to edit this file.

## Project

NeST (Neuro-Symbolic Transpiler) — a compiler for SPLL (Sum-Product Loop
Programming), a probabilistic programming language. Compiles probabilistic
programs to Python or Julia, supporting neural network integration and
probabilistic inference (sampling, exact probability, integration).

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

CLI flags: `-v` verbosity, `-O LEVEL` optimization (0-2), `-k CUTOFF` top-K
threshold, `-c` count branches, `-t` truncate boilerplate, `-d` debug
intermediates (see below).

To prevent having to run `stack test` repeatedly, e.g. to grep for specific
failures, always store the test output to a temporary file and grep that.

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

Every SPLL program compiles into three function variants — **generate**
(forward sampling), **probability** (density/mass at a point), and
**integrate** (probability over a range) — whose availability depends on
tractability, as determined by ModalityInfer. Runtime execution:
`IRInterpreter.hs` (`generateRand` for random sampling, `generateDet` for
deterministic).

## Key Types

- **Expr** (`src/SPLL/Lang/Types.hs`): Main AST — includes `IfThenElse`,
  `LetIn`, `Lambda`, `Apply`, `Uniform`, `Normal`, `ReadNN`, `InjF` (injected
  functions like plus/mult), `Cons`, `TCons`, etc.
- **IRExpr** (`src/SPLL/IntermediateRepresentation.hs`): IR after
  compilation — `IRIf`, `IROp`, `IRLetIn`, `IRLambda`, `IRDensity`,
  `IRSample`, etc.
- **TypeInfo**: Bundle of RType (return type: `TFloat`, `TBool`, `TInt`,
  `ListOf`, `Tuple`, etc.), PType (probabilistic: `Deterministic`, `PNormal`,
  `PLogNormal`, `Integrate`, `Bottom`), and CType (constraints).
- **Value**: Runtime values — `VFloat`, `VInt`, `VBool`, `VList`, `VTuple`,
  `VEither`, `VClosure`, `VThetaTree`, `VSymbol`, `VBranch`, `VADT`, `VAny`
  (VAny is used only for marginal queries).
- **MultiValue**: Structured set of possible values for neural network
  output annotation — `MultiDiscretes [Value]`,
  `MultiTuple MultiValue MultiValue`, `MultiEither MultiValue MultiValue`,
  `MultiADT [(String, [MultiValue])]`, `MultiTypeRef String`.
- **CompilerConfig**: Controls verbosity, optimization level, top-K
  threshold, branch counting, plus flags `pruneAnyChecks`, `noIntegrate`,
  `noProbability`, `noGenerate`, `batched`, `logSpace`.

## Internal Details

Every AST node carries a `TypeInfo` record (`rType` from RInfer, `pType`
from ModalityInfer, `chainName`, and enum/algorithm `tags` from Analysis),
held in a record wrapper around a parametric base functor rather than as
a field on each constructor:

```haskell
data Expr = Expr { ann :: TypeInfo, node :: ExprF Expr }
data ExprF a = IfThenElse a a a | InjF InjFName [a] | Var String | Constant Value | ...
               deriving (Show, Eq, Functor, Foldable, Traversable)
```

A node is written/matched as `Expr ti (IfThenElse c t f)`. The derived
`Functor`/`Foldable`/`Traversable` are what let `SPLL.Lang.Lang`'s
traversals (`tMap`, `getSubExprs`, `setTypeInfo`, etc.) be generic
one-liners. `Constant` deliberately holds a concrete `Value`, not a
`GenericValue a`, since a `Value` can embed `Expr`s inside a `VClosure`
that must stay out of derived traversals. Smart constructors in
`SPLL.Prelude` build nodes through `mkExpr :: ExprF Expr -> Expr`.

`PType` classifies how uncertainty flows through a node, forming a partial
order:

```
Deterministic  >  PNormal, PLogNormal  >  Integrate  >  Bottom
```

`PNormal`/`PLogNormal` are incomparable siblings (different distribution
families) whose meet is `Integrate`. Deterministic values need no
inference; `PNormal`/`PLogNormal` allow closed-form Gaussian shortcuts;
`Integrate` values have a known CDF (via trusted special functions like
`erf`); `Bottom` values can only be sampled from. Each PType implies the
semantics of lower types are available.

### Inference for non-invertible observations

Two IRCompiler engines handle `let`-bindings whose observation can't be
point-inverted onto the bound variable: **set-valued witnesses**
(`setWitnessApply`, for observations that cross a comparison or `if`) and
**plan-guided lazy enumeration** (`planWitnessApply`, for observations over
a neural network's structured output). Both are tried before
forward-chaining point inversion, whose inverses would otherwise crash on
these shapes. Full mechanism, examples, and the `testCases/planEnum*`
pointers: `docs/witness-inversion-engines.md`.

### `observe` (Maybe-valued conditioning)

`observe base pred` is parser sugar, not a dedicated `Expr` constructor —
it desugars to `let v = base in if pred v then right v else left ()`
(`Just x = right x`, `Nothing = left ()`), giving
`p(Just v) = p(base = v) · p(pred v)` and, via structural `ANY`
marginalisation, a proper `Maybe`-valued distribution for free
(`p(Just ANY) + p(Nothing) = 1`). Conditioning is
`p(Just v) / p(Just ANY)`.

The base must be let-bound, not spliced in twice (else a probabilistic
base becomes two independent draws), and a literal lambda predicate is
beta-reduced at parse time — otherwise the bound variable is invisible to
inversion and compilation fails. Known gap: `p(Just ANY)` hard-errors on a
*continuous* observation (set-witness can't handle `ANY` inside a
constructor slot).

## Additional Features

### topK Branch Pruning

`topKThreshold :: Maybe Double` in `CompilerConfig` enables
probability-based branch pruning: the IRCompiler wraps each `IfThenElse`
in probability mode with guards — if `p_cond < threshold` only the else
branch is evaluated, if `p_cond > 1 - threshold` only the then branch,
otherwise both. The same threshold filters enumerable `InjF` branches by
left-parameter probability. Pruned branches contribute zero — this is a
performance optimisation, not an approximation.

### Dimension Counting

Every probability-mode result is a
`PResult { rProb, rDim, rBranches, rImposs }` whose `rDim` tracks
dimensionality: `0` for a discrete mass, `1` for a univariate density, `n`
for multivariate. This determines whether the change-of-variables
correction applies when a value passes through an invertible `InjF`
(multiply by `|derivative of inverse|` when `dim > 0`, nothing when
`dim = 0`). Dimensions **add** under multiplication (independent
continuous variables); under mixture, the **smaller dimension wins** among
possible alternatives. Base cases: `Normal`/`Uniform` emit `dim = 1`;
discrete/deterministic expressions emit `dim = 0`.

### Probability internals (`PResult` / `Semiring`)

`PResult` is built from a combinator vocabulary in `SPLL.Semiring`
(`density`/`mass`/`detP`/`prodP`/`mixP`/`mixSubP`/`enumSumP`/`scaleCoV`/
`shareResult`) rather than hand-written per case, and `rProb` can only be
constructed by routing through it — or one of two escape hatches,
`unsafeLinearP` and `sealP`, for subsystems that assemble bespoke
`IRExpr` formulas (grepping `unsafeLinearP` finds them). Every
probability is computed through a `Semiring` record that's either linear
or log-space (`logSpace` in `CompilerConfig`, CLI `--logSpace`), picked
once per function. **Never hand-write a linear identity on a
probability** — use `srComplement`/`srZero`, not raw arithmetic, since
under log space those are silently different numbers. Full vocabulary,
the rest of the log-space gotchas, and the `shareResult` zero-guard
placement bug: `docs/semiring-presult-internals.md`.

### Impossibility flag

The fourth `PResult` field, `rImposs :: IRExpr`, answers "is this result
structurally impossible?" (wrong `Either` arm, unmatched indicator, failed
applicability guard, off-support sample). `mixP`/`mixSubP` need this fact
to pick the winning alternative — inferring it by comparing probability to
zero is wrong both ways: a deep-tail density can underflow to a true `0.0`
while still possible, and an approximate zero test can discard merely-tiny
densities. `mixWith` branches on the flag alone.

Leaves are possible; `indicatorP`/`guardP` set it on failure; `prodP` ORs;
`mixWith` consumes it (impossible only if every alternative is). It's
spelled as an `IRIf`, never `OpOr`/`OpAnd`, since both operands of an IR
boolean op are evaluated and the guarded-against condition is often what
makes evaluating the other side safe. The compiled result shape is
`(prob, (dim, imposs))`, or with `countBranches`, `(prob, (dim, (bc,
imposs)))`; consumers match it through the `VProbDim`/`VProbDimBC` pattern
synonyms and `resultImpossible`, never the raw tuple shape.

### Branch Counting

`countBranches :: Bool` controls whether the result's third field,
`branchCount`, survives into emitted code (`stripBranchCount` removes it
otherwise). It records how many enumerated branches were actually
traversed (leaves emit 0 or 1, branches sum their children); a pruned
`topK` branch contributes 0.

### Query-Type Guard

`checkQueryType :: Bool` (default `True`, CLI opt-out `--noTypeCheck`)
wraps every prob/integ function root in a guard checking the query value
structurally conforms to the program's return type (`IRConformsTo`,
consumed by all three backends) — without it, a wrong-typed query either
silently returns a bogus number or hits a deep panic. The marginal
wildcard (`VAny`) is accepted at every level so marginal queries aren't
penalized.

### Debug: Intermediate Stage Dump (`-d`)

`showIntermediates :: Bool` (CLI `-d`/`--debugIntermediates`) prints the
fully-annotated AST after each pipeline stage to stderr via
`prettyPrintProg`, showing the progressive accumulation of annotations:

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

Use this to identify which stage introduced a defect when a program
compiles incorrectly. `IRCompiler` selects the inference algorithm per
node directly from the `pType`/`DiscreteValues` annotations visible after
Modality Inference.

### Neural Declarations

Neural networks are declared separately as
`NeuralDecl = (String, RType, Maybe MultiValue)` and enter the global type
environment before inference; `ReadNN name param` calls the named network
at runtime. A `MultiValue` annotation on the declaration lets
`InferenceRule` matching select enum-aware algorithms for downstream
comparisons — except a continuous leaf (`Real`, incl. `_` on a `Float`
slot) is never tagged for enumeration, since enumerating only the discrete
residue would silently drop continuous mass.

The `of ...` clause mirrors the output `RType`:

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

Auto-derivation (`_`, or an omitted clause) fills slots from the RType
(`Float`→`Real`, `Bool`→`[True, False]`, `Tuple`/`Either`/non-recursive
`ADT`→recurse); `Int`/`Symbol` need an explicit enumeration, and a
recursive `ADT` only auto-derives with a default depth on its `data`
declaration (`data T = … depth N`) — otherwise give a depth-bounded
override (`3x.{...}`) or compilation errors. Only *direct* self-recursion
is auto-detected.

## Test Structure

The suite runs under tasty (`tasty-quickcheck` for properties, `tasty-hunit`
for unit tests). Each module exports a `TestTree`; `Spec.hs` assembles them
under the groups Spec / Corpus / Parser / Internals / Rejection / Encode /
Showcase / End2End.

- `test/Spec.hs` — main entry, static Spec properties, and the Corpus
  group of metamorphic properties (sampling-vs-PDF, topK, branch counting,
  P(ANY)=1, validation) generated from `testCases/`
- `test/TestParser.hs` / `TestInternals.hs` — parser and internal-function
  unit tests
- `test/TestRejection.hs` — unhappy-path tests: invalid or ill-typed
  programs are rejected with the expected reason
- `test/TestEncodeProperties.hs` — AutoNeural encode tests, plus
  corpus-driven roundtrip checks that encode/decode preserves slot layout
  and slot semantics
- `test/TestShowcase.hs` — documentation drift guard: checks
  `examples/showcase.ppl`/`.tst`, freezes named definitions, and compiles
  every ` ```spll ` block in `README.md` as a doctest
- `test/End2EndTesting.hs` — integration tests from `testCases/`
  `.ppl`/`.tst` pairs
- `test/TestCaseParser.hs` / `ArbitrarySPLL.hs` — the `.tst` parser and
  QuickCheck `Arbitrary` instances

A `.tst` file may start with two optional header lines, in either order: a
routing header `backends: interpreter, julia, python` (any non-empty
subset; default is all three scalar backends) and a standalone `slow`
line, plus two opt-in tokens: `batched` (declares batched-mode
eligibility, asserted by the `BatchedPython` group rather than filtered)
and `dense` (declares a finite query domain, presupposes `batched`).
Comments are only allowed as a leading/trailing block, not interleaved
between test cases; an unparseable line is a hard parse failure naming
the file and line. Beware CRLF files when adding a token by script —
append before the `\r`.

Expected values are compared with `probTolerance` (1e-4). A `p(...)`/
`cdf(...)` expectation takes an optional third component, the expected
impossibility flag: `p(x) = (prob, dim, imposs)`, checked by all three
backends when declared (a two-component expectation checks prob/dim
only). The corpus rows that pin it target its *structural* semantics
rather than a zero test — notably `normal p(40.0)`, a 40-sigma tail whose
density underflows to a hard `0.0` while `imposs` must stay `False`.

### Slow tests

**The `Slow` group is currently known-broken** — it is not green, and
failures there are pre-existing rather than caused by whatever change you
are making. Do not treat a red `NEST_SLOW_TESTS=1` run as a regression
without first confirming the same failure on an untouched checkout. The
default (non-slow) suite is the gate.

Tests expensive enough to noticeably slow `stack test` but unlikely to
catch regressions elsewhere are skipped by default, run via
`NEST_SLOW_TESTS=1 stack test`: a `.tst` file's `slow` header, or a
`TestInternals.hs` case placed in `slowInternalsTests`.

### Benchmarks

`benchmarks/` holds compiler-performance stress programs
(`stressPlanEnum.ppl`, `stressContinuous.ppl`). They pin no values and
aren't part of the test suite — run and time them via the CLI:

```bash
stack run -- -i benchmarks/stressContinuous.ppl compile -l python -o /tmp/b.py   # time this
```

Always warm up once before timing: the first invocation after a source
change includes stack's rebuild-and-register, which dwarfs the compile
itself. For the test suite, `TASTY_HIDE_SUCCESSES=false` gives per-test
timings and `--ta '-t 60'` bounds each test.

`benchmarks/batched_vs_scalar.py` instead times the *emitted code*: a
scalar per-point loop against one batched call for the same `ReadNN`
program (needs a torch-enabled Python, same lookup as `BatchedPython`).

### Fuzz tests

`test/TestFuzz.hs` (group `Fuzz`, lives inside `Slow`) runs randomly
generated SPLL programs (`test/ArbitrarySPLL.hs`) against the same
metamorphic invariants the hand-written corpus checks — P(ANY)=1, topK
never inflates probability, branch counting doesn't change the
probability value, probability is never negative — rather than known
expected values. Details, the raw-vs-typed generator split, and the
`SuperSlow` sampling-vs-PDF tier: `docs/fuzz-testing.md`.

### Batched Mode (PyTorch tensorizer)

`batched :: Bool` (CLI `--batched`) opts into batched inference: instead
of scalar Python evaluated one query point at a time, emit branch-free
elementwise PyTorch that runs a whole `[B]`-shaped batch at once
(`torch.where` instead of a data-dependent `if`, via `SPLL.IRSelectPass`
and `CodeGenPyTorchBatched`). Tested by the `BatchedPython` group, gated
on the `.tst` `batched`/`dense` header tokens and a torch-enabled Python
(`NEST_TORCH_PYTHON` → a venv path → `python3`; repo convention:
`~/.cache/nest/torchvenv`) — skips with a visible note if none is found.
Mechanism, the dense-enumeration mode, and refusal rules:
`docs/batched-mode-pytorch-tensorizer.md`.

## Runtime Libraries

Generated Python code depends on `pythonLib.py` (scalar) or
`pythonLibBatched.py` (batched mode, see above); generated Julia code
depends on `juliaLib.jl`. These provide runtime helpers for the transpiled
inference functions.
