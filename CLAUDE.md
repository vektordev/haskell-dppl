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
stack run -- -i file.ppl compile -o output.py -l python   # Compile to Python (-o is required)
stack run -- -i file.ppl compile -o output.jl -l julia    # Compile to Julia
stack run -- -i file.ppl generate                         # Forward sampling
stack run -- -i file.ppl probability -x 0.5               # Query P(X=0.5)
stack run -- -i file.ppl cumulative -x 0.5                # CDF query P(X<=0.5)
# Test selection (tasty patterns; `--ta '-l'` lists every group and test name):
stack test --ta '-p Spec'                # run one group
stack test --ta '-p "!/End2End/"'        # everything except a group
stack test --ta '-p TopK'                # any test whose name matches a substring
stack test --ta '-p "/End2End.Interpreter/ && /dice/"'   # one .ppl test case
stack test --ta '-l'                     # list all test names
# Output is quiet-on-success by default; show every test (with per-test timings) via:
TASTY_HIDE_SUCCESSES=false stack test
```

Global flags (before the subcommand): `-v` verbosity, `-O LEVEL`
optimization (0-2), `-k CUTOFF` top-K threshold, `-c` count branches, `-d`
debug intermediates (see below), and the long-form `--pruneAnyChecks`,
`--noIntegrate`/`--noProbability`/`--noGenerate`, `--noTypeCheck`,
`--batched`, `--logSpace`. Per-subcommand flags: `--help`.

To prevent having to run `stack test` repeatedly, e.g. to grep for specific
failures, always store the test output to a temporary file and grep that.

## Compilation Pipeline

```
SPLL source (.spll/.ppl)
  → Parser.hs (megaparsec) → AST (Lang/Lang.hs, Lang/Types.hs)
  → Validator.hs → Typing/RInfer.hs (return types)
  → Analysis.hs (DiscreteValues tags) → Typing/ForwardChaining.hs (chain names)
  → Typing/ModalityInfer.hs (PTypes) → Analysis.hs (IsConditional tags)
  → IRCompiler.hs → IR (IntermediateRepresentation.hs)
     Three compilation branches: generate, probability, integrate
  → IRSelectPass.hs (batched only) → IROptimizer.hs (const folding, CSE, let-in)
  → CodeGenPyTorch.hs, CodeGenPyTorchBatched.hs, or CodeGenJulia.hs
```

`SPLL.Prelude`'s `compile` is the authority on stage order; `-d` dumps the
program after each one.

Every SPLL program compiles into three function variants — **generate**
(forward sampling), **probability** (density/mass at a point), and
**integrate** (probability over a range) — whose availability depends on
tractability, as determined by ModalityInfer. Runtime execution:
`IRInterpreter.hs` (`generateRand` for random sampling, `generateDet` for
deterministic).

## Key Types

- **Expr** (`src/SPLL/Lang/Types.hs`): Main AST. `ExprF` is a small closed
  set — `IfThenElse`, `InjF` (injected functions like plus/mult), `Var`,
  `Constant`, `Lambda`, `Apply`, `ThetaI`, `Subtree`, `ReadNN`. Everything
  else is sugar assembled from those by `SPLL.Prelude`: `letIn x v b` is
  `Apply (Lambda x b) v`, `Uniform`/`Normal` are `Var`s, `cons`/`tCons` are
  `InjF`s.
- **IRExpr** (`src/SPLL/IntermediateRepresentation.hs`): IR after
  compilation — `IRIf`, `IROp`, `IRLetIn`, `IRLambda`, `IRDensity`,
  `IRSample`, etc.
- **TypeInfo**: `rType` (return type: `TFloat`, `TBool`, `TInt`, `TSymbol`,
  `ListOf`, `Tuple`, `TEither`, `TADT`, `TArrow`, etc.), `pType`
  (probabilistic: `Deterministic`, `PNormal`, `PLogNormal`, `Integrate`,
  `Bottom`, and `NotSetYet` before inference runs), `chainName`, and `tags`
  (`DiscreteValues`, `IsConditional`). `PType`'s `PArr`/`TVar` are dead code.
- **Value** (`= GenericValue Expr`): Runtime values — `VFloat`, `VInt`,
  `VBool`, `VSymbol`, `VUnit`, `VList`, `VTuple`, `VEither`, `VADT`,
  `VClosure`, `VThetaTree`, `VError`, plus `VAny`/`VAnyExcept` (used only for
  marginal queries).
- **MultiValue**: Structured set of possible values for neural network
  output annotation — `MultiDiscretes [Value]`,
  `MultiTuple MultiValue MultiValue`, `MultiEither MultiValue MultiValue`,
  `MultiADT [(String, [MultiValue])]`, `MultiTypeRef String`,
  `MultiContinuous` (a `Real` leaf), `MultiAuto` (the `_` placeholder).
- **CompilerConfig**: Controls verbosity, optimization level, top-K
  threshold, branch counting, the marginal-materialization cardinality budget
  (`materializationCardinality`, default 10000 — see Marginal Materialization
  below), plus flags `pruneAnyChecks`, `noIntegrate`, `noProbability`,
  `noGenerate`, `batched`, `logSpace`.

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
`erf`); `Bottom` values offer nothing better than sampling. Each PType
implies the semantics of lower types are available.

### Modality: the layer `PType` projects from

`PType` is not the probabilistic type system but a flat, lossy projection of
one: `Typing/Modality.hs` carries a capability lattice (subsets of
`{CanSample, CanDensity, CanIntegrate, CanExact}`) crossed with orthogonal
support-finiteness and distribution-family axes, and `Typing/ModalityInfer.hs`
infers it bottom-up before `projectGround` flattens it onto the five `PType`
rungs. Read those two modules before changing what an expression is allowed to
do — notably, `PNormal` and `Integrate` are the same capability rung differing
only by family, and `Bottom` is a collapse of four distinct levels.

### Inference for non-invertible observations

Two IRCompiler engines handle `let`-bindings whose observation can't be
point-inverted onto the bound variable: **plan-guided lazy enumeration**
(`planWitnessApply`, for observations over a neural network's structured
output) and **set-valued witnesses** (`setWitnessApply`, for observations
that cross a comparison or `if`). Plan enumeration is tried *before*
forward-chaining point inversion, whose inverses would otherwise crash on
those shapes; set-valued witnesses are the fallback *after* it, taken when
no occurrence of the bound variable is point-invertible at all. Full
mechanism, examples, and the `testCases/planEnum*` pointers:
`docs/witness-inversion-engines.md`.

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
probability-based branch pruning. The compiler threads an `accProb` (the
probability of reaching the current point) through inference; each
`IfThenElse` arm in probability mode is guarded on its *accumulated* path
probability (`accProb * p_cond`) against `TOP_K_CUTOFF`, and an arm below
the cutoff is dropped. The same threshold filters enumerable `InjF`
branches by `accProb * p_left`.

Pruning is **lossy** — a dropped branch's mass is simply gone. Hence the
one-sided invariants: topK never *inflates* a probability
(`Corpus.TopKNeverInflates`), and only threshold 0 is exact
(`Corpus.TopKZeroThreshMatchesExact`).

### Marginal Materialization

A point query on a nested enumerable `InjF` chain (`readMNist(a) ++
readMNist(b) ++ …`) re-descends into its left operand once per enumerated
value, and that descent is *eager* — so an n-term chain costs
`T(n) = |D(n-1)|·T(n-1)`, super-exponential. No optimizer pass recovers
it: the recomputation is a runtime loop re-entry, not duplicated IR.

**Tier 0 materialization** replaces it with a streaming convolution. When
an *operand* is itself such a chain, its marginal is tabulated once over
its finite domain — one let-bound scalar cell per value, each cell an
unrolled convolution over the operand grid — and the loop body reads a
cell instead of re-descending. Measured on n-term digit addition (emitted
Python): 14x faster at n=4, 87x at n=5, 626x at n=6, ~3900x at n=7
(52.8s → 0.014s), with neural-cell evaluations going from ×10 per added
term to exactly quadratic.

Three things make it cheap, and each is load-bearing:

- Cells are **let-bound scalars, not an IR table**. `IRExpr` has no dense
  array and `IRIndex` is an O(n) cons-cell walk, so a runtime table would
  turn the `O(n·range)` DP into `O(n·range²)` on the path the whole
  corpus runs on.
- Only an operand that is **itself** a nested enumerable `InjF` is
  tabulated; the queried node keeps the ordinary path. Tabulating the
  queried node would be a pessimization for an invertible op (its point
  query costs `O(|D_left|)`, its table `|D_left|·|D_node|`, and one cell
  is read). A two-term program's emitted IR is therefore unchanged.
- Tables are built by evaluating the InjF's **forward** function at
  compile time over the operand grid (`propagateValues`, the same
  evaluator Analysis uses for the domains), never by inverting — so
  forward-only ops (`and`/`or`/`max`) need no special case, and cell terms
  accumulate in the same order the enumeration loop does, making the
  result bit-identical to the path it replaces rather than merely close.

`topK` is preserved exactly: `accProb` is only modified at an
`IfThenElse`, so every level of a chain shares one `accProb` and the
per-term guard is the same test on the same value, dropping exactly the
terms the in-loop cutoff drops. `rImposs` is deliberately not tracked per
cell — the enumeration paths already discard a sub-result's dim, branch
count and flag, deriving the node's own flag from the summed mass via
`opaqueMass`.

Two preconditions gate it, and both refuse rather than analyse:

- **Decomposability** (`materializationVerdicts`): tabulating two
  operands separately is wrong if they share an enumerated latent
  (`testCases/letThreadEnumerable` is the canary,
  `testCases/sharedLatentNestedChain` the nested one). Unlike
  `injFLatentVerdicts`, this walk binds lambda parameters, each to a
  latent identity of its own.
- **Cardinality** (`materializationCardinality :: Int`, default 10000, in
  `CompilerConfig`): `Analysis.materializationDomain` is a total
  predicate over a node's tags returning the domain to tabulate or
  `Nothing`; anything unannotated, non-finite, or over budget answers
  `Nothing`, since over-refusing costs performance while under-refusing
  costs correctness silently. The same budget bounds the operand *grid* a
  convolution unrolls — "the domain is small" and "the unrolling is
  affordable" are one question, not two, and a change to either has to be
  made on both. Per-node, deliberately not cumulative across nesting
  levels. Set it to 0 to disable materialization entirely (the
  differential tests' off-switch).

A leaf cell holds a whole compiled sub-inference rather than a few
references, so it is the one place materialization multiplies IR instead
of rearranging it. `pointQueryTable` compiles the first value as a probe,
measures it, and declines the table unless the copy is small
(`maxTabulatedLeafNodes`) and the total fits the budget — a `ReadNN`
digit read is 10 IR nodes, while an arbitrary enumerable if-tree can be
thousands, where copying per value cost 14x the IR and turned a 0.17s
compile into 16s.

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
or log-space (`logSpace` in `CompilerConfig`, CLI `--logSpace`), fixed for
the whole compile. **Never hand-write a linear identity on a
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
`mixWith` consumes it (impossible only if every alternative is).
`impossibleWhen`, which folds a *fresh* condition onto an existing flag,
spells that as an `IRIf` rather than an `OpOr`: both operands of an IR
boolean op are evaluated, and the guarded-against condition is often what
makes evaluating the other side safe or terminating. Combining two
already-computed flags (`prodP`, `mixWith`) uses plain `orIR`/`andIR`. The
compiled result shape is
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
consumed by the three scalar backends; batched mode strips the root guard
instead) — without it, a wrong-typed query either silently returns a bogus
number or hits a deep panic. The marginal wildcard (`VAny`) is accepted at
every level so marginal queries aren't penalized.

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
| After Select Pass | `IRIf` → `IRSelect` retagging (a no-op unless `--batched`) |
| After Optimization | Pseudo-code IR after constant folding, CSE, let-in optimization |

Use this to identify which stage introduced a defect when a program
compiles incorrectly. `IRCompiler` selects the inference algorithm per
node directly from the `pType`/`DiscreteValues` annotations visible after
Modality Inference.

### Neural Declarations

Neural networks are declared separately as
`NeuralDecl = (String, RType, Maybe MultiValue)` and enter the global type
environment before inference; `ReadNN name param` calls the named network
at runtime. A `MultiValue` annotation on the declaration becomes a
`DiscreteValues` tag (`Analysis.hs`), which is what lets `IRCompiler` pick
enum-aware algorithms for downstream comparisons — except that an
annotation containing a continuous leaf anywhere (`Real`, incl. `_` on a
`Float` slot) is declined entirely, since enumerating only the discrete
residue would silently drop continuous mass.

The `of ...` clause mirrors the output `RType`:

```
multival ::= _     -- MultiAuto: auto-derive from RType
           |  Real -- Float leaf
           |  [value1, value2]      -- MultiDiscretes: explicit enumeration
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
for unit tests). Each module exports a `TestTree` which `Spec.hs` assembles
into the top-level groups (`--ta '-l'` prints the current list):

- `test/Spec.hs` — main entry, the static `Spec` properties, and the
  `Corpus` group of metamorphic properties generated from `testCases/`
  (validation, sampling-vs-PDF, topK, branch counting, P(ANY)=1, log-space
  vs linear)
- `test/TestParser.hs` / `TestInternals.hs` — parser and internal-function
  unit tests
- `test/TestRejection.hs` — unhappy-path: invalid or ill-typed programs must
  be rejected with the expected reason
- `test/TestModality.hs` / `TestModalityInfer.hs` — the capability lattice
  and its projection; hand-verified modalities the engine must pin
- `test/TestDeterminism.hs` — the forward determinism dataflow and its
  call-graph fixpoint
- `test/TestEncodeProperties.hs` — AutoNeural encode, plus corpus-driven
  encode/decode roundtrip checks on slot layout and semantics
- `test/TestShowcase.hs` — documentation drift guard: `examples/showcase.*`
  (incl. the `.freeze` definitions) and every ` ```spll ` block in
  `README.md` as a doctest
- `test/End2EndTesting.hs` — `.ppl`/`.tst` integration against interpreter,
  Julia and Python, plus the batched groups (see Batched Mode below)
- `test/TestFuzz.hs` — `Fuzz`, inside the opt-in `Slow`/`SuperSlow` groups
- `test/TestCaseParser.hs` / `ArbitrarySPLL.hs` / `TestTolerances.hs` — the
  `.tst` parser, QuickCheck generators, shared numeric tolerances

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

A query point is written in the *value* grammar (`Parser.pValue`), which
covers ADT constructor values by juxtaposition — `p(Leaf)`,
`p(Node Leaf Leaf)`, `p(Node (Node Leaf Leaf) 0.5)`; a field that is itself
an application needs parentheses. Prefer querying an ADT program at a point
over querying a `Bool`/`Float` projection of it: the projection never
reaches a sibling constructor's field accessors, which is how
`forward-missing-constructor-guard` shipped.

### Slow tests

**The `Slow` group is currently known-broken** — it is not green, and
failures there are pre-existing rather than caused by whatever change you
are making. Do not treat a red `NEST_SLOW_TESTS=1` run as a regression
without first confirming the same failure on an untouched checkout. The
default (non-slow) suite is the gate.

Tests expensive enough to noticeably slow `stack test` but unlikely to
catch regressions elsewhere are skipped by default, run via
`NEST_SLOW_TESTS=1 stack test`: a `.tst` file's `slow` header, a
`TestInternals.hs` case placed in `slowInternalsTests`, and the whole
`Fuzz` group.

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
probability value, probability is never negative, mixtures follow the
dimension-combination rules — rather than known expected values, plus
crash-freedom on both generators. Details, the raw-vs-typed split, and the
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
