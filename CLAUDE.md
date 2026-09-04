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

### Compiler warnings

`src/` and `app/` build under `-Wall -Wcompat -Wincomplete-record-updates
-Wredundant-constraints -Werror` (set in `package.yaml`; the `.cabal` is
hpack-generated and gitignored) with **zero warnings**, and so does `test/`
under the same flags. The backlog is empty: there are no `-Wno-*` flags in
`package.yaml` and none may be added. Fix the code instead, or -- for a genuine
false positive -- scope an `OPTIONS_GHC` pragma to the one module and say why.

Exactly one module does that today: `test/ArbitrarySPLL.hs` carries
`-Wno-orphans`, because its `Arbitrary` instances for `Program`/`Expr`/`Value`/
`TypeInfo` are test fixtures, and the only way to un-orphan them would be to
declare them in `SPLL.Lang.*` -- putting a QuickCheck dependency on the
library.

The last five to go were three `-Woverlapping-patterns` and two
`-Wdeprecations`, each a real defect rather than noise:

- `juliaUnaryOps` / `RInfer`'s `apply` / `toIRGenerate` each ended in an
  unreachable `error` catch-all over an already-exhaustive match. Deleted:
  `-Wincomplete-patterns` flags a future missing constructor at compile time,
  which strictly beats the runtime `error` the catch-all offered. (The
  neighbouring `juliaOps` catch-all is *not* redundant and stays.)
- `Prelude`'s `pPrintIfVerbose`/`pPrintIfMoreVerbose` used
  `Debug.Pretty.Simple.pTraceShow`, which is `DEPRECATED` precisely to nag
  about leftover debug traces. These are real `-v` functionality, so they now
  compose the non-deprecated pieces directly: `trace (TL.unpack (pShow s))`.

and the two `unused-top-binds`: `IRCompiler`'s `findLambdaVars`, live only via
a commented-out block that referenced three functions (`findBoundVariable`,
`getUnappliedLambdas`, `applyLambdas`) which no longer exist anywhere -- block
and function both deleted; and `PlanWorld`'s `pwFactor`, whose field was only
ever read positionally, so `planWorldMass` now reads its world through the
selectors.

The `test/` pass (168 warnings) was mostly mechanical, but four findings were
not:

- `TestParser`'s `testExpressions`, a table of hand-written lambda/apply
  expressions, had no driver at all -- the module's tests are `$(allProperties)`
  and nothing referenced the table. It now has one
  (`prop_ListedExpressionsRoundtrip`), which passes; that is the 1484th test.
- `TestFuzz`'s `$(allProperties)` was silently skipping
  `prop_Fuzz_SamplingMatchesPDF`, which is defined *after* the splice and so is
  not in scope at it. That exclusion is wanted (the property is a SuperSlow
  tier registered by hand), but it was load-bearing on definition order. The
  binding is now `fuzzSamplingMatchesPDF`, excluded by not matching the `prop_`
  prefix, with the tasty-visible name unchanged.
- `TestParser`'s `programToString` never rendered `data` declarations, and the
  two helpers written for that (`adtDeclToString`/`adtConstructorToString`)
  were unreachable. That is *currently* harmless -- `Arbitrary Program` always
  builds an empty ADT list -- so the helpers are gone and the constraint is
  now a comment on `programToString` instead of silent dead code.
- `ArbitrarySPLL`'s `exprGens` had four entries commented out with three of
  their generators (`mkThetaI`/`mkMultI`/`mkPlusI`) left defined-but-unused --
  and a fourth, `mkGreaterThan`, whose commented entry had outlived its
  definition entirely. All four are retired, with a comment recording that
  re-enabling any of them means writing the generator again.

Two module-wide idioms did most of the mechanical work: `TestCaseParser`'s
`symbol` now returns `()` rather than the matched text no caller wanted (23
`-Wunused-do-bind`s at once), and the shadowing of `Test.QuickCheck`'s
`sample`/`total`/`label`/`collect` and `System.Process`'s `env`/`cwd` was
fixed at the import (`hiding`, or an explicit import list) rather than by
renaming ~50 local bindings.

The two incomplete-pattern categories were retired by filling in the missing
cases, mostly as named helpers that state the invariant and `error` with the
offending value (`soleOutputVar`/`inversionFor`/`lookupFPair` in
`PredefinedFunctions`, `binaryInputVars`/`equivalentLambda`/`inverseDerivative`
in `IRCompiler`, `asLambda` in `ForwardChaining`, `mockLogits` in `MockNN`),
and in a few places by routing a genuine failure into an existing error channel
instead (`Prelude`'s `runProb`/`runIntegNamedC` now answer `Left` when a
definition has no compiled variant for that mode; the `Parser` builder maps
answer `Left` on a wrong argument count). `IRCompiler` carries an
`OPTIONS_GHC -fmax-pmcheck-models=1000` pragma: the coverage checker exceeds
its default 30-model budget on two `Maybe (RType, Bool)` cases and then reports
those exhaustive matches as incomplete.

## Compilation Pipeline

```
SPLL source (.spll/.ppl)
  → Parser.hs (megaparsec) → AST (Lang/Lang.hs, Lang/Types.hs)
  → Validator.hs → Typing/RInfer.hs (return types)
  → Analysis.hs (DiscreteValues tags) → Typing/ForwardChaining.hs (chain names)
  → Typing/ModalityInfer.hs (PTypes) → Analysis.hs (IsConditional tags)
  → IRCompiler.hs → IR (IntermediateRepresentation.hs)
     Three compilation branches: generate, probability, integrate
  → IRTensorPass.hs (enum sums → tensor map/reduce)
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
  `IRSample`, etc., plus `IRBuiltin Builtin [IRExpr]` for the tensor
  operations (see Tensors in the IR below).
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

### Forward chaining never re-derives a chain name it already has

`ForwardChaining.solveHCSet` fulfils, per clause group, the first clause whose
premises are all known **and whose conclusion is not already derived**. The
second half of that test is what keeps the fulfilled clause set acyclic, and it
is a correctness requirement, not an optimisation.

A chain name reachable by two routes makes it bite. In an over-determined
observation — `let x = Uniform in let y = Uniform in (x, (x+y+3, x+y+2))`, where
both inner slots recover `y` and hence `x` — each occurrence of `x` sits in its
own bidirectional equivalence group with the binding. Chaining reaches the
binding through slot 1, walks all the way round through the second slot's
occurrence, and (without the test) fulfils a *second* clause concluding the same
binding, closing a cycle. `topSortDAG` has no defined behaviour on a cycle and
`cutList` then truncates, so codegen emitted a shadowing `let ast18 = ast14`
over an `ast14` no earlier clause binds — `Variable ast14 not declared` at run
time, on every backend, with the query having type-checked and compiled
cleanly.

Dropping the second derivation loses nothing: forward chaining's premise
throughout (`mergeExpr`'s candidate merge says so explicitly) is that two routes
to a name are semantically equal. The redundancy is still *paid for* — the
observation's manifold constraint is carried by the deterministic-slot
consistency check IRCompiler emits for the query as a whole, a dim-0 indicator
factor, so `p((a,(b,c)))` above is `p(a)·p(b−a−3)·[c−b == −1]` at dim 2.
Corpus: `overDeterminedSharedLatent`, `degenerateSameLatentSum`.

### Enumerated branches are compiled forward, and that premise is checked

`toIREnumerate` compiles the condition and both arms of an enumerated
conditional with `toIRGenerate` and compares the result against the sample. That
is exact only while the operand is **deterministic given the enumerated
latents** — the premise its own fallback equation states. Where the premise
failed, the same code emitted a fresh random draw compared against the query
value: a "probability" returning a different number on every call with the same
argument, with no crash and no diagnostic on the Python and Julia backends.

The reachable shape is unbounded self-recursion with no decreasing argument
(`main = let a = genA in let b = genB in if a == b then a else main` — resample
and retry on disagreement), which spliced `main_gen()` into `main_prob`.
`dice.ppl`-style recursion is unaffected: it recurses on `x + (-1.0)`, which
statically decreases.

`requireDeterministicUnderEnum` now checks each generated operand and refuses at
compile time, naming the generator it would have called — matching the sibling
witness-construction failures, which fail loudly. Solving the fixed point
algebraically (the marginal *is* closed-form for that program) was declined: it
would make "does my program infer?" unpredictable from the source. The refusal
is lazy and lives inside the prob/integ bodies, so `generate` and
`--noProbability --noIntegrate` compiles of such a program still work.

The purity verdict is the optimizer's own `isPureGiven` (an `IRSample`, or a
`_gen` reference not proven deterministic), told which generators are
deterministic by `CompilerMetadata.detGenNames` — built once per compile from
`Typing/Determinism.functionSummaries`. `isEffectfulVar` alone is a name test
that calls *every* `_gen` reference random, and an enumerated inference body is
written almost entirely in terms of deterministic helper calls, so a name test
would refuse the whole corpus.

Two things this is **not**. It is the local guard for the enumeration path only;
the central "no `generate` call in any probability-mode body" invariant is the
docs-repo investigation `generate-backed-inference-sweep`. And it needed a
soundness fix in `Determinism` first: a *nullary* top-level function is
referenced as a bare `Var` with no `Apply` node, so `genA` in `let a = genA`
fell through to the unbound-name `True` default and a whole random draw was
reported as a known anchor. `detExpr`'s `Var` rule now consults the call-graph
summary, which can only move `True → False` and so under-approximates in the
direction the module already documents as safe.

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
inversion and compilation fails.

On a **continuous** observation the denominator `p(Just ANY)` is answered by
the set-witness engine: a wildcard in a constructor slot leaves the tag pinned
but the payload unconstrained, so the point constraint is dropped and the
observation's interval kept, measured as a CDF difference (dim 0) rather than
a density. `intersectSet` spells that as `WChoice`, a *runtime* choice of
constraint set — the wildcard is a property of the query sample and has no
static trace in the witness template.

`invertToWorlds` has cases for the boolean connectives (`and`/`or`/`not`), so
`(v > lo) && (v < hi)` compiles the same as the nested-if spelling: each leaf
is inverted at both canonical polarities (`invertBoolToWorlds`, reusing
`invertToWorlds` itself the same way the `IfThenElse` condition case already
does), then recombined. `and`/`or` at their "natural" polarity (and+True,
or+False) intersect directly; the other polarity needs a disjoint
decomposition (`not(a&&b) = not(a) or (a&&not(b))`, `a||b = a or
(not(a)&&b)`) so the two possibly-overlapping sets of worlds are never both
measured — getting that wrong double-counts the overlap. `not` just swaps
which list is which. Mirrors the plan-guided engine's analogous
`planInvert`/`planInvertBool` fold over (True-worlds, False-worlds) pairs.
Corpus: `observeTwoSidedIntervalAnd` (the `&&` twin of `observeTwoSidedInterval`)
and `observeDisjointTails` (`||`, the double-counting canary).

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

### Tensors in the IR

`IRBuiltin Builtin [IRExpr]` carries four operations over a **tensor** — a
statically-shaped, flat, homogeneous block of values (`VTensor Shape [Value]`,
row-major, outermost axis first), as against `VList`'s cons spine:

| builtin | shape | means |
|---|---|---|
| `BTensor sh` | variadic, `shapeNumel sh` args | build a tensor from its elements |
| `BMap` | `[IRLambda v body, t]` | elementwise map, shape-preserving |
| `BReduce op axis` | `[t]` | fold along `axis` with `op`, dropping it |
| `BIndex axis` | `[t, key]` | read along `axis` at a runtime key, dropping it |

`Shape`/`Extent` live in `Typing/RType.hs`, because the typed surface tensor of
the `tensors-in-core-language` design is `TTensor Shape RType` over the same
type. `Extent` is a one-constructor sum (`EFixed Int`) deliberately: admitting
shape *variables* later is then a new constructor rather than an arity change
to every shape pattern.

**The map binds its variable by taking an `IRLambda` argument**, not by
carrying a `Varname` field. That keeps the flat argument list, and most generic
passes then need no new case at all — `freeVarsIR`, `binderOf`, CSE scoping and
`allNamesIR` already handle `IRLambda`. Three places *do* need to see through
it, because they would otherwise refuse or mis-scope a compile-time unroll:
`IRSelectPass.isTensorFragment`, `CodeGenPyTorchBatched`'s `batchedGuard`, and
`IROptimizer.loopBinder` (which is also the one place listing which forms
iterate, so the loop-invariance analyses stop re-matching a constructor set).

`SPLL.IRTensorPass` rewrites the enum-sum family onto this, for every backend:
`IREnumSum`/`IRLogEnumSum` become `reduce op (map f domain)`, and
`IREnumSumPaired` becomes **one** let-bound map reduced **twice** — which is
the sharing that node existed to fake. The enum-sum constructors themselves are
not retired (task `retire-irenumsum`); the pass leaves them unreachable rather
than absent.

Only **rank 1 and axis 0** are emitted. The representation admits any rank and
the interpreter implements it (`fibres`/`rewrap` do the stride arithmetic, and
`Internals/tensor builtins` pins the layout); the three backends refuse higher
rank with a named diagnostic rather than emitting something plausible. Nothing
produces a rank > 1 tensor today.

One refusal the pass did **not** preserve, contrary to its own doc comment:
`--batched --logSpace`. `CodeGenPyTorchBatched`'s `emittable` has no
`IRLogEnumSum` case (and refuses the log variant of `IREnumSumPaired`
explicitly), so a log-space batched compile used to be rejected at the guard.
After lowering there is no `IRLogEnumSum` left to reject — the node is a
`BReduce ROpLogSumExp`, which `emittable`'s blanket `IRBuiltin{} -> True`
admits and which `tensor_logsumexp` in `pythonLibBatched.py` already
implements. The combination now compiles and gives correct answers, so this
reads as a capability the pass gained for free rather than a hole; but nothing
in the suite covers it (no `.tst` carries a log-space token), and the comment
at `emittable`'s paired case still claims a refusal that no longer bites.

Measured against the pre-lowering compiler: emitted scalar Python is 0–4%
*smaller* and 1.09x faster with bit-identical results; batched Python is
byte-identical in size and 1.00–1.04x, bit-identical at two enumeration terms
and within 7.5e-9 at four (the reduce reassociates). The larger speedups the
design predicts belong to the `BIndex` consumer, which nothing wires up yet.

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

`anySafe` guards each of the four `PResult` fields with its own `isAny` test
and wraps each in the sub-result's let-in block, so a block **two** fields read
was emitted twice — and for an enumerated sum that block holds the most
expensive node in the program. `opaqueMass` let-binds the sum precisely so the
impossibility flag reads the value rather than recomputing it; the per-field
wrap then undid exactly that, handing `rProb` one copy of the enumeration and
`rImposs` (only `that value == srZero`) another. CSE cannot merge them and
should not: the copies sit in the else-arms of two different `isAny` ifs, so
sharing them means hoisting the enumeration above the guard whose job is to
skip it on a marginal query.

`anySafeShared` binds the packed result once instead, on `shareResult`'s rules
— only the fields that actually read the block go into the tuple, so a
statically-known dim or flag stays the constant it is rather than being hidden
from folding. It is gated on `blockIterates`: share only when the block
contains a **loop** (an enum-sum, `IRMap`, `BMap`, or `BReduce`). That gate is
a claim about run time, not size — what makes a second copy cost anything is
that it is a second traversal, and a block of constants and arithmetic folds to
a few literals whether copied or not. A pre-optimization node count was tried
first and is the wrong question: `testCases/equalsCoin` builds ~100 nodes that
fold to four literals, passing any size gate with nothing worth sharing.

Measured over the corpus: emitted scalar Python totals 68% of its former size
(`clevrEqualLargeMetalSphere*` 2.8x smaller, the `mNistAdd` family 1.6–1.8x),
`mNistAdd4`'s probability function goes from two enumeration passes and 62
neural-forward call sites to one and 31, CLEVR compiles in 0.84s against 1.5s,
and the whole test suite runs in 89s against 128s. Twenty-five small programs
grow by up to 18% — the tuple ceremony against a small loop — which is the
intended trade: bytes for a halved loop.

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
otherwise). It records how many leaf resolutions the *compiled* evaluation
actually traverses, anchored on one rule: **every terminal leaf counts 1,
deterministic or random** — a distribution primitive, or a
deterministically-known value compared against the sample, whichever AST
constructor spells it (`Constant`, `ThetaI`, a bound `Var`, a deterministic
`Apply`, an `InjF` with no probabilistic parameter). Only results that
resolve to no value at all — closures and lambdas — count 0. Combinators
add nothing for the act of dispatching: an `IfThenElse` is the sum of its
two arms' counts (no term for the condition), an enum-sum is the sum over
its enumerated values, and a call forwards the callee's own count
unmodified, so a recursive program's count is its traversed recursion
depth. An arm whose condition has probability exactly zero contributes 0
and — via `IRIf`, not a strict multiply — is never evaluated; that
short-circuit is what makes a recursive program's branch count terminate.
A pruned `topK` branch likewise contributes 0.

`bc` measures the compiled artifact's leaf-evaluation cost, not an
invariant of the distribution: it is stable under respelling the same leaf
(`x` vs `x+0.0`), but not under rewrites that change the number of explicit
branch points — `Uniform < 0.5` gives 1 while the extensionally identical
`if Uniform < 0.5 then True else False` gives 2, because the latter really
does compile to two leaf indicators.

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
| After Tensor Lowering | Enum sums rewritten to `map`/`reduce` over a tensor |
| After Select Pass | `IRIf` → `IRSelect` retagging (a no-op unless `--batched`) |
| After Optimization | Pseudo-code IR after constant folding, CSE, let-in optimization |

Use this to identify which stage introduced a defect when a program
compiles incorrectly. `IRCompiler` selects the inference algorithm per
node directly from the `pType`/`DiscreteValues` annotations visible after
Modality Inference.

### Enumerability across a function call

`SPLL.Analysis.annotateEnumsProg` derives a node's `DiscreteValues` tag from
its shape (`Constant`, `InjF` via `propagateValues`, `IfThenElse` as the union
of its arms). An arrow-typed function cannot carry one fixed tag in the
environment -- what its result enumerates over depends on what its argument
enumerates over -- so `applyTags` computes the tag **per call site**: it
resolves the application's head to a lambda (a literal one, or a top-level
function looked up in the raw function environment), binds the argument's tags
to the parameter, and re-annotates the callee's body under that environment.
`f x ++ f y` then selects the same enumerate clause the hand-inlined body does.
The directly-applied-lambda (`let`) case likewise binds the parameter before
annotating the body, so a `let`-bound enumerable is visible inside it.

Three refusals, each answering "no tag" -- the status quo before this existed:

- **Curried spines of two or more arguments.** In `f a b`, `a` sits where
  IRCompiler's enumerate path cannot reach it: `enumerateAppliedLambda`
  marginalises the argument of the single `Apply` node it is handed, and the
  partial application `f a` is not even tagged `IsConditional` (only `Var` and
  `Lambda` nodes are). Deciding it per argument position would need `pType`,
  and **this pass runs before ModalityInfer, so every `pType` still reads
  `NotSetYet` here** -- `rType` is available, `pType` is not.
- **Recursion.** A function already being looked through is refused; unrolling
  has no termination story and the enclosing tag fixpoint would not converge.
- **An empty propagated domain.** No values at all is an *absence* of a domain,
  not an empty one; tagging it would make downstream inference sum over nothing
  and report probability zero.

Enumerating an ADT domain through a **field accessor or constructor test** is
partial -- `b1` has nothing to say about an `A`, and `implicitFunctionImpl`
answers that with an `error`, not a `Left`. `propagateValues` asks
`implicitFunctionApplicable` first and drops the tuples the function is
undefined on, so an accessor's enumerated domain is its own constructor's
values rather than a compiler crash. Before applied helpers were tagged, a
multi-constructor domain never reached an accessor at compile time.

Corpus: `applyEnum*` (the four shapes plus the no-application control) and
`clevrEqualLargeMetalSphereSplit` (one neural read per object, contributions
summed through a shared helper -- the split sibling of
`clevrEqualLargeMetalSphereNatural`, which reads the whole scene at once).

A **non-conditional** helper (`bump x = x ++ 1`, no `if`) now compiles where it
used to be rejected, but its emitted probability function is generate-backed
and therefore not a probability function at all -- a pre-existing defect
reachable at HEAD by `bump coin ++ 1`, tracked by the docs-repo investigation
`generate-backed-inference-sweep`, not by the tag.

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

### AutoNeural naming: `readLogits` / `writeLogits`

Two independent directions live in `SPLL.AutoNeural`, and both are named for
the data flow rather than for "encode"/"decode" — those words used to collide
(both nominally "produce logits"), which made the actual opposite pair
(reading a logit vector vs. writing one) unreadable from the names alone.

- **`readLogits`** (`makeReadLogitsFunGroup`, `neuralReadLogitsSuffix =
  "_auto"`): a neural declaration `name :: Symbol -> target` forward-declares
  a network (NN1) whose logit-vector output SPLL *reads* into a
  value/distribution. Emits the `<name>_auto` group's `gen`/`prob` readers;
  it never hosts a `writeLogits` function itself.
- **`writeLogits`** (`makeWriteLogits`, `makeTopLevelWriteLogitsFun`,
  `IRFunGroup`'s `writeLogitsFun` field, generated as a `_writeLogits`
  suffix / `writeLogits` Python method): the compiler-generated inverse —
  it derives a logit vector from a value-producing SPLL function's own
  compiled `_prob`/`_normal` functions, for a hypothetical downstream
  network (NN2). Built per function endpoint (task
  `encode-per-function-endpoints`), not per neural declaration.
- The registry keyword is `neural writeLogits :: T of M`
  (`SPLL.Lang.Types.writeLogitsDecls`), and the `.tst` probes are
  `writeLogits_len`/`writeLogits_at` (`TestCaseParser`).
- A third, historical direction (`source -> Symbol`, once called "Encoder")
  named an external network with no SPLL call site; it has been removed and
  is rejected at validation (`SPLL.Validator.validateNeuralShape`).

## Test Structure

The suite runs under tasty (`tasty-quickcheck` for properties, `tasty-hunit`
for unit tests). Each module exports a `TestTree` which `Spec.hs` assembles
into the top-level groups (`--ta '-l'` prints the current list):

- `test/Spec.hs` — main entry, the static `Spec` properties, and the
  `Corpus` group of metamorphic properties generated from `testCases/`
  (validation, sampling-vs-PDF, topK, branch counting, P(ANY)=1, log-space
  vs linear, and `-O0` vs the default `-O2` — the optimizer is a rewrite, so
  the two levels must agree exactly on every corpus query point; a `.tst`
  expectation alone would not have caught a dangling chain-name reference that
  constant folding happened to delete)
- `test/TestParser.hs` / `TestInternals.hs` — parser and internal-function
  unit tests
- `test/TestRejection.hs` — unhappy-path: invalid or ill-typed programs must
  be rejected with the expected reason
- `test/TestModality.hs` / `TestModalityInfer.hs` — the capability lattice
  and its projection; hand-verified modalities the engine must pin
- `test/TestDeterminism.hs` — the forward determinism dataflow and its
  call-graph fixpoint
- `test/TestWriteLogitsProperties.hs` — AutoNeural writeLogits, plus corpus-driven
  writeLogits/readLogits roundtrip checks on slot layout and semantics
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
`cdf(...)` expectation has two shapes (`TestCaseParser.Expectation`):

- **`p(x) = (prob, dim)`** or **`p(x) = (prob, dim, imposs)`** — an ordinary
  point. `prob` and `dim` are *both always checked*, by all three scalar
  backends and the interpreter, unconditionally — there is no "probability
  happened to compute to zero so skip the dim check" special case. The
  optional third component is the expected impossibility flag, checked when
  present; omitting it (most pre-existing corpus lines) means "don't check
  the flag". The corpus rows that pin it target its *structural* semantics
  rather than a zero test — notably `normal p(40.0)`, a 40-sigma tail whose
  density underflows to a hard `0.0` while `imposs` must stay `False` and
  `dim` must still state the true `1.0` (it's on-support, just a tiny
  density — dim is meaningful there and is checked like any other row).

- **`p(x) is impossible`** / **`cdf(x) is impossible`** — the dedicated
  shape for a genuinely impossible query point (wrong `Either` arm,
  off-support sample, unmatched indicator, ...). At such a point the dim has
  no fact of the matter (a hard zero is neither a density nor a mass), so
  none is stated or checked; `prob` is asserted `0` and `imposs` is asserted
  `True`, both unconditionally. This is the *only* way to spell a
  zero-probability, impossible point — `TestCaseParser.pTupleExpectation`
  refuses a `(0.0, dim, True)` tuple outright (a hard parse-time error naming
  the file and line), so a `.tst` author can never write a numeric dim that
  silently goes unchecked. Task `tst-dim-unasserted-at-zero-probability`
  closed that gap: an earlier, purely-documentary pass over this same task
  (corpus sweep + a note, no grammar change) was reopened and redone
  properly once a human review pointed out it left the structural hole open;
  the whole corpus was swept mechanically at the time (25 files' worth of
  `(0.0, dim, True)` rows rewritten to `is impossible`) and every remaining
  zero-probability `(prob, dim)` row was verified against the interpreter
  under the new unconditional dim check.

A zero-probability point that is *not* impossible (the rare on-support
underflow case, `normal p(40.0)`-style) still uses the ordinary tuple shape
with an explicit `imposs = False` third component — omitting the third
component on a zero-probability tuple row is legal (means "don't check the
flag") but unusual, since such a row is exactly the case where stating and
checking `imposs` is most informative.

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

A *scalar* `compile` run at `-v` closes with a batched-eligibility advisory
(`SPLL.Prelude.batchedRefusal`, reported by `app/Main.hs`), so you can see
whether `--batched` would take a program without flipping the flag and
reading a refusal. It re-runs the pipeline in batched mode, which is why it
is behind `-v` rather than on by default, and it names the **first**
offending construct only — fixing that one may reveal more behind it. Its
verdict is pinned against the backend's own refusals by the
`BatchedRefusal` test group.

### Emitting float literals

Haskell's `show` renders the non-finite doubles as `Infinity`, `-Infinity` and
`NaN`. **None of those is a Python name, and `-Infinity` is not Julia syntax**,
so a backend that `show`s a `VFloat` straight into its output emits code that
dies with a `NameError` at run time instead of failing the compile. Log space
reaches this constantly — its zero is `-1/0` (`Semiring.negInfIR`), so every
impossible arm of a `--logSpace` program carried one.

All four value renderers therefore go through a per-language helper —
`pyDouble` (`float('inf')`/`float('-inf')`/`float('nan')`, needing no import),
shared by `CodeGenPyTorch`'s `pyVal` and `CodeGenPyTorchBatched`'s `batchedVal`
and `domainVal`, and `juliaDouble` (`Inf`/`-Inf`/`NaN`) for `juliaVal`. Adding a
new site that emits a `Double` means routing it through one of those.

This survived 1507 tests because the corpus's log-space properties compare
against the **interpreter**, which never renders a literal.
`Spec.prop_LogSpace{Python,Julia}RendersInfinity` are the only tests putting a
log-space compile through a text backend, and each asserts both halves — no
bare `Infinity`, *and* the mapped literal present — so neither can go vacuous.

### Unary math must not raise where the interpreter answers

The interpreter is the reference semantics, so a backend's unary math has to be
IEEE-conforming the way Haskell's is: `exp` **saturates** to `inf` past the
representable range, `log 0` is `-inf`, and `log` of a negative is `NaN`.
CPython's `math` module *raises* on all three (`OverflowError` /
`ValueError`), and Julia's `log` throws `DomainError` on a negative.

That is reachable, not hypothetical. An `InjF` inverse's monotonicity-direction
guard evaluates the inverse derivative **eagerly** just to read its sign, so
`cdf(1000.0)` on `main = log Uniform` emitted `math.exp(1000.0) > 0.0` and took
the whole query down with an `OverflowError` before any branch was chosen — a
crash rather than a wrong number, and one nothing in the corpus caught, because
`exp`'s forward `applicability` is unconditionally `True` and so no guard
stands between a large query and the eager call.

`OpExp`/`OpLog` therefore route through `safe_exp`/`safe_log` in `pythonLib.py`
and `safe_log` in `juliaLib.jl` rather than the raw stdlib name
(`CodeGenPyTorch.pyUnaryOps`, `CodeGenJulia.juliaUnaryOps`). Julia needs no
`safe_exp` — its `exp` already saturates. The batched backend was already right
by construction (`torch.exp` saturates, and `safe_log` in `pythonLibBatched.py`
exists for a different reason: gradient safety under `torch.where`, which
evaluates both arms).

`log` is *currently* safe on every reachable path anyway, because each of its
call sites happens to sit behind an inverse's `applicability` guard — but that
is a property of today's set of `InjF` inverses, not an enforced invariant, so
it is wrapped too. Pinned by `testCases/uniformLog.tst`'s `cdf(1000.0)` row and
`testCases/multExp.tst`'s `cdf(-5.0)`.

## Runtime Libraries

Generated Python code depends on `pythonLib.py` (scalar) or
`pythonLibBatched.py` (batched mode, see above); generated Julia code
depends on `juliaLib.jl`. These provide runtime helpers for the transpiled
inference functions.
