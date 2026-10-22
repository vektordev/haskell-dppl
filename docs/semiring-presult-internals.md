# `PResult` combinators and the `Semiring`

## Combinator vocabulary

`PResult` values are built from a small combinator vocabulary in
`SPLL.Semiring` rather than hand-written per case: leaves are
`density`/`mass`/`detP`, `prodP` is independent conjunction, branches mix
via `mixP`/`mixSubP`, enumeration sums via `enumSumP`, and the
change-of-variables correction (`scaleCoV`) reads the result's own dim so
call sites never name it. `shareResult` binds a sub-result's floated
let-in block once and projects fields off it instead of re-wrapping the
block per field — the difference between linear and geometric IR growth as
nesting deepens; the zero-probability guard must still sit on the bound
value rather than each projection, or a recursive call the guard exists to
skip can run anyway (`dice` stops terminating).

A dim counts dimensions, so it is an `Int` in the IR (`dim0`/`dim1`, never
`const0`/`const1`, which are the float probability constants) and on every
backend: a Python `int`, a Julia `Int`, a torch `int64` tensor batched.
`VProbDim` matches only a `VInt` dim, so a stray float dim fails at its
consumer instead of comparing unequal (task `presult-dim-as-int`).

`enumSumP` reports a **mass**: dim 0, flag derived from the summed value.
That is only right when every enumerated term is one. `enumMixP` is the
enumerated *mixture* of a scalar real value: each term keeps its own dim and
flag, and the fold follows `mixWith`'s rule (impossible terms dropped, a
possible atom outvotes any density, equal dims sum). It decides "lowest dim"
by an `ROpAdd` count of possible dim-0 terms rather than a max/min reduction,
because the batched backend refuses `ROpMax`; that is sufficient only because
a scalar's dim is 0 or 1. Its caller is the mixed enumerate-and-shift/scale
rule (over the operand's values, or over its draws' cells via
`IRCompiler.latentCellSum`, `docs/enumeration.md`), whose "continuous" operand is known only to be a `Float` -- it may be a
plan-answered discrete count or an atom/density mixture (task
plan-sum-with-sunk-discrete-draw-reports-density; corpus
`plan-enumeration/planSumWithSunkDiscreteDraw`,
`arithmetic/plusEnumMixedAtomDensity`).

`rProb` is a newtype `P` that only `SPLL.Semiring` can construct, so
`IRCompiler.hs` must route probabilities through a Semiring-aware
combinator or one of two escape hatches: `unsafeLinearP` (a deliberately
linear-only subsystem — no call site uses it today) or `sealP` (bespoke
`PResult`s assembled from already-trusted values). Grepping `unsafeLinearP`
is the "which subsystems ignore `logSpace`" audit.

## Log-space probabilities

`logSpace :: Bool` in `CompilerConfig` (CLI `--logSpace`) computes
probabilities as **logs** so deep tails and long products don't underflow.
The `PResult` combinators read their operators off a single `Semiring`
record that `semiringOf` derives from the `CompilerConfig` (log-sum-exp
instead of `+`, `-inf` instead of `0`); since the config is fixed for a
compile, so is the semiring. `topK` pruning's accumulator and cutoff are
semiring-aware too. Two consequences worth internalising before touching
`toIRInference`:

- **Never hand-write a linear identity on a probability.** The complement
  of a probability is `srComplement`, not `IROp OpSub const1` — under log
  space the latter is silently a different number. A zero test is
  `srZero sr`, not the literal `0.0`, and log space compares against
  `-inf` with exact `OpEq` rather than `OpApprox`, because
  `(-inf) - (-inf)` is `NaN`.
- **A complement keeps a normal tail's precision only if it can see the
  leaf.** Every instance's `srComplement` is `upperTailComplement`: the
  complement of a standard-normal CDF leaf, looking through `IRIf` arms and
  `IRLetIn` bodies, is the same leaf at `-z` (`1 - Phi(z) = Phi(-z)`, and
  `log(1 - exp(log Phi(z))) = log Phi(-z)`), which the runtimes compute
  through `erfc` without cancelling. Anything else, a let-bound `IRVar`
  included, gets the plain `1 - x`, which keeps only about `1e-16 / P` of
  relative precision on a tail of size `P`. So complement the expression
  rather than a variable bound to it, and where a site picks between a CDF
  and its complement on a runtime condition (the `gt`/`lt` comparisons), use
  `complementWhen sr cond x`, which pushes the choice into the leaf's
  argument rather than binding `x` (task
  `cumulative-normal-upper-tail-cancellation`). End2End's
  `normal upper-tail precision` group checks this to 1e-12 relative on
  every backend, which the corpus's 1e-4 absolute tolerance cannot.
- **The read-logits reader is semiring-aware too.** The `ReadNN`/AutoNeural
  network's inference function (`<nn>_auto`, `AutoNeural.makeProb`) builds its
  answer from `fromLinearSR` (a softmax slot), `scaledNormalDensity` (a
  Gaussian slot pair), `srTimes`, `srComplement` (the Either right flag) and
  `sumAllSR` (constructor alternatives), so under `logSpace` it answers a log
  like every other producer, and its linear form is the arithmetic it always
  emitted (task `read-logits-network-linear-under-logspace`). Neural programs
  are outside `Corpus.LogSpaceMatchesLinear`'s pool; End2End's
  `PlanEngineLogSpaceMatchesLinear` (budget 0, the plan engine) and
  `NeuralLogSpaceMatchesLinear` (default budget, dense enumeration through
  `_auto`) check them instead. Branch *counts* stay linear everywhere.
- **A linear quantity with no native log leaf** — a sum of softmax slot
  probabilities, a `|change-of-variables|` factor — enters the semiring
  through `fromLinearSR`. A CDF difference is `measureDiffSR`, not `srMinus`:
  `srMinus` is the AnyExcept operator, undefined under max-product, while an
  interval's mass is an integral in every family. Log space's difference is
  only defined for a non-empty interval, so test emptiness on the operands
  (the CDF is increasing), never on the difference. A sum of many
  alternatives outside `mixP` is `sumAllSR`, which let-binds operands and
  partial sums wherever `srPlus` reads its operands twice.

## Dimension Counting

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

An operand's `rType` being `Float` says nothing about its dim. The mixed
enumerate-and-shift/scale rule (one binary-`InjF` operand enumerable, the
other an untagged `Float`) used to stamp dim 1 on its sum, so a plan-answered
count plus a coin came out as a density. It now sums its terms with
`Semiring.enumMixP`, the enumerated form of the mixture rule above; see
`docs/semiring-presult-internals.md`.

## Impossibility flag

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

## Branch Counting

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

## One block for every field: `anySafeShared`

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
from folding. It is gated on `blockNests`, which has two halves:

- `blockIterates`: the block contains a **loop** (`BMapList`, `BMap`,
  `BReduce`) or a call (`IRApply`). That half is a claim about run time, not
  size — what makes a second copy cost anything is that it is a second
  traversal, and a block of constants and arithmetic folds to a few literals
  whether copied or not. A pre-optimization node count was tried first and is
  the wrong question: `test/cases/arithmetic/equalsCoin` builds ~100 nodes that
  fold to four literals, passing any size gate with nothing worth sharing.
- The block already holds a **copied field**: an `isAny`-guarded field whose
  else-arm is a let-block, which is what `anySafe` leaves behind when a level
  below declined to share (and what a shared level's binding looks like too).
  Without this half a leaf block's copies compound under nesting: each
  deconstructing level copies its child's copies into about three fields, and a
  right-nested accessor over a mixture of tuples grew its -O0 IR ~7x per level
  (task `structured-accessor-compile-blowup`, mechanism B). With it, one level of
  copying is still allowed — a shallow program keeps its folded output — and
  every level from the second on shares, so the IR grows linearly.

`IROptimizer.foldConstProjections` recovers most of the cost of the shared
tuple: a projection off a let-bound tuple whose every arm puts the same literal
at that position (the dim 0 or the `False` flag of both the `isAny` defaults and
the computed result) folds to that literal, so the tests reading it fold as they
did inline.

### The one rule: bind a non-atomic block

A `PResult` has four fields, and any construction that puts a non-atomic
expression into more than one of them copies it; when the expression holds a
sub-result built the same way, the copies multiply per nesting level. That is
the cause of most of this compiler's exponential compile times, and each was
introduced by a fix that looked local. So (task
`presult-unbound-block-copied-per-field`):

- `unpackResult` takes a `Varname`. A block is bound first (`mkVariable` +
  `setVariables`, a `WFactor`'s bindings, or `shareResult`) and the variable
  unpacked. `packedProb` reads just the probability off a packed expression,
  one read.
- A sub-result's floated bindings are re-attached through `shareResult` (bound
  once under guards), `guardedResult` (`guardP` semantics, the block inline in
  its one reader or bound once), or `shareUnlessLeaf` (the sanctioned
  exception: a leaf block, which holds no sub-result and so cannot compound, is
  copied inline into its readers, keeping its constants foldable). Never
  `mapResult (generateLetInExpr binds)`.
- World factors (`WFactor`) carry their block as a binding; `measureWorld` and
  `measurePlanWorlds` bind it under the world's guards. A factor that several
  worlds share is still emitted once per world (task
  `budget-zero-exponential-in-nested-enum-ifs` owns grouping them).

Measured over the 751 corpus programs that compile in 60 s (Python, haskell-dppl
`5776efa` against this change): -O0 output 54.9 MB → 35.5 MB, -O2 output
13.72 MB → 13.09 MB (−4.7%). Sharing every Any-safe block at two readers instead
of using the nesting test came out about 1% larger at -O2.

Measured over the corpus: emitted scalar Python totals 68% of its former size
(`clevrEqualLargeMetalSphere*` 2.8x smaller, the `mNistAdd` family 1.6–1.8x),
`mNistAdd4`'s probability function goes from two enumeration passes and 62
neural-forward call sites to one and 31, CLEVR compiles in 0.84s against 1.5s,
and the whole test suite runs in 89s against 128s. Twenty-five small programs
grow by up to 18% — the tuple ceremony against a small loop — which is the
intended trade: bytes for a halved loop.

## topK Branch Pruning

`topKThreshold :: Maybe Double` in `CompilerConfig` enables
probability-based branch pruning. The compiler threads an `accProb` (the
probability of reaching the current point) through inference; each
`IfThenElse` arm is guarded on its *accumulated* path probability
(`accProb * p_cond`) against the cutoff, and an arm below the cutoff is
dropped. The same threshold filters enumerable `InjF` branches by
`accProb * p_left`.

The cutoff is a **runtime parameter**, not a compile-time constant: under
topK every `_prob` function takes `(sample, acc_prob, top_k_cutoff, ...)` and
every `_integ` function `(sample, top_k_cutoff, ...)`, and calls between
definitions forward it. Every guard is emitted and decided at run time, so
one compile answers any threshold. The threshold given to `topKThreshold` only
becomes the emitted `TOP_K_CUTOFF` constant, the default a caller passes.
`SPLL.Prelude`'s `run*` entry points pass the env's `TOP_K_CUTOFF`, and
`withTopKCutoff t` re-thresholds a compiled `IREnv` without recompiling it.
Like `acc_prob` (seeded with `ACC_PROB_INIT`), the cutoff is in the
semiring's space: a log-space compile takes `log t`. There is no
static-threshold mode that removes pruned branches at compile time (task
runtime-parametric-topk-threshold).

Pruning is **lossy** — a dropped branch's mass is simply gone. Hence the
one-sided invariants: topK never *inflates* a probability
(`Corpus.TopKNeverInflates`, its CDF twin `Corpus.TopKNeverInflatesCdf`, and
the fuzz invariant `TopKNeverInflates` in
`prop_Fuzz_SharedDrawConfigInvariants`), and only threshold 0 is
exact (`Corpus.TopKZeroThreshMatchesExact`).

"Never inflates" holds only at equal dimension. Pruning removes alternatives
from a mixture, and the mixture reports the *lowest* dim among the
alternatives it still has, so the pruned dim can only rise — and a pruned
point mass can leave a sibling density behind
(`test/cases/topk-pruning/topKPrunesMassArm`: exact `(0.05, dim 0)` at `1.0`, pruned
`(0.95, dim 1)`). A mass and a density are not comparable, so the properties
compare values at equal dim and otherwise require the pruned dim to be the
higher one.

What is dropped depends on **operand order**. An enumerated InjF `l (+) r`
guards each term on `accProb * p(l = e)` and never on `p(r = …)`, and `accProb`
changes only at an `if`, so a commutative swap changes what is pruned. In
`test/cases/topk-pruning/topKOperandOrder`, `(x + y) + z` over three
Bernoulli(0.3) bits answers `p(3) = 0` at threshold 0.1 (`p(x + y = 2) = 0.09`),
while `z + (x + y)` keeps the exact `0.027`. `Corpus.TopKOperandOrder` (Slow)
checks every commutative site of the corpus. No other corpus program diverges
(task `topk-prunes-on-left-operand-marginal-only`).

The guard must not make that loop **eager**. Topk-off, `p(l = e)` is read
once, inside the cell's `isPossible` arm, and the optimizer inlines it there,
so a cell whose inverted value is outside `r`'s domain never descends into `l`.
The cutoff test reads it a second time, so under topK it is let-bound behind
that same `isPossible` guard (zero elsewhere, where the conjoined cutoff test
ignores it). Bound in front of the guard, every cell descended into `l`, and a
left-nested chain such as a scene count paid the product of its split domains:
p(0) on a 7-slot count took 34 s against 0.1 s topK-off (task
`topk-compiled-scene-count-query-exponential-in-slots`, pinned by
`Internals.wideProductSceneTopKQueryPolynomial`).

## A pruned probability is a lower bound — and complements are not

A pruned result is a **lower bound** on the exact one, and lower bounds
compose under products, sums and the lowest-dim-wins mixture — but not under a
complement or a subtraction: `1 − lower` and `a − lower` are *upper* bounds.
`IRCompiler.unpruned` (accumulated probability seeded with `∞`, which fails
every "below cutoff" test in both semirings and crosses a call boundary as a
plain argument) therefore compiles the operand of every such site with pruning
off, and any new `srComplement`/`srMinus`/CDF-difference site must do the
same:

- an `IfThenElse` *condition* (its False-weight is the complement of its
  True-probability — `test/cases/topk-pruning/topKComplementCondition`, the minimized shape
  of the fuzz counterexample this was found by: a condition that is itself an
  `if` had its True-probability pruned to `0`, so its else-weight became `1`);
- the integral behind a `gt`/`lt` against a deterministic bound
  (`topKComplementBound`);
- both operands of the `AnyExcept` subtraction `p(ANY) − p(v)`
  (`topKComplementAnyExcept`; a pruned marginal could even go negative);
- an inverted operand in cumulative mode whose transform is not statically
  increasing, since `scaleCoV` then flips its CDF through a complement
  (`topKComplementCdfFlip`; `covOperandMeta`/`staticallyIncreasing` — `plus`
  declares a literal `1` and stays pruned, `neg`'s `-1` and `mult`'s runtime
  `1/a` do not);
- both bounds of a set-witness interval measure (`cdfAtBound`).

The alternative — inferring a condition at both polarities, each pruned — was
rejected: it is the O(2^d) double compile the `IfThenElse` case retreated from,
and it would not have helped the subtraction sites anyway.

Separately, an `_integ` function takes no `acc_prob` parameter, so a
cumulative-mode call into another definition passes only the sample and the
cutoff (`inferenceCall`); passing the accumulator there applied the callee's
result tuple to an extra argument, and every topK CDF query through a call
crashed with "Expression is not a closure" until `TopKNeverInflatesCdf`
reached `varAlias`.

## Query-Type Guard

`checkQueryType :: Bool` (default `True`, CLI opt-out `--noTypeCheck`)
wraps every prob/integ function root in a guard checking the query value
structurally conforms to the program's return type (`IRConformsTo`,
consumed by the three scalar backends; batched mode strips the root guard
instead) — without it, a wrong-typed query either silently returns a bogus
number or hits a deep panic. The marginal wildcard (`VAny`) is accepted at
every level so marginal queries aren't penalized.
