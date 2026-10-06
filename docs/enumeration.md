# Enumeration, materialization and tensors

Discrete enumeration in IRCompiler: what gets enumerated, how its cost is bounded, and the tensor IR it is built in.

## Enumerated branches are compiled forward, and that premise is checked

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

`requireDeterministicUnderEnum` checks each generated operand and refuses at
compile time, naming the generator it would have called — matching the sibling
witness-construction failures, which fail loudly. Since task
`enum-let-latent-gates-fresh-draw` it refuses **only a draw through a function
on a call cycle** (`CompilerMetadata.cyclicGenNames`, over-approximated like
`ModalityInfer.summaries`'s call graph, so any recursive callee counts, not just
one reaching back into the function being compiled). Every other fresh draw
under an enumeration — a primitive, a neural read, a call into a non-recursive
helper — is handed by `forwardOrInfer` to `toIRInference` with the enclosing
enumerated variables retyped `Deterministic` (`reinferRecovered` over
`recoveredVars`), the same step the over-budget nested application already
took. That fixed the false refusal of the canonical noisy observation of a
shared latent, `draw b = Uniform < 0.5 in (b, if b then Uniform < 0.9 else
Uniform < 0.1)` (`test/cases/let-bindings/enumLetGatesFreshDraw*`), plus three
fuzz-found known issues now in the corpus (`enumNeuralBoolGatesFreshDraw`,
`enumNeuralDeadBranchFreshDraw`, `enumDeadLetFreshDrawTuple`).

Delegation has one catch: every enumerated sum (`enumSumP`) reports a **mass**
(dim 0), which was true while enumerated bodies were always forward-and-compare
indicators, and a delegated body can be a density. Whether it is one is a
*runtime* fact (`(x, Uniform)` is a mass exactly when the query puts `ANY` in
the second slot; topK makes the dim a runtime choice too), so the delegated
probability is guarded at run time — a possible result with a non-zero dim
raises "met a continuous density" rather than being summed as a mass. The guard
is omitted for a cumulative result and for a result type with no `Float` leaf
(which is what keeps a helper call guard-free: its dim is a runtime projection),
and folds away where the dim is a literal 0. A real density sum is the
follow-up `enumerated-sum-over-density-body`, pinned by
`known-issues/enumLetGatesFreshDensity`. Solving the fixed point
algebraically (the marginal *is* closed-form for that program) was declined: it
would make "does my program infer?" unpredictable from the source. The refusal
is an absent probability/integrate variant with a recorded reason (see "A
static refusal is an absent variant" in `modality-and-admission.md`), so `generate` still works.

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

## Enumerability across a function call

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

A **curried spine** `f a b` is tagged the same way, binding every argument to
its parameter (task `shared-enumerated-latent-loses-per-slot-factorization`).
It used to be refused, because **this pass runs before ModalityInfer, so every
`pType` still reads `NotSetYet` here** and it cannot tell which argument is
random. IRCompiler decides that instead: a conditional top-level function
applied to arguments that are all deterministic -- once the enclosing
enumerated latents are fixed (`reinferRecovered` over `recoveredVars`) -- except
a random enumerable *last* one is compiled by `enumerateCurriedArgument`, which
loops over that argument's domain exactly as `enumerateAppliedLambda` loops
over a `let`'s. A random *leading* argument declines there and keeps its old
path; and `enumerateAppliedLambda` measures its bound value with the enclosing
latents fixed, which is what `draw v = contrib u 1` (u enumerated outside,
`sharedLatentNestedLet`) needs once `contrib u 1` carries a tag. Before, even
`match Red (readC s)` had no probability path ("set-valued witness
construction failed"), while `match (readC s)` did. Corpus:
`curriedHelperEnumArg`, `sharedLatentPerSlot`.

Two refusals remain, each answering "no tag":

- **Recursion.** A function already being looked through is refused; unrolling
  has no termination story and the enclosing tag fixpoint would not converge.
- **An empty propagated domain.** No values at all is an *absence* of a domain,
  not an empty one; tagging it would make downstream inference sum over nothing
  and report probability zero.

The recursion refusal is decided **from shape before any value is forced**
(`definitelyUntagged`, task `plan-fold-mutual-recursion-blowup`). Knowing
whether an `InjF` is tagged otherwise costs its whole propagation, and a fold
written as mutual recursion (`evenSum`/`oddSum`) only meets its refused call
one look-through deeper, after `evenSum`'s body has propagated `rest` over the
entire `of` domain. That cost 2.5x the allocation and OOM-ed at barcode depth 7
for a verdict of "untagged". `InjF`/`IfThenElse` now check whether any operand
provably gets no tag, mirroring `discretesTags`/`applyTags` without reading
tags, and short-circuit to `Nothing`. The computed tags are unchanged, and all
425 corpus programs emit byte-identical Python. Pinned by `Internals`'
`enum annotation refutes a recursive fold without forcing its argument` (the
order, with a poisoned argument, plus corpus-wide soundness of the shape
check).

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

## Stacked draws are sunk into their operands

IRCompiler enumerates a `draw`-bound discrete variable over the whole body of
its binding, so stacked draws enumerate as their **joint**, even where the body
factorizes. The CLEVR "exist with a predicate input" shape --
`draw c = readQ q in draw o1 = readAttrs s1 in ... in (match c o1) ++ ...` --
nested loops over `c` and every `o_i`, `8 * 97^N` terms, and did not finish one
call at three slots.

`SPLL.DrawSinking` (between enum annotation and forward chaining, since it needs
the `DiscreteValues` tags; a rewritten program is annotated again) moves each
enumerable, possibly-random `draw` down to the one `InjF` operand that reads
it: past directly nested bindings that don't read it, and into an operand when
some *other* operand may be random. That leaves `draw c` around
`(draw o1 = .. in match c o1) ++ ...`, which is the per-slot form. Sound for
eager draws: the binding is still evaluated at most once and every use of the
name stays under it; nothing is ever moved under a non-binding `Lambda`, into an
`if` arm, or into a function argument. A binding that ends up as `draw x = e in
x` is replaced by `e`. A binding read only by the *value* of a directly nested
binding (`draw x = e in draw y = v2 in b`, `b` not reading `x`) moves into `v2`.

**Product reads are split per field first** (task
`draw-product-read-enumerated-jointly`). `draw t = see img in Face (tells ..
(x0 t)) .. (tells .. (xJ t))` with `see` a neural read of a single-constructor
ADT is a product over its fields (AutoNeural's `ADTPlan`, one logit block per
field, no flag), so when the body reads `t` only through field accessors of
discrete fields, `splitProductDraw` rewrites it to `draw t_x0 = x0 (see img) in
.. draw t_xJ = xJ (see img) in ..` (a non-variable read argument is bound once
first) and the per-field draws then sink: `2J` terms instead of `2^J`, which
was refused past the dense budget at `J = 14`. A field read by several
operands keeps one shared draw above them. Not split: multi-constructor reads
(the constructor couples the fields), bodies using `t` whole (`isFace t`), and
reads none of whose per-field draws would then reach an operand of its own
(nothing to gain, and the plan engine's accessor descent handles the single
draw: `planEnumInlineADT` at budget 0). Each field's read calls the network
again, as the `define` spelling always has: `J` calls per evaluation instead of
one (follow-up `repeated-neural-read-not-shared`). Pinned by
`Internals.drawProductReadFactorizesPerField` (cost),
`Internals.productReadSplitConditions` (each condition) and the
`neural/drawProductRead*` / `drawMultiConstructorReadStaysJoint` corpus pairs.

The per-slot chain is then tabulated by Tier 0 materialization *inside* the
loop over `c`, which needed its decomposability gate to be retaken given the
enclosing enumerated bindings (`sharesLatentGiven` over
`materializationScopes`, fed by `CompilerMetadata.fixedLatents`): the summands
share `c`, but not once `c` holds one value. Measured at ten CLEVR slots
(97-value reads, 8 colours, 256 rows, scalar emitted Python with a
feature-major oracle): an `exist` query costs 0.37s against the
fixed-predicate program's 0.055s, i.e. 8 colours at ~0.8x the per-predicate
cost each; the full count distribution 92s against 21s. Values agree with a
Poisson-binomial reference to 2e-15. Corpus: `sharedLatentPerSlotHoisted`;
structural test `Internals.sharedLatentFactorizesPerSlot` (loop-chain cost
against the fixed-predicate program at 3 and 6 slots).

The programs this moves in the corpus are `letTwoEnumerable`,
`sharedLatent{PlusFresh,OneSideOnly,NestedChain,NestedLet}`,
`enumLetGatesFreshDrawNested` and `listConsDeconstruction`; the
decomposability canaries still keep a shared latent around the operands that
share it, since a binding read by two operands never moves into either.

## Marginal Materialization

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
  (`test/cases/let-bindings/letThreadEnumerable` is the canary,
  `test/cases/let-bindings/sharedLatentNestedChain` the nested one). Unlike
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
  differential tests' off-switch). The CLI flag `--materializationBudget N`
  sets it per invocation -- the explicit opt-in to dense enumeration of an
  over-budget `of` domain; there is no automatic dense fallback. Pinned
  through the real binary by `test/TestCLI.hs`.

A leaf cell holds a whole compiled sub-inference rather than a few
references, so it is the one place materialization multiplies IR instead
of rearranging it. `pointQueryTable` compiles the first value as a probe,
measures it, and declines the table unless the copy is small
(`maxTabulatedLeafNodes`) and the total fits the budget — a `ReadNN`
digit read is 10 IR nodes, while an arbitrary enumerable if-tree can be
thousands, where copying per value cost 14x the IR and turned a 0.17s
compile into 16s.

## The dense-enumeration budget gate

An enumerable application (`let x = <discrete draw> in body`, with a
`DiscreteValues` tag on the draw -- which every neural read with a wholly
discrete annotation carries, written or auto-derived) is enumerated densely by
`enumerateAppliedLambda`: the whole domain becomes one
`BTensor` literal. `enumerationWithinMaterializationBudget` refuses that above
`materializationCardinality`, at **both** sites that enumerate:
`toIRInference`'s enumerable-`Apply` equation (it declines and dispatch falls
through to `planWitnessApply`) and `toIREnumerate`'s nested twin (it hands the
inner application to `toIRInference`, since `toIREnumerate` has no plan path
of its own and its catch-all would refuse the random draw). Before the gate an
`of` annotation forced dense enumeration of a 21845-value scene (6-27MB
modules). Tasks `of-annotation-forces-dense-enumeration`,
`enumeration-budget-gate-misses-nested-application`.

The gate is a refusal to blow up and must be nothing else: its count,
`enumeratedCount`, is exactly the length of the list the loop would run over,
empty enumerations counting zero. (`multiValueCardinality` answers `Nothing` on
an empty enumeration, which made the gate decline and reroute a two-value
`right ..` domain.)

Inside an enumeration loop the bound variable holds one fixed value, so
`enumerateAppliedLambda` records it in `recoveredVars`, and `planWitnessApply`
re-types its re-fetched body with `reinferRecovered` (see "Recovered variables
are re-inferred" in `modality-and-admission.md`). Without that, an
over-budget inner application whose body reads the outer variable was refused
by the plan traversal as reading "an enclosing random binding".

**Dense first, everywhere.** Since every read is tagged, a neural domain
under the budget is enumerated densely whether or not an `of` was written,
and the plan engine is reached by default only above it. Measured on the 16
corpus programs this moved: 13 emit larger modules (up to 6.8x,
`planEnumRecWeightedCount` 44 KB -> 300 KB) and the 3 `planMultiReader*` smaller
(93 KB -> 35 KB); every value agrees. Accepted as a cost question, not a
correctness one. The plan engine keeps its small-domain coverage through
End2End's `PlanEngineMatchesDense` (budget 0 against the default compile at
every query point of every neural corpus program; `planEngineCorpus` lists the
programs that must answer there) and through the `*Polynomial` growth tests in
`TestInternals`, which compile at budget 0. Two of the moved programs,
`planEnumRecWeightedCount`/`planEnumRecAlternatingWeightCount`, cost ~13 s each
densely under the `-O0` interpreter and are `slow` for it (docs task
`dense-enumeration-cost-on-accumulator-folds`). Known gap: dense enumeration
evaluates the body at *every* domain value, so a helper that is partial on part
of the domain (reads `tl s` before testing `isEmpty s`) crashes at run time
where the plan engine drops that value's mass (`Internals`'
`planEnumStructuralPartial`, pinned at budget 0; docs task
`dense-enumeration-crashes-on-partial-body`).

**Known cost**: over budget, the plan traversal is the only route, so a body
it does not cover is refused (an absent probability variant; `generate`
survives) where dense enumeration used to compile it. Dense fallback was
explicitly rejected; the fix is plan coverage, and `--materializationBudget N`
is the explicit per-invocation opt-in to dense enumeration. Task
`plan-path-coverage-for-over-budget-bodies` closed the gaps first found here:
built-in constructors (`TCons`/`Cons`/`left`/`right`) and arithmetic at the
observed position, and inner deterministic `draw`s / local lambdas, which the
traversal beta-reduces when the argument is deterministic given the plan
(`planBetaReduce`).

**Value-grouping clash rule** (task `plan-flat-sum-over-product-exponential`).
The milestone-4 grouping (`planGroupValues`) bakes a value group's residual
leaf constraints into one summed mass, which double-counts if anything else
constrains those leaves again. The gate used to be a syntactic reader count
(`planReaderCount <= 1`): too strict for readers of *disjoint* slices (a flat
`g (o1 sc) + ... + g (oN sc)` over a product scene enumerated 3^N worlds and
OOM-ed at N = 8) and too lax for a helper reading its parameter twice
(`planHelperReadsPlanParamTwice`, a silent wrong number). Now a merged world
records the leaves it baked (`pwBaked`); `intersectPlanW`/`addSpecCons` set
`pwClash` when a baked leaf meets any other constraint or baked set;
`planWitnessApply` traverses with grouping on and, if a surviving world
clashed, discards that attempt (bindings via `pass`, name supply rewound) and
reruns with grouping off -- for a body the reader count already kept
ungrouped, byte-identical to what it emitted before.
So readers of the same leaves (`(numRed scene, numRed scene)`,
`draw n = numRed scene in (n, n)`) still enumerate one world per scene path and
are as large as the dense module (`planOverBudgetTuplePair`, 8.2MB; follow-up
`plan-multi-reader-value-grouping`), while disjoint readers group
(`planFlatSumOfTenSlots`, ~50KB; `Internals.planFlatSumOverProductPolynomial`).
Corpus: `planEnumRecCountOfLazy*`, `planOverBudget*`; structural test
`Internals.nestedEnumerationHonoursBudget`.

## Agreement fusion: two categoricals multiply in O(V)

Combining two categorical variables by **agreement** — `let a = camNN i in
let b = depthNN d in if a == b then right a else left ()` — is the
product-of-experts shape: the kept mass is `P_a(k)·P_b(k)` per class and
`Z = Σ_k P_a(k)·P_b(k)` is the fusion evidence. It compiled to a *joint*
enumeration, O(V²), evaluating the second expert's marginal V times per
outer value. Correct, and unusable at the vocabulary scale it exists for.

`IRCompiler.enumerateAgreement` rewrites the double sum into dense vector
algebra over the shared domain. Writing `T`/`E` for the two arms' masses
against the query and `Sb = Σ_k pb(k)`:

```
Σ_j pa(j) · Σ_k pb(k) · ( [j==k]·T(j) + [j≠k]·E(j) )
  = Σ_j pa(j)·pb(j)·T(j)          -- the diagonal: the elementwise product
  + Σ_j pa(j)·(Sb − pb(j))·E(j)   -- everything off it
```

Four `BMap`s build the `[V]` vectors, `BZip` (with the semiring's *own*
multiply — `OpMult` linear, `OpPlus` in log space, which is why `Semiring`
gained `srTimesOp` alongside `srReduceOp`) is the elementwise product, and
`BReduce` sums. Measured on emitted Python over two decades of domain size,
against the same source compiled the old way: V=10 0.028ms vs 0.305ms,
V=100 0.229ms vs 25.5ms, V=1000 2.20ms vs 2551ms — fused time grows 78x
across a 100x domain, the joint path 8366x. Bit-identical on the diagonal,
within 9e-16 on the complement.

The off-diagonal subtraction is **forced, not chosen**: any O(V) form of
"sum over everything but the diagonal" is the total minus the diagonal,
because summing those terms directly is the O(V²) being removed. It is
spelled with `srMinus` (so log space gets `logSubExpIR`) and loses precision
only as agreement approaches certainty — the same cancellation the
`AnyExcept` site already accepts.

Six refusals, each falling back to the ordinary enumeration so behaviour is
exactly as before:

- **branch counting** (`-c`) and **topK**. The fused artifact traverses
  fewer leaves, so its `bc` is legitimately not the enumerated path's, and
  topK's per-branch cutoff has no per-branch site to hang on. Refusing keeps
  every existing `-c`/topK number intact — and turns the corpus's own
  "branch counting doesn't change the probability" property into a
  differential test of fused against unfused, which is how the fusion is
  covered at every corpus query point rather than only where a `.tst` says so.
- **the max-product semiring**, whose `srMinus` is `mapHasNoExcept` for the
  same reason the algebra above is sum-product-only.
- **an arm that reads the inner variable**, where the off-diagonal sum does
  not factor and no O(V) form exists.
- **unequal domains**, a shape error for the product.
- **operands that may share an enumerated latent** — the correctness gate,
  and the only one whose failure would be a silent wrong number. Answered by
  `latentVerdicts`, the decomposability analysis (design
  `materialize-discrete-marginals`) which until now had *no consumer*: it is
  keyed by binary-`InjF` chain name and the agreement condition `a == b` is
  a binary `InjF`, so the scope-correct verdict for exactly these two
  operands is already computed. Canary: `test/cases/neural/agreementSharedLatent`.

Corpus: `categoricalProductFusion` (hand-derived posteriors, non-uniform on
both operands, including the zero-product impossibility rows),
`agreementSharedLatent` (the refusal), and the pre-existing
`showcase_poe_discrete`/`observeDiscretePoE`, whose pinned values are
unchanged by the rewrite. Structural coverage is
`TestInternals.agreementFusesToElementwiseProduct`, which asserts the fused
body has no reduction inside a loop body while the same source under `-c`
does — a shape assertion rather than a wall-clock one, since the timing
belongs in `benchmarks/stressAgreementProduct.ppl`.

**Not yet fused**: a *conjunction* of agreements, `if (v == c) && (v == d)`,
which is how `showcase_poe_with_prior` and `showcase_poe_three_sensors`
spell three-way fusion. Those stay O(V²)/O(V³).

## Tensors in the IR

`IRBuiltin Builtin [IRExpr]` carries five operations over a **tensor** — a
statically-shaped, flat, homogeneous block of values (`VTensor Shape [Value]`,
row-major, outermost axis first), as against `VList`'s cons spine:

| builtin | shape | means |
|---|---|---|
| `BTensor sh` | variadic, `shapeNumel sh` args | build a tensor from its elements |
| `BMap` | `[IRLambda v body, t]` | elementwise map, shape-preserving |
| `BReduce op axis` | `[t]` | fold along `axis` with `op`, dropping it |
| `BIndex axis` | `[t, key]` | read along `axis` at a runtime key, dropping it |
| `BZip op` | `[a, b]` | elementwise binary `op` over two same-shaped tensors |

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

**An enumerated sum is built in this form and no other.**
`SPLL.Semiring`'s `enumSumNode` emits `reduce op (map (\v -> body) domain)`,
where `op` is `srReduceOp` — so a new reduction is a `ReduceOp` case, not a
constructor. `enumSumP`'s branch-counting path emits **one** let-bound map
reduced **twice**, once for the probability and once for the branch count,
which is the loop-body sharing that needs no second traversal of the body.

There used to be three `IRExpr` constructors here — `IREnumSum`,
`IRLogEnumSum`, `IREnumSumPaired` — plus a whole pipeline stage
(`SPLL.IRTensorPass`) lowering them into the above. Task `retire-irenumsum`
deleted all four: the producers build the tensor form directly, so there is
nothing left to lower. `IRExpr` went from 23 constructors to 20, and the
`-d` dump lost its "After Tensor Lowering" row because the stage is gone.
Emitted code is byte-identical for a default compile; a `-c` (branch-counting)
compile differs only in generated variable names, the loop axis now being named
by `mkVariable` rather than by the pass's own counter.

`IRIsPossible` is the deliberate **residue**: it also carries a `MultiValue`,
but it is a membership *test*, not a loop, emitted as a single
runtime-library call (`isPossible`) that walks the value against the domain
description. Putting it on the dense axis would mean materialising the domain
as a tensor and reducing an equality map with a boolean OR — a reduction
operator existing for no other purpose — so it stays as it is.

Only **rank 1 and axis 0** are emitted. The representation admits any rank and
the interpreter implements it (`fibres`/`rewrap` do the stride arithmetic, and
`Internals/tensor builtins` pins the layout); the three backends refuse higher
rank with a named diagnostic rather than emitting something plausible. Nothing
produces a rank > 1 tensor today.

One refusal this form does **not** preserve: `--batched --logSpace`.
`CodeGenPyTorchBatched`'s `emittable` used to have no `IRLogEnumSum` case (and
refused the log variant of `IREnumSumPaired` explicitly), so a log-space
batched compile was rejected at the guard. There is no such node to reject any
more — a log-space enumerated sum is a `BReduce ROpLogSumExp`, which
`emittable`'s blanket `IRBuiltin{} -> True` admits and which `tensor_logsumexp`
in `pythonLibBatched.py` implements. The combination compiles and gives correct
answers, so this reads as a capability gained for free rather than a hole; but
nothing in the suite covers it (no `.tst` carries a log-space token).

The non-scalar `MultiValue` gate those cases also carried is *not* lost. A
domain's values are now ordinary `IRConst` children of a `BTensor`, and
`batchedVal` refuses each composite one for the same reason
`scalarDiscreteMulti` did — so the refusal is per-constant rather than
per-node. `IRIsPossible` keeps its own `scalarDiscreteMulti` gate, and the
synthetic rows in `TestInternals.batchedRefusalUnitTests` (which had no corpus
trigger) now cover that node alone.

Measured when the lowering first landed, against the compiler before it:
emitted scalar Python is 0–4% *smaller* and 1.09x faster with bit-identical
results; batched Python is
byte-identical in size and 1.00–1.04x, bit-identical at two enumeration terms
and within 7.5e-9 at four (the reduce reassociates). The larger speedups the
design predicts belong to the `BIndex` consumer, which nothing wires up yet.
