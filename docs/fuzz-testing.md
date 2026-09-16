# Fuzz testing (`test/TestFuzz.hs`)

`test/TestFuzz.hs` runs randomly-generated SPLL programs
(`test/ArbitrarySPLL.hs`) against the same metamorphic invariants the
hand-written corpus checks in `Spec.hs`'s Corpus group, rather than known
expected values. `genRawFuzzProgram`/`genRawFuzzExpr` cover the full AST
space and are only useful for crash-freedom (almost every draw is
ill-typed); `genTypedProgram`/`genTypedExpr` build well-typed programs
over scalars, tuples, `Either` and lists (roughly half of all draws are
structured) and drive the real invariants (programs validate, P(ANY)=1,
probability is never negative, topK at threshold 0 reproduces exact
inference and at a real threshold never inflates it, branch counting
doesn't change the probability value, and mixtures follow the
dimension-combination rules). Each property caps structural size and
wraps each case in a wall-clock timeout. Since most draws end up with no
probability function to check, every such branch returns `discardVacuous`
rather than `property True`, so QuickCheck's own discard-ratio accounting
reports this honestly instead of it being invisible inside an inflated
success count.

**The `Fuzz` group is currently red**, and legitimately so: widening the
typed generator to structured types (design `typed-program-generator-expansion`
milestone M1) turned up three distinct compiler bugs, tracked as
`fuzz-structured-type-bugs` in the internal-docs repo. 7 of 11 properties
fail, all tracing back to those three causes — `head []` throwing inside the
IR interpreter, a compile-time blowup specific to structured shapes, and the
generate-backed-prob guard reporting by `error` rather than `Left`. The
default suite is unaffected; per the design, findings are filed rather than
fixed so that coverage work is not blocked behind bug triage.

## Shrinking

`genTypedProgram` draws shrink, via `shrinkTypedProgram`/`shrinkTypedExpr`
in `ArbitrarySPLL.hs`, and every typed property is wired with
`forAllShrink` rather than `forAll`. Before this, a failure was reported
only as a `--quickcheck-replay` seed against a large opaque draw — and
those seeds replay the RNG stream, not the draw, so they do not survive an
edit to the generator or the property.

The shrink is **type-preserving**, and has to be: almost every structural
reduction of a well-typed SPLL expression is ill-typed, so it is discarded
downstream and reduces nothing. `tyOfTypedExpr` recovers a node's `Ty`
from its shape alone (the generator annotates everything `makeTypeInfo`),
and the shrinker offers only strictly-smaller candidates of a compatible
type: the smallest inhabitant of the node's type, either arm of an
`IfThenElse`, a type-matching argument of an `InjF`, and
one-child-at-a-time recursion. A node `tyOfTypedExpr` does not recognise
simply does not shrink, so the shrinker is safe to point at any `Expr`.

Structured types made type recovery **partial**, so the contract is
compatibility rather than equality. A `left x` node fixes only the left
component of its `Either` and says nothing about the right, which
`tyOfTypedExpr` records as `TyAny`; the arms of an `if` are joined rather
than one being picked. Replacing a node whose type was pinned only by both
arms with a single-arm leaf is a well-typed shrink whose recovered type is
strictly *more general*. What keeps that sound is that `typedLeaves` never
offers a leaf committing a free position — `typedLeaves TyAny = []`, and
that propagates through the structured cases — so a shrink may leave a
position free but can never disagree about a fixed one. For the scalar
fragment, compatibility and equality coincide.

Its contract is pinned by the `Shrinker` group, which — alone in this
module — lives in the **default** suite, not in `Slow`: it is pure and
fast, and a break in it would hide every other failure in here behind an
unreadable counterexample. Those tests are named without the `prop_`
prefix so `$(allProperties)` does not also collect them into `Fuzz`.

## Generator coverage instrumentation

`prop_Fuzz_GeneratorCoverage` reports, every run, what the generator
actually produced: the outcome split (validate-failed / compile-crashed /
compile-rejected / compiled-without-a-probability-function / with one),
the realized `pType` of `main`, the top constructor, and node-count and
depth buckets. Without it, a generator that silently collapses to a
single shape after a refactor still gives a fully green run — every
invariant holds vacuously on `Normal` alone.

Measured at 200 draws when this landed: 100% compile, 35% reach a
probability function, and the realized `pType` splits 65% `Bottom` / 23%
`Integrate` / 9.5% `Deterministic` / 1.5% `PNormal` / 1% `PLogNormal`.
The property's `cover` bounds are set well below those and are
deliberately *not* wrapped in `checkCoverage`, so a miss prints
"Only N% ..., but expected M%" as a warning rather than failing the run —
observe first, enforce once the distribution has been characterized over
larger runs.

The `Fuzz` group lives inside `Slow`. One property,
`prop_Fuzz_SamplingMatchesPDF`, cross-checks `generate` against
`probability` independently (every other property only cross-checks
different `CompilerConfig`s against each other) and, since sampling is
expensive, lives in its own further opt-in tier, `SuperSlow`
(`NEST_SUPERSLOW_TESTS=1 stack test --ta '-p SuperSlow'`).

Every `try`/`catch` here must catch only *synchronous* exceptions
(`trySync`, not a bare `SomeException` handler) — `System.Timeout.timeout`
cancels via an async exception, and a blanket handler would swallow the
cancellation itself, defeating the per-case budget for exactly the slow
cases it exists to bound.

The interpreter substitutes a mock for every declared neural network
(`MockNN.hs`); `(2, [logit0, ...])` (a verbatim logit vector) is the only
deterministic mode, used to pin exact densities in `.tst` files.
