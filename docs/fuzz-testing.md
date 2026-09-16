# Fuzz testing (`test/TestFuzz.hs`)

`test/TestFuzz.hs` runs randomly-generated SPLL programs
(`test/ArbitrarySPLL.hs`) against the same metamorphic invariants the
hand-written corpus checks in `Spec.hs`'s Corpus group, rather than known
expected values. `genRawFuzzProgram`/`genRawFuzzExpr` cover the full AST
space and are only useful for crash-freedom (almost every draw is
ill-typed); `genTypedProgram`/`genTypedExpr` build well-typed programs
over scalars, tuples, `Either` and lists (roughly half of all draws are
structured) with `let`-bindings (about 65% of draws carry one), one draw in
five declaring and reading a neural network, and drive the
real invariants (programs validate, P(ANY)=1,
probability is never negative, topK at threshold 0 reproduces exact
inference and at a real threshold never inflates it, branch counting
doesn't change the probability value, and mixtures follow the
dimension-combination rules). Each property caps structural size and
wraps each case in a wall-clock timeout. Since most draws end up with no
probability function to check, every such branch returns `discardVacuous`
rather than `property True`, so QuickCheck's own discard-ratio accounting
reports this honestly instead of it being invisible inside an inflated
success count.

**The `Fuzz` group is currently red**, and legitimately so. Widening the typed
generator to structured types (design `typed-program-generator-expansion`
milestone M1) turned up three distinct compiler bugs, tracked as
`fuzz-structured-type-bugs` in the internal-docs repo — `head []` throwing
inside the IR interpreter, a compile-time blowup specific to structured
shapes, and the generate-backed-prob guard reporting by `error` rather than
`Left`.

Milestone M2 (`let`-bindings) widened the reach of the last of those a great
deal: **43% of typed draws now make `compile` throw instead of returning
`Left`**, measured over 200 draws, and 62% of the witness-shaped ones do. Four
distinct messages account for all of them — the set-valued witness engine's own
refusal (`setWitnessApply`'s `refuse`, ~72% of the crashes), the
generate-backed-fallback guard, `toIRInference`'s "found no way to convert to
IR" fallthrough, and `PredefinedFunctions`' "has 0 inversions solving for". All
four report by `error`, which is what makes them crashes rather than refusals;
the last one needs no `let` at all. Tracked as `fuzz-let-witness-bugs` in the
internal-docs repo.

Milestone M3 (neural declarations) is the same story again and sharper: **76%
of neural draws make `compile` throw**, measured over 300, against 43% of typed
draws overall. The dominant message is new -- a generate-backed fallback
reported from *an enumerated conditional*, which is the plan/enumeration path's
own variant of the guard M2 found on the ordinary path, at 58% of the neural
crashes on its own. Two more are new and rarer: `unionMultiValues` reporting a
mismatch between an empty `MultiDiscretes` and a `MultiEither`, which is an
internal invariant violation rather than a refusal, and a `toIRNormalParams`
failure to extract Normal parameters from a `PNormal` expression. The rest are
the already-filed M2 messages, reached again because a neural draw's body is an
ordinary generated expression and can contain a witness-`let` like any other.
Tracked as `fuzz-neural-plan-bugs` in the internal-docs repo.

The default suite is unaffected; per the design, findings are filed rather than
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
and the shrinker offers only strictly-smaller candidates whose type is at
least as general (see below): the smallest inhabitant of the node's type, either arm of an
`IfThenElse`, a type-matching argument of an `InjF`, and
one-child-at-a-time recursion. A node `tyOfTypedExpr` does not recognise
simply does not shrink, so the shrinker is safe to point at any `Expr`.

Structured types made type recovery **partial**, so the contract is
*generality* rather than equality. A `left x` node fixes only the left
component of its `Either` and says nothing about the right, which
`tyOfTypedExpr` records as `TyAny`; the arms of an `if` are joined rather
than one being picked. Replacing a node whose type was pinned only by both
arms with a single-arm leaf is a well-typed shrink whose recovered type is
strictly *more general*. What keeps that sound is that `typedLeaves` never
offers a leaf committing a free position — `typedLeaves TyAny = []`, and
that propagates through the structured cases — so a shrink may leave a
position free but can never disagree about a fixed one. For the scalar
fragment, generality and equality coincide.

The test is `tyGeneralizes`, and it is deliberately **asymmetric**. M1 stated
it as `tyJoin`-compatibility, which is too weak: a join succeeds whenever no
position actively disagrees, so a `TyAny` on the *node's* side absorbs an
unrelated type on the replacement's. `left (right 0)` recovers as
`Either (Either ? Int) ?` and its own argument `right 0` as `Either ? Int`;
those join, so the argument was offered as a shrink of the node — stripping a
constructor and changing the expression's type. M2's deeper nesting made that
reachable in practice, and `tyGeneralizes` refuses it while still admitting
every reduction the symmetric test was meant to allow. Pinned by the
`Shrinker` group's "a constructor stack is not stripped a layer".

`let`-bindings add a **scope** to all three directions. Generation, recovery and
shrinking are indexed by a `TyEnv` as well as a `Ty`; `collapses` may reduce a
`let` to its bound value always, but to its body only when the binding is dead,
since otherwise the "shrink" would strand an unbound variable — a different and
invalid program rather than a smaller one. Every leaf `typedLeaves` offers is
closed, which is what makes the workhorse reduction scope-safe everywhere.

One consequence of `let` worth knowing: the generator names binders after their
scope depth and then alpha-renames the whole draw with `uniquifyBinders`, because
`SPLL.Validator` is stricter than lexical scoping. It rejects shadowing outright,
and it rejects an `Apply` whose two sides declare any name in common — which two
*sibling* `let`s in disjoint scopes do. A caller composing two independent draws
into one program (`genMixturePair`) has to re-prefix one of them with
`uniquifyBindersFrom`, since both start numbering at `v0`.

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

Since M3 it also reports which neural annotation a draw carries (`none` /
`lazy` / `materialized (of _)` / `explicit (of [..])`) and cross-tabulates the
outcome over just the neural draws -- at one draw in five, the neural surface's
own compile/refuse/succeed split is invisible in the aggregate row, and that
split is the thing M3 is about.

A draw that does not terminate is now *classified* (`CompileTimedOut`) rather
than failing this property. Reporting a hang is
`prop_Fuzz_TypedCompileNeverCrashes`' job, and it still does; a property whose
whole purpose is to print a distribution must not be the one that dies of a
single draw and loses every row gathered before it. There is at least one such
draw in the current generator's range, so this was not hypothetical -- before
the change, a full-length coverage run reported nothing at all.

It also reports the target type and shape, and (since M2) the `let` shape:
`NoLet`, `PlainLet`, or `WitnessLet` — the last being a continuous binding
observed only through an `if` whose condition reads it. That classifier is
*syntactic*: it says which shape was generated, not which engine ran, there
being no hook on `setWitnessApply` to read. It is a sound proxy nonetheless,
because a `WitnessLet` reaches its bound variable only through a comparison and
an `if`, which is exactly what forward chaining cannot point-invert — so a
witness-shaped draw that ends up with a probability function got it from the
set-witness engine and from nowhere else.

Measured at 200 draws when M-I landed: 100% compile, 35% reach a
probability function, and the realized `pType` splits 65% `Bottom` / 23%
`Integrate` / 9.5% `Deterministic` / 1.5% `PNormal` / 1% `PLogNormal`.
After M2, over 500 draws: 71% carry a `let` (51% witness-shaped, 19%
plain), the scalar/structured split is unchanged at 55/45, and the outcome
split is 43% compile-crashed / 35% with a probability function / 17%
without / 4% rejected. The `cover` bounds are set well below all of those and
are
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

## The neural surface (milestone M3)

A neural draw is the corpus' `planEnum*` shape, generated:

```
neural nn :: (Symbol -> T)            -- optionally `of <MultiValue>`
main sym = let s = nn sym in if <observation of s> then _ else _
```

Three things make it different from every other draw.

**`main` takes an argument.** `TestFuzz.fuzzArgs` supplies it: `(0, seed)`, the
mock network's random mode, which produces a logit vector of exactly the
partition plan's width whatever that plan is -- so nothing here has to
recompute the plan. The seed is *derived from the declaration* rather than
drawn, because the declaration is the one part of a neural draw the shrinker
never touches: a seed that moved as the program minimized would let the failing
behaviour evaporate mid-shrink, which is the workflow the shrinker exists to
retire.

**The generated core is wrapped.** `tyOfTypedExpr` cannot recover a type for
the `sym` lambda or for the `ReadNN` (the network's target type lives in the
`Program`, not on the node), so everything that consumes a draw goes through
`ArbitrarySPLL.typedMainCore` instead of reading `main` directly. Without that
indirection every neural draw would report as `<unrecognised>` and, worse,
would silently stop shrinking. The shrinker reduces the core and rebuilds the
wrapper around each candidate; it never reduces the declaration, the read or
the binding, since those are what make the draw a neural draw at all.

**The `of` clause is a second oracle, for free.** A declaration over a purely
discrete target compiles two ways: with no `of` clause the reads go through
plan-guided lazy enumeration, and with `of _` the same declaration gets a
`DiscreteValues` tag and the support is materialized into an `IREnumSum`
instead. The two are one distribution computed by two engines and must agree
exactly. The corpus pins this with hand-written `planEnumRec*`/`*Materialized`
file pairs; `prop_Fuzz_NeuralMaterializedTwinAgrees` gets a fresh pair out of
every draw. `of _` over a target containing a `Float` is *not* such a pair:
`annotateEnumsProg` declines to tag a `MultiValue` with a continuous leaf, so
the twin would be the same compilation. `genNeuralTwinProgram` draws from the
discrete-only lattice for that reason.

Target types are narrower than `Ty`: `Float`, `Bool`, and tuples/`Either`s of
those (what `autoDeriveMultiValue` can produce a plan for), plus `Int` with an
explicit `of [0..k-1]` -- which without ADTs is the only way to get a plan slot
wider than two. ADT targets and recursion are milestone M4.

The `Neural generator` group (default suite, beside `Shrinker`) pins the
machinery the properties depend on being right about: that a neural draw
validates, that its core type is still recoverable and so still shrinks, and
that shrinking never quietly turns a neural draw into an ordinary one.
