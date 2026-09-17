# Fuzz testing (`test/TestFuzz.hs`)

`test/TestFuzz.hs` runs randomly-generated SPLL programs
(`test/ArbitrarySPLL.hs`) against the same metamorphic invariants the
hand-written corpus checks in `Spec.hs`'s Corpus group, rather than known
expected values. `genRawFuzzProgram`/`genRawFuzzExpr` cover the full AST
space and are only useful for crash-freedom (almost every draw is
ill-typed); `genTypedProgram`/`genTypedExpr` build well-typed programs
over scalars, tuples, `Either` and lists (roughly half of all draws are
structured) with `let`-bindings (most draws carry one — see "how many draws
carry a `let`" below, and read the figure the coverage property prints for the
run in front of you rather than any number written down here) and function
values (about a third of draws — see "The arrow surface" below), one draw in
five declaring and reading a neural network and one in five declaring a named
top-level function, and drive the
real invariants (programs validate, P(ANY)=1,
probability is never negative, topK at threshold 0 reproduces exact
inference and at a real threshold never inflates it, branch counting
doesn't change the probability value, and mixtures follow the
dimension-combination rules). Each property caps structural size and wraps each
case in a wall-clock timeout — and, since a QuickCheck property is a *lazy*
value, each one that computes a probability must force that computation inside
the timed action (`forcedProbAt`), or the bound covers only the compile. Since most draws end up with no
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

Milestone M3 (neural declarations) is the same story again and sharper:
**roughly three quarters of neural draws make `compile` throw**, against 43% of
typed draws overall. The exact figure is *not* pinned, and the record disagrees
with itself: this file said 76% over 300 draws, the design's own progress note
says 73% and "222 of 300" (which is 74%), and an independent 200-draw run in
the ninth shift saw 26 of 34 neural draws crash (76%, but n=34). Take "about
three quarters" and re-measure if a number has to carry weight. The dominant
message is new -- a generate-backed fallback reported from *an enumerated
conditional*, which is the plan/enumeration path's own variant of the guard M2
found on the ordinary path, and is the majority of the neural crashes on its
own (recorded as 58% here and 68% in the design; neither was re-derived, and
the coverage instrumentation does not break crashes down by message, so this
one cannot be settled without a fresh instrumented run). Two more are new and rarer: `unionMultiValues` reporting a
mismatch between an empty `MultiDiscretes` and a `MultiEither`, which is an
internal invariant violation rather than a refusal, and a `toIRNormalParams`
failure to extract Normal parameters from a `PNormal` expression. The rest are
the already-filed M2 messages, reached again because a neural draw's body is an
ordinary generated expression and can contain a witness-`let` like any other.
Tracked as `fuzz-neural-plan-bugs` in the internal-docs repo.

**Historical (superseded, kept because the diagnosis below is built on it):**
before the whole-property deadline landed, the Slow `Fuzz` group did not
complete at the default size on this machine. A full run stalled for over 25
minutes inside `prop_Fuzz_TopKNeverInflates`, and
`prop_Fuzz_NeuralMaterializedTwinAgrees` was abandoned after 40 minutes against
a worst case of about 18 by its own per-case budget. The group completes today
— see "The group now completes" below for the current measurement.

**The earlier reading of that overrun — a hang `System.Timeout.timeout` cannot
interrupt — is wrong, and the correction matters.** Run at
`NEST_FUZZ_SCALE=0.9` (see below), `prop_Fuzz_NeuralMaterializedTwinAgrees`
finishes in 50s and *fails properly*: `did not terminate within 5000000us`,
reported as a counterexample and then **shrunk four times**. The per-case budget
fires, is caught, and minimizes. What is unbounded is the **aggregate**, not any
one case. The property discards ~95% of its draws, needs 20 successes, and
spends a full 5s budget on each hanging draw *and on each of its shrink
candidates* — so a run costs (draws + shrinks) × 5s with no ceiling on either
factor. A per-case timeout bounds a case; it does not bound QuickCheck's search.

The minimized draw confirms the culprit is item 2 of
`fuzz-structured-type-bugs`, and sharpens it: **the network is not involved at
all.** The bound variable is dead — the read is applied and then ignored — so
the non-terminating core is pure structured-accessor code,

```
snd (head (Cons (TCons (right (Uniform < 0.79))
                       (TCons (TCons (Uniform < 0.84) (Uniform < 0.65))
                              (Cons (if False then 3 else if False then 2 else 1) [])))
                []))
```

which is the first *minimized* repro for that item (it was recorded there as
"large program, re-derive via replay").

**The group now completes, because each property carries a whole-property
deadline as well as a per-case one** (see "Two budgets" below), and because
every property that computes a probability now forces it inside the per-case
timeout (`forcedProbAt`) rather than handing the driver a thunk. Measured at
scale 1 over four runs in the ninth shift: the whole group finishes in
**128–131s**, against a stall of over 25 minutes and a 40-minute abandonment
for a single property before the deadline landed. Which properties are green
and which spend their deadline **moves from run to run** — the draws are seeded
differently and several properties sit near the 120s line — so read the run in
front of you rather than a list written here. A typical run: 5 of 12 properties
green, two (`TopKZeroMatchesExact`, `TopKNeverInflates`) announcing budget
exhaustion by name on stderr, the rest reporting `did not terminate within
5000000us` against a shrunk counterexample. The group total is well under the
sum of the budgets because tasty runs the properties in parallel — which also
means each property's *wall-clock* deadline is contended, and 120s of deadline
does not buy 120s of one property's compute.

The underlying bug is untouched — the draws still hang, and the properties
reporting it are still red — but a run now ends and prints what it found instead
of having to be killed, so a red `Fuzz` result is readable again. Running at a
reduced `NEST_FUZZ_SCALE` remains the way to get *more* draws through in the
same time; the deadline caps the clock, it does not buy coverage.

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

**How many draws carry a `let`** has been measured three times and come out
differently each time, because the generator kept changing under it and because
the runs differ in `n`:

| When | n | witness / plain / none | carry a `let` |
|---|---|---|---|
| After M2 | 500 | 51 / 19 / 29 | 71% |
| Sixth shift (catalog widened) | 400 | 55 / 25 / 20 | 80% |
| Ninth shift (after `recip` left the catalog) | 200 | 52.5 / 17.5 / 30 | 70% |

Read it as "most draws, roughly 70–80%", and take the exact split from the
coverage property's own output for the run in front of you — that is what the
instrumentation is for. Earlier versions of this file quoted 65% in one place
and 71% in another, neither traceable to a run still reproducible.

The ninth shift's 200-draw run also gives the current outcome split: 51.5%
compile-crashed / 30% with a probability function / 15.5% without / 2%
rejected / 1% timed out, with 73% of realized `pType`s `Integrate`. Compare
M2's 43% / 35% / 17% / 4% — the crash rate has gone *up* as the generator
widened, which is the instrumentation doing its job. The `cover` bounds are set well below all of those and
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

## The InjF catalog

The typed generator does not keep its own list of predefined functions. The
scalar InjF productions are *derived* from the compiler's `globalFEnv`
(`injFCatalog` in `test/ArbitrarySPLL.hs`), which is the design's Axis 1
requirement and what milestone M1 deferred.

The reason is drift, not breadth. A hand-maintained per-type table is a second
copy of `globalFEnv` with nothing keeping the two in step, and the failure is
silent: a predefined function added to the compiler is simply never generated,
and the run stays green. The table it replaced had in fact drifted — it never
emitted `double`, `sq`, `recip` or `max`, never compared `Int`s, and never used
`eq` at all, none of which was a decision anyone took. (`recip` is excluded
again today, but deliberately and by derivation — see below.)

A declaration enters the catalog when its *forward* direction **claims** to be
total on its argument types — `applicability` is `IRConst (VBool True)`, which
is the declaration's own statement about its domain — and every position in its
contract is a scalar. The first condition is the safety one: `log`, `sqrt` and
`recip` are defined only on part of `Float`, and generating them unguarded
would manufacture NaN/Infinity densities that say nothing about the compiler.
Reading the guard off the declaration keeps that judgment in one place, so a
function that later gains an applicability test drops out automatically.

**What `applicability` guarantees is what the declaration claims, not that the
claim is true.** The catalog is exactly as honest as `PredefinedFunctions`, and
`recip` was the counterexample: body `1/a`, applicability `True`, while its own
inverse two lines below carried a `b /= 0` guard with a comment about NaN/Inf
densities. It was generated for eight shifts — 47 occurrences in 400 draws —
and because `typedLeaves TyFloat = [constF 0]`, the shrinker *preferentially*
minimized any failing draw containing it toward `recip 0`, turning genuine
counterexamples into `Infinity` artifacts: the exact false-counterexample class
the shrinker work exists to prevent. The fix was to correct the declaration
(`recipFwd` now states `a /= 0`) rather than to exclude the name test-side, so
that the derivation stays the one place the judgment is made; nothing in the
compiler reads a *forward* applicability test, so that correction is a
statement of domain and not a behaviour change. `recip` is now an
`InjFGuarded` exclusion, derived rather than listed.

A polymorphic contract contributes one entry per instantiation, which is
coverage a monomorphic table could not express: `plus` is generated at both
`Float` and `Int`, `eq` at all three scalars.

Everything with a container in its signature (`Cons`, `head`, `fst`, `left`,
`isNull`, …) is excluded and keeps its dedicated production in `genTypedRec`,
because those need the target type to drive the *shape* rather than just the
argument list — and their element types come from `genTy`, which is wider than
the three scalars the catalog would have offered.

`tyOfTypedExpr` reads the same catalog backwards to recover an application's
result type. That is not an optimization: generation and recovery must agree,
or the shrinker silently declines to shrink the shapes they disagree on, and
counterexamples come back full-size with nothing going red. The `InjF catalog`
test group (default suite, 7 tests) pins the agreement, pins the partition of
`globalFEnv` into generated and excluded — each exclusion carrying its derived
reason — and checks that no draw ever names a function the compiler does not
define. Adding a predefined function changes that partition and fails the
group until someone has decided which bucket it belongs in.

## The depth knob (`NEST_FUZZ_SCALE`)

Structural size and case count are the two dials that decide how much program
space a run visits, and they used to move independently: `fuzzSize` was a source
constant (edit, rebuild) while the count was a flag (`stack test --ta
'--quickcheck-tests N'`). "Same code, shallow in CI, deep nightly" could not be
said in one switch.

`NEST_FUZZ_SCALE` is that switch — a positive multiplier, default 1, applied to
`fuzzSize`, to every `withMaxSuccess` in the module, and (upwards only) to the
per-case wall-clock budgets. Anything that is not a positive finite number
(unset, empty, unparseable, `0`, negative, `1e400`) falls back to 1: a typo in a
cron line should leave the suite doing its ordinary job rather than report a
fake regression. An absurd but *finite* setting is **clamped** to
`maxFuzzScale` (1000) rather than dropped, which is the other half of that
promise: `scaleFuzz` rounds into an `Int`, so `NEST_FUZZ_SCALE=1e30` overflowed
it, and while `scaleFuzz`'s `max 1` catches a negative result it does not catch
a wrapped-positive one — a wrapped-negative `perCaseBudgetMicros` would have
handed `System.Timeout.timeout` a negative argument, which never fires, so a
typo could switch the per-case bound *off*. It is read once through `unsafePerformIO`, because the things
it feeds — `resize`, `withMaxSuccess` — are pure and are evaluated while tasty
builds the test tree, before any property runs.

The budgets scale **up only**. A deeper run draws bigger programs and needs the
room; a shallower one must keep the full budget, or ordinary draws start being
reported as hangs — the false failure the 1s-to-5s history above already paid
for once.

## Two budgets, and they bound different things

The per-case budget (`perCaseBudgetMicros`, 5s; 8s in the SuperSlow tier) bounds
**one case**. It works: a non-terminating draw is cut off, reported as a
counterexample, and shrunk.

It does not bound the **property**. QuickCheck keeps drawing until it has
`withMaxSuccess` successes or has discarded `maxDiscardRatio` times as many, and
it re-runs the case for every shrink candidate besides — so a property that
discards most of its draws and meets a draw that reliably burns its whole
per-case budget multiplies the two together, with no ceiling on either factor.
That is what stopped the group completing. For the properties whose per-case
work is genuinely inside the timed action, it is not a hang the timeout failed
to catch: the timeout fires every time, and there are simply too many firings.

That qualification is not pedantry — the unqualified version of this sentence
let a real hole survive three shifts. `withinBudgetScaled` wraps `timeout`
around an `IO Property`, so it bounds only what that action actually *forces*.
Five properties returned their probability comparison as an unforced thunk
(`return $ case irProb … of …`); `ioProperty`'s rose tree is forced by the
QuickCheck driver *after* `timeout` has returned `Just prop`, so `runProbC` —
the entire IR interpretation — ran outside the bound, and only `compileSafe`
was actually guarded. A draw that failed to terminate inside `runProbC` could
therefore hang the group with no timeout able to fire, the whole-property
deadline included (it is consulted at the *entry* of the next case, which never
arrives). The repair is `forcedProbAt`: draw the sample and `evaluate` the
comparison inside the timed action, which is what
`prop_Fuzz_NeuralMaterializedTwinAgrees` had done from the start. Anything
added here that computes a probability must do the same; returning a lazy
`Property` from `withinBudget` silently opts out of both budgets.

So each property also carries a **whole-property wall-clock deadline**
(`propertyBudgetMicros`, 120s, scaled upwards only by `NEST_FUZZ_SCALE`; 600s in
the SuperSlow tier, whose length is expected rather than pathological). Once it
is spent, the remaining cases are **discarded** rather than failed, so the
property drains in milliseconds and QuickCheck's own "Gave up! Passed only N
tests" is the verdict. Failing instead would be actively misleading: every
shrink candidate would also be over budget and fail instantly, so the run would
report an arbitrary minimal program as the counterexample for what is really a
timekeeping event. A one-line note naming the property and the budget goes to
stderr, because a discarded case's `label`/`counterexample` does not survive into
the give-up report, and "gave up" alone cannot be told from a picky
precondition.

This is a wall-clock bound on a test and so is machine-dependent, in exactly the
way the per-case budget already is. The default is set well above what any
property needs when it is behaving — the slowest, `prop_Fuzz_GeneratorCoverage`,
takes ~11s at scale 1 solo (34–37s when the whole group runs) — so hitting it
means something is genuinely wrong rather than that the bound was tight.

That "solo" is worth spelling out, because tasty runs ~12 of these properties
**in parallel** and a wall-clock deadline is therefore contended: a property's
120s buys it rather less than 120s of compute. The ninth shift checked whether
that had quietly turned any well-behaved property into a permanent give-up, and
it had not: `prop_Fuzz_ProbNeverGenerateBacked`, the suspected victim, spends
~78–116s of its deadline but **fails on a real per-case timeout**, `did not
terminate within 5000000us` against a shrunk counterexample, rather than
exhausting the deadline — and it is not a property that "does no compiling", it
compiles every draw and some of those compiles hang. So the deadline was left
alone. If a property ever *does* start giving up for timekeeping reasons, the
fix is to lower its `withMaxSuccess` to what the deadline can buy, not to raise
the deadline: the deadline exists to make the group terminate. The deadline is fixed at the property's first
case and does not slide forward, which is what makes it an aggregate bound
rather than a second per-case one; `budgetStep` is split out pure and pinned by
the `Fuzz scaling` group, since a bound that silently never fired would let the
stall it exists to prevent come back unnoticed.

It scales **down** as well as up, which is not what the design originally asked
for but is the more useful direction today: the draws that hang are the large
structured ones, so a reduced scale is how a verdict gets out of the
already-written oracles while the underlying bugs are drained. Measured on
`prop_Fuzz_GeneratorCoverage`: 0.01s at `0.02`, 0.89s at `0.25`, 10.6s at `1`.
Cost grows faster than the scale, since size and count both move.

`prop_Fuzz_GeneratorCoverage` tabulates the effective setting, so a nightly run
deep enough to be worth reading can be told apart from an ordinary one in its
own output.

The contract is pinned by the `Fuzz scaling` group in the **default** suite,
beside `Shrinker` and `Error channels`. A knob that silently read as 1 would
turn a nightly deep run into an ordinary one with nothing going red — the run
would simply pass, shallowly — so `parseFuzzScale` and `scaleFuzz` are split out
of `fuzzScale` to be testable without an environment.

There is no CI configuration in this repository, so the design's "CI-vs-nightly
split that actually invokes it" has nothing to attach to yet; the knob is the
half that can exist without one.

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

## The arrow surface (task `fuzz-arrow-generator-coverage`)

The generator emits function *values* — a lambda bound, passed, selected by an
`if`, projected out of a tuple or list, or declared at the top level — and
applies them. Mechanism and productions: `api/test/ArbitrarySPLL.md` in the
internal-docs repo. What matters here is what it costs and what it found.

**It is deliberately one production slot, not three.** `genTypedExprIn` picks
with `oneof`, so anything added at a node dilutes everything else there
equally. At three slots the axis measurably cost the two properties that draw
a *pair* of programs — `prop_Fuzz_MixtureFollowsCombinationRules` and the
neural twin oracle — their power: both need two draws to reach a probability
function, so they see the square of that rate, and both stopped falsifying and
started giving up on their discard ratio. At one slot the rate of draws
reaching a probability function is 20–26% against a 31% pre-axis baseline, the
compile-crash rate is 52–54% against 51.5%, and a third of draws still carry a
function value.

**`Slow` was red before this and is red after it.** Three full runs: 8 of the
25 `Fuzz` properties fail without the axis, then 9 and 7 with it. Read that as
"the same eight-ish properties, all of them falsifications of the already-filed
`fuzz-structured-type-bugs` / `fuzz-let-witness-bugs` / `fuzz-neural-plan-bugs`
families, plus or minus a seed" — **the count is not stable enough to carry an
argument**. Each property is bounded by a wall-clock budget rather than by a
draw count, so which ones get far enough to falsify moves between runs. The
one property that failed with the axis and not without it,
`prop_Fuzz_MixtureFollowsCombinationRules`, did not fail on the third run
either.

What the axis found, in one run each:

- The **curried-callee crash** (`toIRInference/Apply: chain name 'ast2' should
  resolve to a lambda, but resolved to … IfInfo …`), which is gap 1 of the
  already-filed `callee-normalize-curried-and-accessor-gaps` — an independent
  rediscovery of a known defect, which is the axis working as intended.
- A **new** crash with no function value in it at all:
  `main = 6 * (if Uniform < 0.5 then 1 else 0)` dies in `forceOp` at `-O2` and
  in the interpreter at `-O0`, because the `Int` multiplication inverse is
  written with a division that neither evaluator defines. Filed as
  `int-mult-inversion-divides-and-crashes`. The axis only changed which draw
  the search reached first.
- A **compile blowup** on a draw carrying function values, filed as
  `mixture-blowup-on-function-value-draws` — unminimized, seed-dependent (it
  reproduced in one run of two at the same commit), and not established to be
  caused by the function values rather than by the 19-comparison chain in the
  same draw.

The `Arrow generator` group (default suite, beside `Shrinker` and `Neural
generator`) pins the classifier every coverage bound is stated in terms of,
that a helper draw validates and applies its helper, and the one soundness
rule the shrinker has to respect here: a function value reduces to the
constant function as a whole and is never minimized from within, because
nothing at a bare lambda says what its parameter was bound at.
