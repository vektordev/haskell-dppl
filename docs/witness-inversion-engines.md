# Witness inversion engines for non-invertible observations

Two engines in `IRCompiler.hs` handle `let`-bindings whose observation can't
be point-inverted onto the bound variable via ordinary forward chaining.
The probabilistic `Apply` arm tries them in the order below, with
forward-chaining point inversion in between.

## Plan-guided lazy enumeration

`planWitnessApply` is tried *first*, ahead of point inversion, and fires when
the bound value is a neural network's structured output
(`let s = nn sym in <predicates over s>`): since the NN's distribution
factorizes per `PartitionPlan` slot, the observation inverts into worlds
constraining individual plan leaves, measured as products of logit-slice
reads — no `of` clause or support materialization needed.

Point inversion's inverses would otherwise crash on these shapes, which is
why the engine intercepts rather than backstops. Bodies its traversal
declines are untouched: they fall through to point inversion, and only then
to set-valued witnesses. See `tests/cases/plan-enumeration/planEnum*` for worked examples
across the milestone levels (inline predicates, recursive user-function
specialization, value-grouped DP for counting folds, and continuous-leaf
constraints).

### Independent factors of a plan-free subtree

A subtree of the body that mentions no plan-bound variable is *independent of
the plan*, not merely occurrence-free: every random draw in SPLL is a
syntactic leaf, and the traversal only ever descends an inlined expression
tree (a shared `let`-bound draw is an `Apply` of a `Lambda`, which is
plan-free as a whole and is caught at that node instead), so such a subtree
shares no draw with the plan leaves. Under independence the joint factorizes,
so the subtree is compiled by the *ordinary* probability compiler against the
same target and multiplied into the world (`PlanWorld`'s `pwFactors`,
combined with `prodP` in `measurePlanWorlds`: probabilities multiply, dims and
branch counts add). This is the plan analogue of the set-witness residue
factor below, and it is what lets a plan-enumerated neural declaration coexist
with fresh continuous randomness at all.

Two entry points: `planFactorFree`, for a whole plan-free subtree in an
observation position, and `planFactorBool`, for a plan-free *if-condition*,
whose two polarity masses become the mixture weights of the two branches'
worlds. Both decline a subtree that also reads a specialized callee's
deterministic parameter (`planEnvDetOccs`) — `planGenDet`'s name rewrite has
no counterpart through a full inference compile. A factored world is never
collapsed by the milestone-4 value DP (`planGroupValues`), whose group mass is
built from `planWorldMass`, which measures plan leaves only.

**The independence is checked, not assumed.** Occurrence-freedom buys
independence from the *plan*; it does not by itself buy independence between
two factors multiplied into the same world. Fresh `Normal`/`Uniform` leaves and
calls to top-level stochastic functions are per-occurrence draws, so two
occurrences never share one. The one shared random source reachable from inside
the traversal is a variable bound by an enclosing `let`, which SPLL's `let`
makes a single draw shared by every occurrence (see
`NeST_internal_docs/designs/let-binding-semantics.md` — the existing `let` is
the *eager* form, `Apply (Lambda x body) expr`; the lazy/substituting `let~` is
only proposed). The traversal cannot descend into such a `let` itself, but one
enclosing the whole plan-bound binding puts its variable in scope, so
`planFactorExternals` refuses any factor that reads a non-`Deterministic` local
of the ambient scope. The check is deliberately local to the factor rather than
tracking which factors share a world: the "same world" relation depends on how
worlds combine, which is the part a future change could alter silently.

No program reaches that hazard today — every enclosing random binding that
would put such a variable in scope is refused by the outer engine before the
plan traversal runs. So the guard is belt-and-braces, and is pinned white-box
(`TestInternals`, `plan factorization independence guard`) precisely because no
corpus program would notice it breaking.

Still refused, and genuinely not a product: value *enumeration* of a plan-free
stochastic subtree (`planEnumValuesRaw` — a stochastic subtree has no single
value to enumerate, it has a weighted support), and a comparison operand that
mixes a plan leaf with fresh randomness (`snd o + Normal * 0.5 > 2.0`), which
is a convolution of the leaf's Gaussian with the noise, not a factorization.
Corpus `tests/cases/plan-enumeration/planFreeStochastic*`.

## Set-valued witnesses

`setWitnessApply` is the last resort: it fires once `toInvExprMaybe` reports
that *no* occurrence of the bound variable is point-invertible, which is what
happens when every path to the binding crosses a comparison or `if`. The
observation then inverts into guarded constraint-set worlds (intervals from
comparisons, measured as CDF differences; case splits from conditionals;
intersections across multiple occurrences) — e.g.

```
let x = Normal in if x < 0.0 then 0.0 - x else x
```

yields the `|Normal|` density `2φ(y)` (`tests/cases/distributions/letProbAbsNormal`). Bodies
drawing fresh randomness alongside such constraints are refused with a
diagnostic, except inside a transported field constructor (see "Residue
factors" below).

A nested `let` between the source and the constraint — `let x = Normal in
let y = x + 1.0 in if y > 0.0 then 1.0 else 0.0`, which the parser desugars
to `Apply (Lambda y b) e` — is inverted *through* the inner binding in two
stages rather than looked past: `invertToWorlds` first inverts the body `b`
onto `y` (using `y`'s own `lambdaVarOccurrences` entry, so every structural
case above applies unchanged), then inverts `e` onto `x` with each y-world's
set as the target, so an interval or point on `y` transports onto `x` through
the same monotone/point machinery (change-of-variables factors compose;
decreasing right-hand sides swap endpoints; a bare rename `let y = x` needs
no special case). A `WFull`/`WEmpty` y-set passes through untouched, and a
`WChoice` y-set — what every point constraint meeting an interval produces,
i.e. the `observe` shape — is transported side by side into two mutually
exclusive guard groups, with the choice condition ordered after the y-guards
(it reads the witness value, which only the y-guards make safe to evaluate)
and before the x-guards. Two shapes keep the existing refusal: `x` occurring
in the inner *body* at all (its worlds would reference the inner binding's
value, which is not in scope where worlds are measured), and an inner
right-hand side drawing fresh randomness (`let y = x + Normal in …`), which
`transportDirect` cannot seed through — exactly where the flattened
`(x + Normal) > 0.0` refuses. Corpus: `tests/cases/set-witness/setWitnessNestedLet*`
(seven programs, incl. the two-sided, chained, `observe` and
point-valued-arm shapes); refusals pinned in `TestRejection`'s
`SetWitnessNestedLet` group. The engine stays linear-only, so these programs
are on `Spec.logSpaceUncoveredPrograms` like their single-`let` siblings.

### Residue factors of a transported subtree

A subtree with a *single* occurrence of the bound variable is transported
whole onto that occurrence by `transportDirect`, through the forward-chaining
inverse seeded at the subtree's root. Every step of that inverse consumes its
sibling operands as premises (`x + c` inverts to `s - c`), except a **field
constructor's**: the deconstructing inverse of `(x, e)` is `fst s`, and `e` is
never consulted. So in

```
let x = Uniform in if x > 0.5 then (x, 1.0) else (x, 0.0)
```

the point `(0.7, 0.0)` transported to `x = 0.7` with full density, and
`p((ANY, 1.0))` answered `1.0` instead of `0.5`; with a fresh draw in the
sibling slot, `(s, Normal)`, the sibling's density was silently omitted
(task `set-witness-transport-drops-sibling-field-constraint`). `TCons`,
`Cons`, user ADT constructors, and any of those under a unary wrapper
(`right (x, 1.0)`) all had it.

When the spine from the subtree's root to the occurrence crosses a field
constructor (`isFieldConstructor`), the world now also carries the subtree's
**residue factor**: the subtree compiled as an ordinary point observation
against the same target, with the bound variable re-typed `Deterministic`
and let-bound to its transported witness (`residueFactor`). That is the
point-witness path's body-factor fold, applied per world. For a residue
that is deterministic given the witness the factor is the missing
consistency indicator (`(x, 1.0) == s` with `x := fst s`, dim 0); for one
that draws fresh randomness it is the sibling's own density, and dims add,
so `(s, Normal)` at `(-0.5, 0.3)` is `φ(-0.5)·φ(0.3)` at dim 2. `WWorld`
carries the factors as a list of `PResult`s; `intersectW` concatenates them,
the nested-`let` case carries a y-world's factors over to its x-worlds
unchanged (they read `y` at its observed value, a function of the sample
alone), and `measureWorld` multiplies them in with `prodP` under the world's
guards. No factor is emitted where no field constructor is crossed, since
the inverse path consumed every sibling there and the indicator would be an
always-true tautology on every transported subtree in the corpus; the
emitted IR of the existing set-witness programs is unchanged.

`memberGuard`'s point case (the x-free deterministic arm, `(0.0, 0.0)`
against `(ANY, 0.3)`) is the wildcard-aware `equalityGuard`, since a target
point is a projection of the query sample and a marginal wildcard can sit
in it at any depth: the static guard errored on a float slot and silently
answered `False` (zero mass) on a discrete one. Corpus:
`tests/cases/set-witness/setWitnessSibling*`.

### Interval transport through monotone `InjF` steps

An interval on a subtree that is a chain of monotone float functions over
the bound variable — `exp x > -1.0`, `(x + 1.0) > 0.0`, `x * (-2.0) > 1.0`,
`exp (exp x) < 2.0` — is carried down to the variable by
`ForwardChaining.toSeededMonotoneInvExpr`: the point inverse of the chain
plus a static direction certificate (`Monotonicity`; a net-decreasing chain
swaps the endpoints, infinities included). The direction table is
`stepMonotonicity` (`plus`/`double`/`exp`/`log` increasing, `neg`
decreasing, `mult` by a *literal* by its sign; anything else refuses the
transport with the set-witness diagnostic — `sqrt`, `recip`, `sq`, and
`mult` by a non-literal such as `(0.0 - 2.0)` all land there).

Every step's input is first clamped into that step's forward **image**
(`injFImage`, next to the direction table; `clampToImage`), because a bound
the forward function can never produce must not reach a partial inverse:
`exp`'s inverse `log` turned `exp x > -1.0` into `log(-1) = NaN`, which
`measureSet`'s empty-interval clamp then laundered into a silent zero mass
on every backend. Clamped, `-1` becomes `0`, `log 0 = -inf`, and the world
has full mass; an interval wholly outside the image collapses onto the
boundary point and measures zero (`exp x < -1.0` is impossible). The clamp
is applied per spine step on the step's own input, which is what makes a
nested chain right — `exp (exp x) > 0.5` sends `log 0.5 < 0` into the inner
`exp`, which clamps it again. Infinite bounds bypass the clamp: `exp`'s
image boundary *is* the argument's infinity, so `(-inf, 5)` on `exp x`
transports to `(-inf, log 5)` directly. `log` has a partial *domain* but a
full image, so it clamps nothing; its `-inf` endpoint stays `-inf` rather
than becoming `exp(-inf) = 0`, which happens to agree with sampling (`log`
of a negative is `NaN`, and `NaN > c` is `False` on every backend). The
plan-guided engine's `planPeelSlice` reads the same image table: its
interval transport (`peelBound`) clamps per step the same way, and its
point transport (`peelPoint`) adds strict image-membership guards instead,
so `exp leaf == -1.0` is impossible rather than a NaN density. Corpus:
`tests/cases/set-witness/setWitnessTransport*` (one program per table entry plus the
nested, two-sided and always-false `exp` shapes) and
`tests/cases/plan-enumeration/planEnumContExp*`.
