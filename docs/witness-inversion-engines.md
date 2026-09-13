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
to set-valued witnesses. See `testCases/planEnum*` for worked examples
across the milestone levels (inline predicates, recursive user-function
specialization, value-grouped DP for counting folds, and continuous-leaf
constraints).

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

yields the `|Normal|` density `2φ(y)` (`testCases/letProbAbsNormal`). Bodies
drawing fresh randomness alongside such constraints are refused with a
diagnostic.

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
`(x + Normal) > 0.0` refuses. Corpus: `testCases/setWitnessNestedLet*`
(seven programs, incl. the two-sided, chained, `observe` and
point-valued-arm shapes); refusals pinned in `TestRejection`'s
`SetWitnessNestedLet` group. The engine stays linear-only, so these programs
are on `Spec.logSpaceUncoveredPrograms` like their single-`let` siblings.

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
`testCases/setWitnessTransport*` (one program per table entry plus the
nested, two-sided and always-false `exp` shapes) and
`testCases/planEnumContExp*`.
