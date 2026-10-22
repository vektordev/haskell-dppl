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
to set-valued witnesses. See `test/cases/plan-enumeration/planEnum*` for worked examples
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
Corpus `test/cases/plan-enumeration/planFreeStochastic*`.

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

yields the `|Normal|` density `2φ(y)` (`test/cases/distributions/letProbAbsNormal`). Fresh
randomness alongside such constraints becomes a factor of the world it sits
in, either as a transported field constructor's residue or as an x-free
subtree (see "Residue factors" and "Fresh x-free subtrees" below); what is
still refused is fresh randomness *combined arithmetically* with the bound
variable (`x + Normal > 0.0`), which is a convolution, not a product.

**Where a refusal lands.** Every refusal in this document -- the set-witness
diagnostic, a plan traversal's decline carried inside it, the orthant
over-coupling message -- is a refusal of one *variant*, not of the compile
(task `static-refusals-become-absent-variants`). The probability (or
integrate) function is absent, exactly as for a `Bottom`-typed program, and
its reason is recorded on the function group (`IRFunGroup.refusedVariants`):
`runProb`/`runInteg` and the CLI's `probability`/`cumulative` commands answer
with it, `generate` still compiles, and any function whose variant calls the
refused one is refused too, naming it.

The False outcome of an `==` is a *complement*, not a point: `x == 0.0`
observed False confines `x` to `WExcept WFull 0.0`, every value but that one.
Intersecting it with another constraint keeps the removal (`(s \ p) ∩ t =
(s ∩ t) \ p`), and it is measured as the set's mass minus the point's in the
semiring's sense (`mixSubP`): for a continuous `x` the point is a density and
the set keeps its whole mass. So `draw x = Normal in if x == 0.0 then 0 else
if x == 1.0 then 1 else 2` answers `p(0) = φ(0)`, `p(1) = φ(1)` (densities,
dim 1) and `p(2) = 1` (dim 0) — the letfree `if Normal == 0.5 ...` agrees,
through the same subtraction in the `IfThenElse` rule. Corpus
`test/cases/set-witness/setWitnessContinuousEquals*` (task
`sampling-matches-pdf-continuous-equality-density`).

**Null-set conventions under negation.** Every interval of a continuous
variable is closed at its bounds, so a boundary query answers the density.
For a Float variable, `invertToWorlds` closes an interval with one of its
own bounds removed back to the interval (`closeNullExcept`, a runtime
`WChoice` on "the removed point is a bound"; measured once, from the
excepted side): `not ((v < 1.0) || (v == 1.0))` is `v > 1.0` and answers
the same density at 1. A point removed from an interval's inside or from
the whole line stays removed, which keeps `x == 0.0` meeting its own
complement empty. On the letfree side, the `IfThenElse` rule derives the
False weight as the complement of the True weight, which cannot carry a
density, so a negated condition `if not c then a else b` is compiled as `if
c then b else a`. Task `null-set-conventions-not-preserved-under-negation`;
the remaining boundary inconsistencies (both polarities closed, Float atoms,
a removed point hiding a query point) are task
`set-witness-null-set-boundary-conventions`.

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
right-hand side convolving the bound variable with fresh randomness (`let y = x + Normal in …`), which
`transportDirect` cannot seed through — exactly where the flattened
`(x + Normal) > 0.0` refuses. Corpus: `test/cases/set-witness/setWitnessNestedLet*`
(seven programs, incl. the two-sided, chained, `observe` and
point-valued-arm shapes); refusals pinned in `TestRejection`'s
`SetWitnessNestedLet` group.

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
`test/cases/set-witness/setWitnessSibling*`.

### Fresh x-free subtrees

A subtree that mentions no occurrence of the bound variable and is not
`Deterministic` draws fresh randomness of its own, independent of the bound
draw. `invertToWorlds`' first clause used to refuse it, so

```
let x = Uniform in if x < 0.5 then Normal else x
```

had no probability function although `Normal` alone is the simplest thing the
compiler compiles (task `world-residual-factor-delegation`, design finding F8).
`worldFactorFree` now measures it as the factor of one unconstrained world
(`WWorld [] WFull [f]`), reusing `measureSet` with the subtree in the bound
distribution's role: a point target is its density or mass there (times the
target's change-of-variables factor, which matters when the target is a
nested `let`'s transported y-point), an interval its CDF difference, a
`WChoice` either side at runtime. The factor is compiled in its own writer
scope into a self-contained block that is let-bound **once** (`WFactor` carries
the binding), and `measureWorld` emits it under the world's guards through
`shareResult`. Folding the block into each of the four `PResult` fields instead
(as `residueFactor` does) copied it four times per nesting level: a fuzz
program with a fresh `draw` nested in an x-free field grew to 23MB of `-O0`
IR and compiled 6x slower, enough to trip the fuzz per-case deadline. That answers the program above as
`0.5·φ(y) + [0.5 ≤ y ≤ 1]` (dim 1), and cumulatively as
`0.5·Φ(y) + clamp(y − 0.5, 0, 0.5)`.

An x-free *condition* that draws fresh randomness takes the same case split
as an x-dependent one: each polarity inverts through the x-free clause into a
factor world carrying `P(c = polarity)`, so the arms are weighted by the
condition's two masses (`if Uniform < 0.3 then … x … else 1.0`) -- the
set-witness twin of the plan engine's `planFactorBool`.

Two refusals remain. An interval target on a non-scalar subtree would need a
multivariate CDF, which nothing provides (the cumulative query then gets the
engine's usual runtime `IRError`). And, as on the plan side, independence is
**checked**, not assumed: a subtree reading a random local of the ambient
scope -- an enclosing eager `draw`, one draw shared by every use -- is refused
by the same `planFactorExternals` test, since it would not be independent of
the bound draw's other readers. That shape has no end-to-end spelling today
(the outer binding is refused first), exactly as on the plan side.

Corpus: `test/cases/let-bindings/letProbFresh{Branch,BranchAtom,Condition}`,
`test/cases/set-witness/setWitnessNestedLetFreshBranch` (the fresh arm one
binding down, measured at the transported y-point), and the control
`letProbFreshBranchTuple`, which the residue factor already answered. The
emitted Python of every pre-existing corpus program is byte-identical.

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
`test/cases/set-witness/setWitnessTransport*` (one program per table entry plus the
nested, two-sided and always-false `exp` shapes) and
`test/cases/plan-enumeration/planEnumContExp*`.

### A point transport that reads a wildcard

A point transported through an arithmetic step (`x + 0.0`, `log x`) at a
marginal query's `ANY` has no value: the step's inverse is a raw type error
on the wildcard (`Minus (VAny, 0.0)`), and so is its domain guard (`exp`'s
`s > 0`). The bare `x` in the same slot recovers the wildcard itself, which
every consumer of a `WPoint` reads as "unconstrained". `transportDirect`
gives the arithmetic chain the same meaning: where the chain's
`invReadsAny` (`ForwardChaining.readsAnyChain`) holds at run time, the set
is `WFull` (a `WChoice` on that test), the domain guard holds, and the
residue factor fixes the variable at the wildcard. Nothing of the chain is
evaluated on that side. The residue factor stays safe because
`equalityGuard` tests the sample before the value, and compares a tuple it
builds syntactically (under its let-bindings) field by field, each field
under its own bindings only. So `x + 0.0` under an `ANY` field is never
computed. The point-witness fold has the matching rule: where a wildcard
witness has no answer of its own (a non-inline body in probability mode),
the operand's result is read at it as its marginal, one (`anySafe`), before
the operand's own inverse steps run. Task
`any-slot-through-injf-inverse-reaches-condition`; corpus
`test/cases/set-witness/anySlotThrough*`.

### One step around a subtree that does not transport

`transportDirect` carries a whole subtree onto the variable's *one*
occurrence in it. A step wrapped around a subtree with several occurrences
-- an `if`-mixture, `(if x < 0.0 then 0.0 - x else x) + 0.0` -- has no such
inverse, and a projection of a literal pair has no interval step (`fst (x,
0.0) > 0.5`). Both used to be refused, and they were most of the
rewrite-invariance net's logged frontier for its injf-identity and
tuple-law families. The walk now has two more structural cases, mirrored in
`worldsShape`:

- **`fst (a, b)`, `snd (a, b)`** is inverted as `a` (resp. `b`) against the
  same target. The other field's value is discarded, so its randomness
  marginalises to one and its reads of the variable constrain nothing
  (`fst (x, x > 0.5) > 0.5` is `P(x > 0.5)`).
- **An InjF step `f (.., a, ..)`** whose operand `a` alone reads the variable,
  the others deterministic, is the binding `let y = a in f (.., y, ..)`
  without the `let` (`invertThroughStep`): the observation is transported
  through the step alone, by `transportDirect` with `a`'s node in the
  variable's role (a point picks up the step's change of variables, an
  interval its direction, a wildcard target makes the set `WFull`), and each
  resulting set is the target for inverting `a` onto the variable -- the
  nested `let`'s stage 2 (`invertOntoValue`), so steps compose. The
  structural InjFs (`==`, comparisons, connectives, `TCons`) keep their own
  cases, and a field constructor is not a step here: its inverse consults no
  sibling, which the residue factor makes up for only at a bare occurrence.
  A step over two operands that both read the variable (`m * m`) stays
  refused. The step trusts forward chaining's inverse, as `transportDirect`
  does, so `sq`'s missing negative root (task
  `sq-inverse-drops-nonpositive-preimages`) reaches it too.

Both cases come after `transportDirect`, so a subtree that transported keeps
its emitted code. Task `set-witness-walk-stops-at-identity-injf-wrapper`;
corpus `test/cases/set-witness/setWitnessThroughStep*`, refusal pinned in
`TestRejection`'s `SetWitnessNestedLet` group.

## Plan engine: entry points, several reads, case splits

The plan engine is entered from a `draw` of a neural read **and from a call of
a top-level function straight on one** (`planWitnessApply`, tasks
`plan-engine-not-entered-for-inline-neural-read`,
`of-annotation-continuous-leaf-disables-enumeration`): `sevens (readDigits s)`,
`match (readAttrs s1) ++ match (readAttrs s2)`. Such a call is a *tagged
invocation* in forward chaining's sense, which the traversal used to decline
outright; the tag only names FC's per-call-site inversion variables, which
this AST traversal never reads. What it does need is a callee body meaningful
in the caller's scope: a top-level function's outermost lambda has no free
locals, and for a curried callee (`match c (readAttrs s)`, the CLEVR
exist-with-predicate shape) `calleeLeadingArgs` binds each outer parameter to
its call-site argument under a fresh name, provided the argument is
deterministic given the enclosing recovered variables. A random leading
argument, or a let-bound lambda called from another scope, is still declined.
Before, an `of` domain over the dense budget, or one with a `Real` leaf, made
these spellings fail in set-valued witnesses where the `draw`-bound twin
compiled. Corpus `plan-enumeration/ofRealLeafCounting*`,
`planRecursiveHelperOn{Inline,Drawn}Read`.

One traversal can hold **several neural reads** (`planOpenBinding`, task
`plan-pairwise-across-separate-neural-reads`). Plan leaves are keyed by a flat
logit offset, so a nested `draw b = readX s2` met inside the body gets its own
disjoint offset range (`psNextOff`) and its own raw-vector binding
(`psRaws`, read through `planRawRead`); two independent reads' joint is the
concatenated plan, and a comparison across them is the same `pwPairs`
difference Gaussian as inside one read. That is the one-read-per-object CLEVR
layout (`plan-enumeration/planPairwise*`). A single read is `[(0, nn_raw)]`
and emits what it always did. Refused inside a specialized function (its
memoized specializations would share one range between two calls, merging
independent reads) and for a symbol argument that is not plan-free and
deterministic; pinned in `known-issues/planPairwise*`, together with the
helper shapes ModalityInfer types `Bottom` first.

A call argument that *is* plan-dependent but not an accessor chain -- a fold's
result handed to a helper, `isValid (checksumSum 1 ds)` -- is **case-split on
its value** (`planResolveApply`, task `plan-fold-result-through-helper-crashes`):
the argument's (value, world) pairs come from `planEnumValues`, the callee is
specialized once per value (bound as a deterministic `PBDet` constant, so the
memo keys on it), and each specialization's worlds are intersected with its
value's world. Both sides are partitions, so the result is one too; the
intersection (not a product of masses) is what keeps it right when the callee
also reads the scene through a slice. It used to die with an uncaught `error`
("neither a plan slice ... nor deterministic given scope: Apply"). A call that
needs no split takes the old code path and emits identical IR. Cost: when two
readers constrain the same leaves value grouping is off (see the grouping
clash rule below), so each split argument carries one world per scene path, and two split arguments cross-multiply (443 s at 1111 paths).
Corpus `plan-enumeration/planHelperOnFoldResult*`; differential
`Internals.planHelperOnFoldResultMatchesDense`.

The same split applies to a value **shared by several children of one node**
without any call (`planShareSplit`, task
`plan-fold-disjunction-of-comparisons-blowup`): in `(f ds == 0) || (f ds == 10)`,
or `draw s = f ds in (s == 0) || (s == 10)` after `planBetaReduce` copies `f ds`
into both comparisons, the copies used to be enumerated separately, bake the
same leaves, clash, and rerun ungrouped (exponential; 2 GB OOM at barcode
depth 4). Now the shared sub-expression (plan-dependent, not a slice,
`planDetGivenPlan`; matched annotation-blind by `sameTerm`, outside lambdas) is
enumerated once and replaced by a fresh `PBDet` variable per value. It is tried
at every plan-dependent node of `planEnumValuesRaw` and at every *scalar*
(Bool/Int/Float) one of `planInvert`. A structured observed node is not split,
because a partial-`ANY` target like `(ANY, 1.0)` needs the field-wise
`planAnySplit` and `planDetGuard` is deliberately wildcard-blind below the top.
It falls back to the old dispatch if the value cannot be enumerated. Corpus
`plan-enumeration/planFoldDisjunction*`; tests
`Internals.planSharedFoldValueMatchesDense`, `planFoldDisjunctionPolynomial`.

### Factored observations and count guards

A point observation of a product region (`sc` against a `Scene` value), or of
a constructed value (`Scene (soften (o1 sc)) ...`), factors over the fields:
its worlds are a conjunction of per-field world lists on disjoint leaves
(`PlanConj`, built by `planInvertConj`/`planRefConj`, kept disjoint by
`conjAdd`). Crossed, N fields of c alternatives are c^N worlds; `conjFlatten`
instead collapses every multi-world conjunct but the largest into one summed
mass (the value grouping on a single value, so the clash rule still applies).
Where at most one conjunct has several worlds nothing changes.

An `if` whose condition is a comparison of a plan-dependent sum against a
deterministic bound, and whose branch observation factors (`planConjShape`),
goes through `planInvertIfConj` (task
`scene-count-conditional-edit-exponential`): each branch's conjuncts are pushed
down the sum into the one summand whose static footprint (`planFootprint`)
holds their leaves, and intersected into that summand's worlds *before* the
count is grouped (`planEnumAbsorb`). Without this the branch constrained every
leaf the count had baked, every world clashed and the traversal reran
ungrouped: "if at least two objects are metal, make them rubber" was 2 MB at 6
slots and OOM at 10. Now it is the DP over (slot, count so far), 160 KB at 10
slots. A conjunct that arrives grouped clashes when absorbed; the branch is then
rebuilt with its own grouping off (`planUngroupedLocally`, the attempt
discarded by `planAttempt`). Dead-branch gating is decided on a traceless probe
of the condition (`planProbe`). Corpus `plan-enumeration/sceneCountConditionalEdit`;
growth test `Internals.sceneCountConditionalEditPolynomial`. Not covered: a
count threaded through a helper (`bump c o` folded over the slots), whose
summands are not separate operands.

## Set witnesses: equality through a transform

An `==` whose bound-variable operand is not the bare occurrence (`exp x ==
1.0`, `x * 2.0 + 1.0 == c`) is split by `equalityWorlds` before the point
transport sees it, so the complement is placed on the bound variable itself
rather than handed to every inverse step below the `==` (`log`, `b > 0`,
`b - 1.0`). The True outcome is inverted as the point `side = c`, and the
False outcome is `WExcept WFull x_c` where the inverse's applicability guard
holds and `WFull` where it fails. Only a single plain point world is
complemented; anything else is refused. Corpus
`test/cases/set-witness/setWitnessEqualityThrough*`,
`setWitnessContinuousEquals*`, `setWitnessIntervalThenContinuousEquals`,
`setWitnessNestedLetContinuousEquals`.

The same rule decides the letfree `IfThenElse`: its False weight is
"certain minus `p(cond = True)`" through `mixWith`, not a bare
`srComplement`, so a condition whose True outcome is a density (a continuous
`Normal == 0.5`) leaves its False branch the whole unit mass at dim 0, where
it used to answer `1 - density`. At dim 0 the two agree exactly, and the
combine is still `srComplement` (max-product refuses `srMinus`).

## Affine Gaussian marginalisation of an unwitnessed `draw`

A third answer to "no occurrence of the bound variable is point-invertible",
tried before set-valued witnesses: if the binding's certificate is a Gaussian
affine form and **every** use of the variable flows affinely into **one**
Gaussian density leaf, the variable needs no witness at all -- it is
integrated out analytically inside that leaf (task
`affine-gaussian-closure-lost-across-let-bindings`, the scalar M1 slice of
docs design `affine-gaussian-forms`; dispatched on the certificate since
`affine-form-as-law-certificate`, law-carrying-modality M4).

**The certificate.** ModalityInfer issues `JAffine` for every node with an
affine form: a `plus`, a `mult` by a constant, or a `neg` over operands that
have one (`affineInjF`, `affineOf`). A point mass is a constant, and any other
`PNormal` operand is one fresh latent keyed by its own chain name. The node is
`PNormal` exactly when that form exists; `tryNormalClosure` keeps only the
log-normal rows. `bindParam` binds a Gaussian argument at its form, keyed by
the argument's chain name, so every read of the variable carries the same
latent (`draw x = Normal in x + x` is one latent). A witnessed binding is one
`Recovered` latent to whatever reads it, and records its own density factor:
the `Marginal` latents its argument integrates (`acFactors`). A field
constructor's density is the product of those binding factors (each counted
once) and each field's residual; where two factors integrate the same
`Marginal` latent it is `JSharedLatent`, floored to sample-only. A latent
the joint affine engine integrates (below) is `Joint` instead, and sharing it
is not a reason to floor.

**The compiler.** `CompilerMetadata.affineEnv` holds the IR of such a variable's
form, `c + sum a_i * eps_i` over independent standard normals, keyed the same
way: by the chain name of the env-free Gaussian leaf that introduced each
latent. `toIRNormalParams` collapses a form (`mu = c`, `sigma` the norm of the
coefficient vector) **only** for expressions reading an `affineEnv` variable,
so everything else emits exactly what it did before. The Gaussian catch-all
takes such an expression (`readsMarginalised`) whether or not it has a handler
of its own. The rules are `plus`, `mult` by a deterministic operand, `neg` and
the env lookup; `-` is `plus`/`neg` by the time IRCompiler sees it.

`affineMarginalisable` decides applicability. It reads the argument's
certificate (`affineOf` over its `lawTable` law), and keeps `isAffineOver` as
the check that the form's IR can be built (inside a callee entered at a call
site the certificate, issued over the program as written, cannot promise
that). "One leaf" means: all occurrences sit in a single affine `PNormal`
consumer, which is either the value of a directly nested `draw` (that
binding's own treatment -- witnessed, marginalised in turn, or refused --
carries the latents on) or the let spine's terminal expression. That is what
keeps the scalar collapse sound. Otherwise the binding goes to
`setWitnessApply`:

- uses spread over two consumers: `(x + Normal, x + Normal)` needs a joint
  density, and so does `draw y = x + Normal in x + y`, since `y` may be
  witnessed and then `x`'s latents would be counted twice. Those go to the
  joint affine engine, next;
- a binding whose body cannot be compiled inline (`bindInline`: a top-level
  callee's own body), or one returning a function;
- anything non-Gaussian or gated -- a chain gated on its own state is `Bottom`
  in ModalityInfer and never reaches here.

A saturated call of a non-recursive top-level function is affine when its
arguments are, and its body is affine over the parameters they bind
(`affineCall`, `affineCallForm`): constant arguments are let-bound, the others
enter `affineEnv`. The latents the body draws are keyed by the call site too,
so two calls of one helper draw independent latents, while a latent reaching
the body through an argument keeps its key and stays shared.

Witnessed variables mix in for free: after an inversion `reinferRecovered` makes
them `Deterministic`, which the algebra treats as constants. That is what
answers a partial observation like `(s1, s3)` of a three-step chain, as
`N(s1) * N(s3 | s1)` with `s2` integrated out. Corpus
`let-bindings/affineChain*`, `affineSelfSum`, `unwitnessedGaussianLetChain`,
`higher-order/arrowApplySelfSum`.

### Joint affine marginalisation: correlated Gaussian fields

The fourth engine, tried after the single-consumer collapse and before
set-valued witnesses (design `affine-gaussian-forms` M2). It applies when the
binding's certificate is an affine form and the body is a let spine whose
every binding is affine over the variables bound so far, ending in a tree of
tuples (`jointAffineApplicable`, twin of `ModalityInfer.jointAffineBindingCert`).
The engine does not dispatch the nested bindings: every spine variable enters
`affineEnv` with its form. The fields reading the spine (at most
`jointAffineMaxSlots` = 3) are jointly Gaussian, with means their constants
and covariance the Gram matrix of their coefficient vectors. The other fields
read none of it and are independent factors, compiled as usual.

- **Classes.** Two fields covary unless their covariance is a constant zero
  (no shared latent, or orthogonal coefficients). A class of one field is a
  scalar Gaussian leaf, so `(x + y, x - y)` is two independent `N(0, √2)`,
  with a CDF. A larger class is one multivariate density.
- **The density** (`jointGaussianDensity`) is unrolled through the Cholesky
  factor `L` of the class's covariance: `z = L⁻¹ r` for residual `r`, and the
  density is `∏ φ(zᵢ) / Lᵢᵢ`, a product of standard normal leaves under
  `srTimes`, so log space keeps a tail's precision. The coefficients and
  covariances are let-bound once; the factor is local to its arm.
- **`ANY` fields.** One density per subset of observed fields, selected on
  each field's `ANY` test (the field's own sample, or a tuple around it): a
  Gaussian's marginal drops the unobserved rows. The dimension is the number
  of observed fields of the class.
- **Refusals.** A constant singular covariance (`(x + y, x + y)`) declines:
  the law is degenerate and needs its rank (M4, ticket
  `affine-gaussian-rank-deficient-joint-law`). A covariance that is not
  constant gets a run-time check on each pivot instead, an `IRError` if it is
  singular for those inputs. A cumulative query of a class of two or more is
  refused, since the joint CDF of correlated Gaussians has no closed form.
  The lattice cannot see either (the certificate carries no coefficients), so
  both are over-promises the admission oracle lists (`knownOverPromises`).

In ModalityInfer, `letBinding` re-infers the body with the argument's own
latents marked `Joint` when this engine is the first that applies. Latents
the argument reads through another variable keep their recovery, so a
sharing outside the body still floors. Corpus `let-bindings/correlatedGaussianLetSharesLatent`,
`affineSharedLatent*`, `affineSumDifferenceDecorrelates`.

## One application rule: `Binding`

Every probabilistic application `l v` is resolved to a `Binding`, whatever its
head: a lambda in place (a `draw`), a named function, a function parameter, a
let-bound lambda (`resolveBinding`; task `binding-resolver-one-application-rule`,
design `law-carrying-modality` §C). It names the resolved lambda, its
parameter, body and occurrences, forward chaining's invocation tag, and two
facts the engines decide on instead of the head's syntax:

- `bindScope`: how the body is made meaningful at the call site. A curried
  callee's leading parameters are let-bound under fresh names when their
  arguments are deterministic (`enterBindingScope`); a lambda bound that way to
  a function parameter is recorded in `boundLambdas`, so a call through the
  parameter is a binding too.
- `bindTopLevel`: a top-level callee's body is never compiled inline as a body
  factor, because it may be recursive. Its body factor is the callee's own
  `_prob` at the recovered witness (`namedCall`), or nothing.

The modality engine asks the witness question of the same resolved lambda for
every head (`ModalityInfer.letBoundLaw`), so a helper's parameter is `IWit`
like a `draw`'s. Each engine's applicability is a predicate both sides read
(`modality-and-admission.md`, "Engine applicability"), and `applyBinding`
tries them as a declared list. The engines:

- **point inversion** folds the body inline where `bindInline`, else uses
  `namedCall` where the variable reaches a field, else the single witness. The
  field test follows `draw` binders (`occursUnderFieldCtor`). A cumulative query
  through a binding read more than once is refused for every head.
- **set-valued witnesses** invert through a call the way they invert through a
  nested `draw` (`callBindingAt`, `invertThroughBinding`): a saturated
  non-recursive top-level call binds whichever parameter x reaches, the others
  being deterministic; a call through a bound lambda or a resolved in-scope
  lambda binds its parameter. A `draw` whose body hides a field constructor
  carries the residue factor (`letHidesField`).
- **a random leading argument** (`pair Uniform Uniform`, `obs b p`) is bound
  first, in parameter order, as a curried lambda in place binds
  (`leadingArgBinding`): its witness is read from the call's forward-chaining
  copy, and its body factor is the call with the argument replaced by the
  recovered variable. `ANY` in that witness slot is a runtime refusal, and the
  cumulative variant is refused.

Corpus `higher-order/namedFunction*`, `rewriteProbeHelper*`,
`helperCallsHelperRandomArg`, `namedHof*`, `set-witness/absNTopLevelSetWitness`,
`either-maybe/observePredicateParameterLambda`.

Forward chaining still copies one level of a callee's body per invocation:
`getDependentGroups` does not follow equivalence groups, so a `draw` inside a
callee, or an application of a function parameter, has no point inverse in the
tagged copy. Those shapes reach the set-witness engine, which enters them
through the binding instead.

## Point inversion through a deterministic `if`

Forward chaining has no clauses for an `if`, so a variable whose every
occurrence sits in the arms of one had no point inverse:
`draw x = Normal in if 2.0 < 0.5 then [x] else x : [x]`, and the recursive
`step t x = if t < 0.5 then [x] else x : step (t - 1.0) (...)` (task
`witness-through-deterministic-if-over-list-arms`). When the direct inverse
finds nothing and the seed is an `if` whose condition draws no fresh
randomness and holds no occurrence of the variable,
`ForwardChaining.toInvExprMaybeWith` inverts each arm on its own, seeded at the
arm, and selects the two chains field by field with an `IRIf` on the
condition. Nested ifs split recursively. An arm where the variable is dead
leaves the whole split without an inverse.

The condition enters the chain as a free variable (`ifConditionVars`: its
chain name plus the invocation tag). `IRCompiler.bindIfConditions` binds it to
the condition compiled where the body means what it means in the callee
(`enterBindingScope`), so `t < 0.5` reads the call's argument for `t`. The
engine declines when the body can't be entered, when the condition is not in
the body this binding compiles (a leading-argument binding), or when the
condition reads a parameter of a function-valued body. The caller's predicate
admits a condition only when it is `Deterministic` after re-inferring the
recovered variables. A cumulative query never splits, because the point path
refuses a variable read more than once, and the set-witness engine splits the
same `if` for it. The modality verdict (`isWitnessedLambda`) accepts the same
split when the observation reaches the lambda's body.

The per-invocation copy (`getDependentGroups`) steps into the arms of an
`if` whose condition has no random leaf (`ifChildren`), and only into those
arms. Before this, a callee whose body is an `if` had an empty copy. Copying
every `if`'s arms and condition made the copies of a recursive body whole,
which cost 5x on `known-issues/markovBranchRandomRateCompileGrowth`.

An `ANY` in the witnessing slot of an if-rooted program stays a runtime
refusal: observation masks stop at an `if` root (`observation-masks.md`).
Corpus `conditionals/witnessThroughDetIf*`, `distributions/ouChainRecursive`.

## Forward chaining never re-derives a chain name it already has

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

That indicator contributes no dimension, but the density it multiplies was
taken in the witness slot's coordinate alone: the support's speed in the
other coordinates is never accounted for. The number is the density in that
slot's chart, not the density with respect to the support's Hausdorff measure,
and the same distribution written with its slots swapped or rescaled reports a
different one (`(x, x*2.0)` gives 1.0, `(x*2.0, x)` gives 0.5, the ℋ¹ value
is 1/√5). Which convention is right is design
`compositional-gramian-hausdorff-measures`' call. Until then the compiler warns
(`ChartDependentDensity`, `docs/pipeline-and-types.md` "Compile-time
warnings"): `CompileWarnings.chartDependentClasses` reports each group of
`Float` slots that depends, continuously, on fewer primitive draws than it has
slots, naming the draws and the slot each is recovered through
(`ForwardChaining.witnessPath`). Counting draws bounds the support's dimension
from above, so it misses a rank-deficient map with as many draws as slots
(`(x+y, x+y)`). A group reading a neural output or a drawing function is
skipped. Dependence through a comparison, an integer or an `if` condition does
not count, which keeps the piecewise-isometric `(x, if x > 0.5 then 1.0 else
2.0)` quiet.

## A point inversion's change of variables is its spine's

`toValuePath` hands back every solved clause up to the one concluding the
witnessed occurrence, in topological order: the value-carrying **spine** from
the observed slot (`chainSpine`), plus side computations that recover the
other operands of each inverse step, often other latents (the divisor of a
`mult` inverse, the subtrahend of a `plus` one), plus whatever unrelated
clauses happen to sort earlier. The change of variables (`invCoV`) is the
product of the inverse derivatives along the spine alone
(`ForwardChaining.jacobianClauses`). The joint Jacobian of a point inversion
is triangular, and its determinant is the product of the diagonal entries,
one per latent; a side computation's derivative is another latent's own
diagonal entry, which that latent's witness already carries. A side operand
supplies its value, never its derivative. The cumulative step direction
(`cumulativeStep`) reads the same spine.

Multiplying over the whole path applied a sibling's scaling twice whenever
its recovery sorted ahead of the witness's own: `(a + 3.0*b, 3.0*b)`, a
comparison slot ahead of the slot recovering its operand, and above all an
alias (`draw x0 = z`), which adds a binding level and so reorders the sort.
Where a spine step's value-carrying premise cannot be identified,
`jacobianClauses` falls back to every clause the start needs; no corpus
program reaches that fallback. Corpus: `crossLatentSideOperandJacobian`,
`comparisonSiblingJacobian`, `aliasedDrawScaledSibling`,
`aliasedDrawScaledChain`, `aliasedDrawThroughScalingHelper`,
`doubleAliasedDrawParameterScaledSibling`.

## Several reads of a structured variable merge field by field

A variable read more than once has one inverse chain per read, and
`ForwardChaining.mergeExpr` combines them (the set-witness engine's
`IRCompiler.mergeWitnessValue` does the same for its point witnesses). Two
witnesses that are tuples or constructions with complementary wildcard fields
merge field by field, with the product of their Jacobians; any other pair is
taken as two routes to the same value, and one is kept (`mergeExpr2`: the
first, or the one holding no wildcard; `mergeWitnessValue`: picked at run
time by a shallow `isAny` test). Both tests read the witness's shape off its
syntax, so a read inverted through a structural wrapper hid it: `fst (e,
0.0)` recovers `e` as the first field of the let-bound `(e', ANY)`, a
projection of a let-bound variable, not a tuple. Beside `snd e`'s `(ANY, b)`
it counted as a whole value and won, and the other field went unobserved
(`draw e = (Normal, Uniform) in (fst (fst (e, 0.0)), snd e)` answered at dim
1, and points off the Uniform's support were possible). `isLeft (fst (e,
0.0))` likewise hid its `Left ANY` from the `fromLeft e` read's `Left x`, and
a helper `h q = fst q` hid its tuple the same way.

`ForwardChaining.exposeConstructIR`, applied to every candidate before
either merge, resolves the body under the witness's let prefix through the
variables the prefix binds, `fst`/`snd`/`fromLeft`/`fromRight` of a matching
construction, and an `if` whose arms both resolve, down to the construction
(recursively in its fields, which stay the let-bound names, so nothing is
recomputed). Corpus: `data-structures/fstOfPairWrapperStructuredDraw`,
`sndOfPairWrapperStructuredDraw`, `structuredDrawHelperProjectsField`.
Not covered: a structured variable re-read through an alias (`draw s = t`),
through a helper taking the whole tuple, or through a projecting helper
behind a second helper (task structured-draw-reread-through-binder-drops-field).
