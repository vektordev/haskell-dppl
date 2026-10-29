# Modality, refusals and the admission contract

How ModalityInfer decides what a node can do, how a refused variant is represented, and the contract between ModalityInfer and IRCompiler.

## Modality: the layer `PType` projects from

`PType` is not the probabilistic type system but a flat, lossy projection of
one: `Typing/Modality.hs` carries a capability lattice (subsets of
`{CanSample, CanDensity, CanIntegrate, CanExact}`) crossed with orthogonal
support-finiteness and distribution-family axes, and `Typing/ModalityInfer.hs`
infers it bottom-up before `projectGround` flattens it onto the five `PType`
rungs. Read those two modules before changing what an expression is allowed to
do — notably, `PNormal` and `Integrate` are the same capability rung differing
only by family, and `Bottom` is a collapse of four distinct levels.

The finiteness axis `Fin` means **enumerable domain** and nothing else:
`Finite` exactly when the node carries a `DiscreteValues` tag with no
continuous leaf (`Analysis.enumerableDomain`, the one predicate every
enumeration equation in IRCompiler also reads). A node whose type merely has
finitely many inhabitants (an untagged `Bool`) is `Infinite`. `Fin`'s one
reader is `marginalize`'s `keepD` (a finite side makes the marginal density a
finite sum), and only an enumeration can cash that promise. A random `if`
condition does not go through `marginalize`: its rule (`mixtureGround`)
mirrors the codegen, which weights each arm by `p(cond)` and its complement,
so it needs the condition analytic but never finite.

## An `if`'s arms see a gated variable's conditioned law

`ModalityInfer` infers the two arms of an `IfThenElse` under an environment in
which every *random* let-bound variable the condition reads is rebound to its
law **given the condition** (`conditionEnv`/`conditionI`). In
`let s = Normal in if s < 0.0 then x else y`, the `s` that `x` sees is the
Normal's negative part: a truncated law that keeps every capability the
standalone law had (its density is the original restricted and renormalised,
its CDF the original shifted and rescaled) but belongs to **no family** and is
**no longer witnessed** on that arm (`IWit` says the observation determines
the value on every path; inside one arm it does so only if that arm recovers
it). The condition itself is inferred under the unrefined environment, and a
deterministic condition conditions nothing.

Without this, the arm occurrences were bound at the standalone witnessed
`PNormal`, so the family rule typed `s + Normal` inside an arm as `PNormal`
and `sim_fpi s2 thetas` (a recursive call threading `s2` into a further draw)
as `Integrate`: the program was admitted, the set-witness engine refused it at
compile time ("draws fresh randomness"), and because that refusal is eager it
took the `generate` variant down with it. The sum of a truncated Normal and a
Normal has no closed form any engine implements (one level is an `erf`
expression; the nested stopping-time shape is an orthant integral), so the
honest verdict is `Bottom`: `generate` compiles, `probability` is declined by
`missingVariant`. The shapes that *do* have an engine — the gated value
returned as itself, an affine image of it, a tuple of such parts — keep
`Integrate` and their existing set-witness answers
(`test/cases/distributions/gatedContinuousTruncated`, `letProbAbsNormal`).

The refinement keys off the condition's free variables, not off the
`v < bound` spelling, so `if isNeg s`, `if s * s < 1.0` and `if s < w` all
condition `s`. Pinned by the `conditioning` group in `test/TestModalityInfer.hs`
and `Rejection.GatedContinuousFeedsFreshDraw`.

The same task fixed the Lambda rule's annotation: a curried `f x y = …` node
projected its body — the inner lambda's Dirac closure — as `Deterministic`
whatever the result was, and IRCompiler's variant gate reads exactly that
node's `pType`, so a two-parameter function with a `Bottom` body still had a
probability function compiled (and crashed in it) where its one-parameter
twin was declined. `projectNode` now recurses down the arrow spine, as it
already did for a `Var` referencing the function; IRCompiler's `pt` and
`ptUnderLambdas` therefore agree.

**An observed `if` under a deterministic condition passes the observation to
its arms** (task `tensor-gaussian-heads-rd-diffusion`). The witness question
of a binding (`isWitnessedLambda`) is seeded at the context's observed node
(`icObs`), the declaration root. When that root is an `if` whose condition's
law is `Exact`, each arm is inferred with `icObs` set to the arm: whichever
arm runs, its value is the observation, and IRCompiler compiles each arm
against the same sample. Without it, the recursive call in
`step t x = if t < 0.5 then [x] else x : step (t - 1.0) (mu x)` bound its
parameter unwitnessed (the observation could not reach the else arm through
the `if`), so the inner `mu x` read a random input and the trajectory was
`Bottom`. Arithmetic steps such as `distributions/ouChainRecursive` never
showed it: an unwitnessed Gaussian argument still gives a Gaussian.

## Recovered variables are re-inferred, not re-typed

Once an engine fixes a variable's value -- the point-witness fold recovering it
from the observation, an enumeration loop binding it, a residue factor fixing
it at its witness -- the rest of the compile must see it as `Deterministic`.
`IRCompiler.reinferRecovered` does that by re-running the modality engine
(`ModalityInfer.reinferGiven`) on the body, with the recovered names bound
`Exact` (task `reinfer-body-under-recovered-bindings`, design
`law-carrying-modality` M1). It replaced `retypeDetGiven`, a syntactic
re-typing of the names and the pure `InjF`/`if` nodes over them that did not
follow a binder: after `draw y = x * 2.0` with `x` recovered, `y` kept its
standalone `PNormal`, and the Gaussian catch-all handed `Var y` to
`toIRNormalParams` (rows 7-9 of the design's evidence table, and
`let-bindings/letAliasRandomBinding`/`accumulatedPosition`).

The environment is the one `inferE` had at the target's position, rebuilt by
`envAt` from its declaration's root with the same binding helpers
(`bindParam`, `lambdaParamMod`, `conditionEnv`), so enclosing binders that
were not recovered keep their laws. A pin binds `Exact` at every binder of its
name on the way down and is also bound outright, which covers a loop variable
with no source binder (`enumerateCurriedArgument`'s, or a parameter
`enumerateAppliedLambda` renamed). The top-level summaries are computed once
per compile (`CompilerMetadata.reinferContext`).

### Laws and certificates

The engine's environment and results are `Law`s: the capability summary
(`IMod`, which still projects to the `pType`) plus a justification -- a Dirac
(with its value where it is statically known), a primitive leaf, a field
constructor over its fields' laws, or none yet (design `law-carrying-modality`
§A-§B, milestone M3). `inferProgram` emits one per node (`LawTable`, by chain
name), which `compile` threads into `CompilerMetadata.lawTable`; the compiler
also keeps `lawEnv`, the laws of the binders enclosing the code it compiles,
extended at every `Binding` by `bindingLawEnv`, which is `inferE`'s own binder
rule (`bindParam`). Nothing dispatches on either yet. `-d` prints each node's
justification after Modality Inference.

A Dirac's value is known for a constant, a single-valued enumeration domain,
a product with a zero factor, an `InjF` whose operands are all points of known
value (its forward function evaluated on them, `foldedValue`: `(0.0 * z) +
0.0` is the point 0.0), `fst`/`snd` of a pair whose projected field is a known
point (`projectedLaw`), and a call whose callee's result does not depend on
its arguments. That last fact is the callee's own law, `JReturns n j`: the
justification `j` of a lambda's body under its parameter's representative law,
kept where it is a known point or a constructor, with every field's fact other
than a known point or a nested constructor dropped (`argumentFree`; an affine
form or a plan read names nodes of the callee's body, which every call would
share), and `n` the arguments still to apply. `h z = 0.0 * z` returns the
point 0.0, and `h z = (0.0 * z, Normal)` a pair whose `fst` is that point. The
compiler measures any non-literal node of known point from that value
(`IRCompiler.lawPoint`).

`lawEnv` holds a binding's law as the modality engine issued it. A variable an
engine then recovers or enumerates is pinned through `recoveredVars` and
`reinferRecovered`, not in `lawEnv`.

Two things moved with it:

- **The sink test counts uses through binders.** The witness fold treats a
  binding as a sink (an ANY-valued witness is absorbed) only if its value
  reaches one place. Forward chaining's occurrence count is syntactic, and the
  stale type used to veto an alias anyway. Now `draw y = x in (y, y + 1.0)`
  has no random source left once `x` is recovered, so `usesThroughBinders`
  counts `x`'s uses through `y`; without it `(ANY, 1.5)` evaluated
  `VAny + 1.0` instead of refusing (`TestInternals`, ANY refusal group).
- **The deterministic-application arm compares with `equalityGuard`.** It
  used a bare `OpEq`, exact on floats and blind to a nested `ANY`, while every
  other deterministic leaf is compared float-tolerantly and field by field.
  More `let`s reach that arm now (`let-bindings/drawConstNestedAny`,
  `distributions/floatEqualityBehindHelperCall`).

A **single-use** binding whose witness is a wildcard -- the recovered value is
ANY, or a step of the inverse chain read one (`invReadsAny`) -- is no longer
refused: its one occurrence lies under an ANY slot of the observation, so the
witness fold answers with the body's own inference with the binding left
random, never evaluating the occurrence (task `fuzz-admission-oracle-bugs`
item 8: `snd (draw h = Uniform in (exp h, True))` used to answer p(True) = 0,
the optimizer having folded `exp`'s applicability guard on the sentinel into
"impossible"). The inverse's domain guard is not asked of an unevaluable
witness, and the optimizer now picks an `IRIf` arm only on a Bool constant. A
multi-use binding keeps the refusal.

### Engine applicability, and the floor on a binding no engine handles

Each engine of a probabilistic application answers whether it applies with a
pure predicate that returns its certificate, and the modality engine's let
rule and IRCompiler's dispatch read the same predicates (task
`engine-applicability-as-data`, design `law-carrying-modality` M5). In dispatch
order:

| engine | predicate | certificate |
|---|---|---|
| enumeration | `Analysis.enumerableApplication` (a conditional head, `isConditional`, over a random enumerable argument) | the domain |
| plan-guided enumeration | `AutoNeural.planReadOf` (a neural read whose declaration yields a plan) | the network |
| point inversion | `ForwardChaining.pointWitnessCert` (`toInvExprMaybe`, seeded at the lambda's body) | the inverse, and the root-seeded witness verdict |
| affine marginalisation | `ModalityInfer.affineBindingCert` (an affine form with latents, every use flowing into one affine consumer) | the form |
| joint affine marginalisation | `ModalityInfer.jointAffineBindingCert` (an affine form with latents, read by a spine of affine bindings ending in a tuple of at most 3 affine fields) | the form |
| set-valued witnesses | `ForwardChaining.worldsShape`, `invertToWorlds`' shape walk without its IR | the shape |
| in place | `Lang.readOnceInPlace` (the body reads the variable once, under no lambda and in no nested `let`'s body) | none: the argument is measured at the read |

For a `draw` (a lambda in place) whose argument is random, not a function of
witnessed variables alone (`determinedByWitnesses`), and read by the body,
`letBinding` lists the certificates on the applied lambda (`JBinding`, shown
by `-d`, and per binding by `-v`). Where the list is empty it binds the
variable sample-only and re-infers the body, so the function is `Bottom`: no
inference variant is promised, and `bindingWithoutEngine` records the reason
on the absent variants. The order is stated once, as the constructor order of
`ModalityInfer.Engine` (`engineOrder`): `bindingCerts` lists certificates in
it and `applyBinding` tries its constructions in it (`dispatchEngines`).
Enumeration is tried earlier, at the `Apply` arm's first equation; the
in-place engine is tried last, after the set-witness engine's fallback (which
can answer where its predicate declined).

**The in-place engine** (task `dispatch-on-law-certificates`, law-carrying-modality
M6). A binding whose body reads its variable once, under no lambda and in no
nested `let`'s body, has the argument's own law at that read, which is how
`bindParam` types the read anyway. So `body[x := arg]` is what the binding
denotes, and the engine compiles that (`inPlaceApplicable`; only for a lambda
in place compiled inline, so every node on the way is compiled from this
tree). It is an engine with a certificate (`CertInPlace`), last in the order,
not a source rewrite: a binding any other engine measures keeps that engine's
code. The set-witness walk uses the same predicate to enter an inner binding
whose body holds x (`draw c = x < 0.5 in if c ..`, `draw z = 0.5 in x < z`):
it walks the body with the value in place, in `worldsShape` and
`invertToWorldsStep` alike. Corpus `let-bindings/drawSingleReadInPlace*`,
`set-witness/setWitness*InPlace`. Two reads (`draw x = Normal in x + x`) are
never in place; the affine engine owns that.

**Why this order** (acceptance 6 of `dispatch-on-law-certificates`, measured at
`1a09132` plus the in-place engine). For each pair of engines whose
certificates both appear on some binding of a corpus program, the corpus
programs where they do were compiled to Python with the second engine moved
just ahead of the first, and their `.tst` rows run (End2End, interpreter,
against a control run in the current order). An engine that answers is
"first applicable wins", so the swap only matters where both apply:

| seam (current order) | co-apply | swapped order: code changed, size | variants lost / gained | `.tst` rows newly failing |
|---|---|---|---|---|
| enumeration < plan | 92 | 61, +9.1 MB | 1 / 2 | run exceeded 8 GB (the 423x plan pessimisation under budget, see `enumeration.md`) |
| enumeration < point inversion | 11 | 11, +91 KB | 9 / 1 | 1 program |
| enumeration < set-valued witnesses | 74 | 70, +373 KB | 33 / 2 | 15 programs |
| enumeration < in place | 83 | 69, -701 KB | 7 / 2 | 1 program (run incomplete) |
| plan < point inversion | 14 | 10, -20 KB | 1 / 0 | 1 program |
| plan < affine, plan < joint affine | 1 | 0 | none | none |
| plan < set-valued witnesses | 50 | 20, -218 KB | 10 / 0 | 7 programs |
| plan < in place | 87 | 46, -680 KB | 11 / 1 | 4 programs, 2 lose probability (run incomplete) |
| point inversion < affine | 20 | 19, -8 KB | none | none |
| point inversion < joint affine | 30 | 27, -211 KB | none | none |
| point inversion < set-valued witnesses | 110 | 97, +8.1 MB | 24 / 2 | 20 programs |
| point inversion < in place | 77 | 66, -364 KB | 4 / 1 | 2 programs |
| affine < joint affine | 28 | 11, -23 KB | none | none |
| affine < set-valued witnesses | 27 | 5, -6 KB | 1 / 0 | 1 program |
| affine < in place | 34 | 9, -20 KB | none | none |
| joint affine < set-valued witnesses, joint affine < in place | 29, 32 | 0 | none | none |
| set-valued witnesses < in place | 159 | 33, -92 KB | 1 / 3 | none |

Every seam the current order wins on answers or capability is kept for that
reason. Four make no difference to answers or refusals, only to code size,
and there the alternative is smaller: point inversion < affine and < joint
affine, affine < joint affine, affine < in place. Set-valued witnesses < in
place trades one variant for three. The order stays as it is (the in-place
engine last moves no code of a program another engine measures); flipping
those seams is a separate change. The enumeration rows are approximate: the
measurement build moved enumeration into the binding list, where the
`Apply` arm's earlier equations normally take it.

The plan traversal and the set-witness IR can still decline what their
predicate admits (a transported sentinel, an x-free factor reading a random
local, a plan node outside the traversal), so their predicates are necessary
conditions and the refusal stays the net. The predicates are permissive where
the compiler might know more: a part with no fresh randomness of its own counts
as deterministic (`permissiveDet`), since an enclosing variable may be
recovered by the time the body is compiled. A named callee's binding is not
floored, so a call no engine handles is still admitted and refused. The plan
closed form of `compareGround` is the plan certificate too: both operands must
project from plan reads through bindings (`JPlan`, `planDependent`), where
any declaration containing a `ReadNN` used to qualify.

## A static refusal is an absent variant, never a compile-killing error

When an engine declines a shape -- the set-witness diagnostic, a plan
traversal's decline carried in it, the `toIRInference` catch-all ("found no
way to convert to IR"), the Bottom-argument `Apply` arm, the InjF form checks,
the generate-backed enumeration guard, the Normal/LogNormal parameter
extractors, a CDF call under an extra semiring -- it calls `Semiring.refuse`
rather than `error` (task `static-refusals-become-absent-variants`, design
`pipeline-coherence` P1). `CompilerMonad` wraps
`WriterT [...] (ExceptT VariantRefusal Supply)`: the `ExceptT` sits *under*
the writer so a refusal passes through every `scoped` sub-scope. `runCompile` answers `Either`, and
`envToIRUnoptimized'` turns a `Left` into an absent variant whose reason is
kept in `IRFunGroup.refusedVariants` (keyed `gen`/`prob`/`integ`/`normal`/
`writeLogits`) -- the same observable as a `Bottom` verdict, so `generate`
survives a refused `probability`. `Prelude.missingVariant` prints the recorded
reason. `propagateRefusals` then refuses, to a fixed point, every variant that
calls a refused one (`main_prob` calling a refused `f_prob`), naming the callee
and its reason, so no backend emits a call to a function that was never
written (`Rejection.RefusedVariant`).

A `Bottom` verdict records a reason the same way (`intractableRefusal` in
`envToIRUnoptimized'`): the first that applies of a comparison with no closed
form (`comparisonWithoutClosedForm`), a binding no engine applies to
(`bindingWithoutEngine`), and otherwise the node the `Bottom` starts at
(`bottomOrigin`: the `Bottom` node none of whose operands is `Bottom`, a
curried call counted as one node), named with its source position and its
operands' laws. `Normal + Uniform` answers "`+` at m.ppl:1:8 has no inference
rule for its operands Normal (Gaussian) and Uniform (random)".

A few sites *catch* a refusal instead of propagating it, where an engine
tries an alternative after a failed attempt: the cumulative atom of a point
inverse (`pointInverseCoV`), a call whose leading argument is bound only when
compiling through the callee refuses, and the open-body marginal of the
body-factor fold. Refusals are otherwise
eager where the old `error`s were lazy, so a refusing sub-compile whose result
an engine then discards now refuses the variant; the corpus showed no such
case. Query-dependent
refusals stay runtime `IRError`s: the ANY-marginal refusal in the body-factor
fold has no static answer. What is left as `error` in `IRCompiler` is an
internal invariant, each commented as such; three of those are reachable and
filed (`Could not find name in TypeEnv`, `Comparison not implemented for type:
TArrow`, `More than one probabilistic argument`).

## The admission contract

The modality engine and IRCompiler answer "can this be inferred?"
independently (design `pipeline-coherence`, F2). The contract between them:
**a top-level function whose own `pType` is admitted (`Deterministic`,
`PNormal`, `PLogNormal`, `Integrate`) compiles probability and integrate
functions that evaluate, at a point from its own `generate`, to a value or a
refusal; a `Bottom` one still generates.** `test/AdmissionOracle.hs` checks it
per function (helpers at canonical arguments), reading the verdicts from
`Prelude.admissionTyped` -- the program exactly as the variant gate reads it,
so the verdict is known even when the compile crashes. Four buckets: value,
refusal (a `Left`, a `VError`, or an `IRError` the interpreter raises -- the
one exception that is not a crash, recognised by its `Error during
interpretation:` prefix), promised-absent (below), crash. A crash is the
violation.

`prop_Fuzz_AdmissionTotality` (Slow) runs it over the typed generator, with
`knownAdmissionCrashes` excepting filed crash families by message, each
naming its doc. Task `fuzz-admission-oracle-bugs` fixed the nine families it
was seeded with and emptied the list down to one open doc,
`function-value-compared-in-probability-mode`; an entry is removed in the
commit that fixes its family, and a family that resurfaces under a removed
needle is a new finding, not noise -- lifting item 2's needle exposed the
commonest arrow-generator crash, which had been hiding under it. Two
mechanisms behind the families that went with it: the set-witness engine
builds an interval target only for a scalar result (a cumulative query of a
list compared lists with `<`), and the `hasAnyExcept` (`==`/constructor-test)
InjF arm requires exactly one probabilistic operand, with `==` of two random
enumerables compared on the forward grid instead. An admitted variant the IR
compiler *refused* (absent, with a recorded reason) is **promised-absent**
(`AdmissionOracle.overPromises`): not a crash, but the lattice over-promising
in its graceful form, which is a bug of its own (task
`admission-oracle-promised-variants-present`). The property fails on one
under the label `LATTICE OVER-PROMISE` unless its reason matches a filed
family in `knownOverPromises` (keyed by refusal-site message, each naming its
doc; today all are items of `fuzz-admission-over-promises`). When that landed,
about half of the admitted inference evaluations were over-promises. An
admitted variant absent with *no* recorded reason is still a crash-class
violation (the variant gate disagreeing with the verdict). A whole compile
answering `Left` after typing succeeded stays in the refusal bucket. The default-suite `Admission oracle` group pins the oracle
itself, including on the historical mixture-Fin repro. There is no corpus twin: over all 443
corpus programs the oracle finds nothing, and none of them is `Bottom`, so the
corpus cannot exercise half the contract (measured when the task landed).
