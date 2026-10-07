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
`PNormal`, so `tryNormalClosure` typed `s + Normal` inside an arm as `PNormal`
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
(`letBoundMod`, `lambdaParamMod`, `conditionEnv`), so enclosing binders that
were not recovered keep their laws. A pin binds `Exact` at every binder of its
name on the way down and is also bound outright, which covers a loop variable
with no source binder (`enumerateCurriedArgument`'s, or a parameter
`enumerateAppliedLambda` renamed). The top-level summaries are computed once
per compile (`CompilerMetadata.reinferContext`).

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

## A static refusal is an absent variant, never a compile-killing error

When an engine declines a shape -- the set-witness diagnostic, a plan
traversal's decline carried in it, the `toIRInference` catch-all ("found no
way to convert to IR"), the Bottom-argument `Apply` arm, the InjF form checks,
the generate-backed enumeration guard, the Normal/LogNormal parameter
extractors, a CDF call under an extra semiring -- it calls `Semiring.refuse`
rather than `error` (task `static-refusals-become-absent-variants`, design
`pipeline-coherence` P1). `CompilerMonad` is
`WriterT [...] (ExceptT VariantRefusal Supply)`: the `ExceptT` sits *under*
the writer so the many `lift (runWriterT ...)` sub-scopes keep their shape and
a refusal passes through them. `runCompile` answers `Either`, and
`envToIRUnoptimized'` turns a `Left` into an absent variant whose reason is
kept in `IRFunGroup.refusedVariants` (keyed `gen`/`prob`/`integ`/`normal`/
`writeLogits`) -- the same observable as a `Bottom` verdict, so `generate`
survives a refused `probability`. `Prelude.missingVariant` prints the recorded
reason. `propagateRefusals` then refuses, to a fixed point, every variant that
calls a refused one (`main_prob` calling a refused `f_prob`), naming the callee
and its reason, so no backend emits a call to a function that was never
written (`Rejection.RefusedVariant`).

One site *catches* a refusal instead of propagating it, because it used to
discard a failed attempt's lazy `error` along with its bindings: the
set-witness inversion (`invertToWorlds`) when it has a fallback (the affine
marginalisation), so the fallback still gets its turn. Refusals are otherwise
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
