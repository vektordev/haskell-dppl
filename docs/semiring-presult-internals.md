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

`rProb` is a newtype `P` that only `SPLL.Semiring` can construct, so
`IRCompiler.hs` must route probabilities through a Semiring-aware
combinator or one of two escape hatches: `unsafeLinearP` (linear-only
subsystems — set-witness/plan-enum measurement, AutoNeural read-logits reads)
or `sealP` (bespoke `PResult`s assembled from already-trusted values).
Grepping `unsafeLinearP` is the "which subsystems ignore `logSpace`" audit.

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
- **Not everything is semiring-aware.** The `ReadNN`/AutoNeural read-logits network and
  the set-witness/plan-enum continuous measurement machinery build bespoke
  `IRExpr` formulas and stay linear-only under `logSpace`. `Spec.hs`'s
  `logSpaceUncoveredPrograms` lists the corpus programs that reach them and
  so are excluded from the `LogSpaceMatchesLinear` property. Branch
  *counts* stay linear everywhere.
