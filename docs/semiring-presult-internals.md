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

`enumSumP` reports a **mass**: dim 0, flag derived from the summed value.
That is only right when every enumerated term is one. `enumMixP` is the
enumerated *mixture* of a scalar real value: each term keeps its own dim and
flag, and the fold follows `mixWith`'s rule (impossible terms dropped, a
possible atom outvotes any density, equal dims sum). It decides "lowest dim"
by an `ROpAdd` count of possible dim-0 terms rather than a max/min reduction,
because the batched backend refuses `ROpMax`; that is sufficient only because
a scalar's dim is 0 or 1. Its one caller is the mixed enumerate-and-shift/scale
rule, whose "continuous" operand is known only to be a `Float` -- it may be a
plan-answered discrete count or an atom/density mixture (task
plan-sum-with-sunk-discrete-draw-reports-density; corpus
`plan-enumeration/planSumWithSunkDiscreteDraw`,
`arithmetic/plusEnumMixedAtomDensity`).

`rProb` is a newtype `P` that only `SPLL.Semiring` can construct, so
`IRCompiler.hs` must route probabilities through a Semiring-aware
combinator or one of two escape hatches: `unsafeLinearP` (a deliberately
linear-only subsystem — no call site uses it today) or `sealP` (bespoke
`PResult`s assembled from already-trusted values). Grepping `unsafeLinearP`
is the "which subsystems ignore `logSpace`" audit.

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
- **Not everything is semiring-aware.** The `ReadNN`/AutoNeural read-logits
  network's inference function (`<nn>_auto`) stays linear-only under
  `logSpace`. Neural programs are outside `Corpus.LogSpaceMatchesLinear`'s pool
  altogether; End2End's `PlanEngineLogSpaceMatchesLinear` checks the neural
  corpus at budget 0 (the plan engine) and skips the programs that still reach
  `_auto` (`End2EndTesting.readLogitsLinearOnly`). Branch *counts* stay linear
  everywhere.
- **A linear quantity with no native log leaf** — a sum of softmax slot
  probabilities, a `|change-of-variables|` factor — enters the semiring
  through `fromLinearSR`. A CDF difference is `measureDiffSR`, not `srMinus`:
  `srMinus` is the AnyExcept operator, undefined under max-product, while an
  interval's mass is an integral in every family. Log space's difference is
  only defined for a non-empty interval, so test emptiness on the operands
  (the CDF is increasing), never on the difference. A sum of many
  alternatives outside `mixP` is `sumAllSR`, which let-binds operands and
  partial sums wherever `srPlus` reads its operands twice.
