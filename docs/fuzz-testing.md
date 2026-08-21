# Fuzz testing (`test/TestFuzz.hs`)

`test/TestFuzz.hs` runs randomly-generated SPLL programs
(`test/ArbitrarySPLL.hs`) against the same metamorphic invariants the
hand-written corpus checks in `Spec.hs`'s Corpus group, rather than known
expected values. `genRawFuzzProgram`/`genRawFuzzExpr` cover the full AST
space and are only useful for crash-freedom (almost every draw is
ill-typed); `genTypedProgram`/`genTypedExpr` build well-typed scalar
programs and drive the real invariants (programs validate, P(ANY)=1,
probability is never negative, topK at threshold 0 reproduces exact
inference and at a real threshold never inflates it, branch counting
doesn't change the probability value, and mixtures follow the
dimension-combination rules). Each property caps structural size and
wraps each case in a wall-clock timeout. Since most draws end up with no
probability function to check, every such branch returns `discardVacuous`
rather than `property True`, so QuickCheck's own discard-ratio accounting
reports this honestly instead of it being invisible inside an inflated
success count.

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
