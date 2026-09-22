-- The same limitation as neuralLeafConvolvedWithFreshNormal reached through a
-- comparison rather than a sum: the neural leaf is compared against a
-- *random* threshold, so neither side of the `>` is both plan-dependent and
-- deterministic. Unlike the sum, this one is not silent -- it takes the
-- compile down through `setWitnessApply`'s eager `error`, carrying an
-- accurate diagnostic. The refusal is correct; that it is raised as an
-- exception rather than returned on the `Left` channel is the separate defect
-- tracked by tasks/unwitnessed-gaussian-let-chain-admitted-but-crashes.
expect-failure: diagnostic "comparison: some side is neither plan-dependent nor deterministic"
