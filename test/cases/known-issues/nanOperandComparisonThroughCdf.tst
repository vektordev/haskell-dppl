-- A comparison against NaN is False, and generate says so; probability
-- answers p(True) = 1.0. The comparison rule for a deterministic bound
-- measures the other side's CDF at it, and inverting `Infinity - Infinity`
-- through plus evaluates that CDF at an infinite point. The mirrored spelling
-- `(1e400 - 1e400) < 1.0` answers correctly. Verified at 3b72682 on dev,
-- interpreter. Found by the rewrite-invariance net's compare-flip family over
-- arithmetic/nanConstantMixture (TestRewrites.knownDivergences). Docs task
-- nan-operand-comparison-measured-through-cdf.
backends: interpreter, python
expect-failure: broken
p(True) is impossible
p(False)=(1.0, 0.0)
