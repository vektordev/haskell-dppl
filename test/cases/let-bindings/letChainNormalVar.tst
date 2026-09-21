-- The no-function-value-at-all reach of the same toIRNormalParams fallthrough
-- (task modality-arrow-apply-crashes, bug A, added 2026-09-13): the inner `y`
-- is a *local* Var labelled PNormal, which the Normal shortcut has no (mu,
-- sigma) to read off. The Uniform twin always compiled, because point
-- inversion never asks. y ~ N(1, 1).
backends: interpreter, julia, python, batched
p(0.5)=(0.3520653, 1.0, False)
p(1.0)=(0.3989423, 1.0, False)
p(2.0)=(0.2419707, 1.0, False)
cdf(1.0)=(0.5, 0.0)
cdf(2.0)=(0.8413447, 0.0)
cdf(7.0)=(1.0, 0.0)
