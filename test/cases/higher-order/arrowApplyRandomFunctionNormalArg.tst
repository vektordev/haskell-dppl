-- A random choice of function applied to a random argument: the mixture
-- 0.5 N(1, 1) + 0.5 N(0, 2), so p(s) = 0.5 phi(s-1) + 0.25 phi(s/2).
-- The inline spelling answers; the let-bound one (draw f = ... in f Normal)
-- is still refused (arrow-lifted-mixture-for-function-values) and the
-- draw-gated one fails at query time (enumerated-sum-over-density-body).
-- Investigation modality-function-space-test-coverage, probe P13.
backends: interpreter, julia, python, batched
p(0.5)=(0.2726997, 1.0, False)
p(2.0)=(0.1814780, 1.0, False)
cdf(1.0)=(0.5957312, 0.0)
