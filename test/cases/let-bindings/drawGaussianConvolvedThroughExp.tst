-- A draw-bound Gaussian convolved with a fresh Normal and then pushed through
-- an InjF (`exp`). `r` is read once, with no binder on the way, so the in-place
-- engine measures `exp(Normal + Normal)` at the read (task
-- dispatch-on-law-certificates): the exact lognormal, as the inline spelling
-- compiles. Before it, the set-witness engine's construction failed and took
-- the compile down (docs-repo task
-- draw-bound-gaussian-convolved-through-injf-crashes; was a known-issues pin).
-- exp(N(0, sqrt 2)), a lognormal with sigma = sqrt 2:
--   p(1.0) = 1 / sqrt(2 pi * 2) = 0.28209479
--   p(2.0) = lognormal(0, sqrt 2) pdf at 2 = 0.12508365
--   cdf(1.0) = 0.5
-- Found by experiments_nest bayes-factor-model-comparison/neural_in_program;
-- the neural form is neural/neuralLeafConvolvedThroughExpDrawBound.
slow
p(1.0)=(0.2820947917738782, 1.0)
p(2.0)=(0.12508365099693788, 1.0)
cdf(1.0)=(0.5, 0.0)
