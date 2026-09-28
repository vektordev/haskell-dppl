-- A draw-bound Gaussian convolved with a fresh Normal and then pushed through
-- an InjF (`exp`) takes the compile down with the set-witness engine's eager
-- `error` ("set-valued witness construction failed for the binding of 'r'").
-- Each half compiles on its own: `draw r = Normal in r + Normal` (folded to a
-- single N(0, sqrt 2)), `draw r = Normal in exp(r)` (point inversion), and the
-- inline spelling `exp(Normal + Normal)` compiles to the exact lognormal. `r`
-- is read once, so the draw and the inline spelling denote the same
-- distribution: exp(N(0, sqrt 2)), a lognormal with sigma = sqrt 2.
--   p(1.0) = 1 / sqrt(2 pi * 2) = 0.28209479
--   p(2.0) = lognormal(0, sqrt 2) pdf at 2 = 0.12508365
--   cdf(1.0) = 0.5
-- Found by experiments_nest bayes-factor-model-comparison/neural_in_program
-- (its hypothesis C, `2.0 * exp(0.5 * (r + Normal * 0.4)) + 1.0` with `r`
-- draw-bound to a neural Gaussian reading); the neural form is pinned
-- separately as neuralLeafConvolvedThroughExpDrawBound. Docs-repo task:
-- draw-bound-gaussian-convolved-through-injf-crashes.
expect-failure: broken
p(1.0)=(0.282095, 1.0)
p(2.0)=(0.125084, 1.0)
cdf(1.0)=(0.5, 0.0)
