-- The neural form of drawGaussianConvolvedThroughExp: a Gaussian neural leaf
-- (reader layout [mu, sigma]) draw-bound, convolved with a fresh Normal, then
-- pushed through `exp`. Both engines decline and the set-witness engine's
-- eager `error` takes the compile down; the message adds "Plan-guided lazy
-- enumeration was applicable but could not compile the body: unsupported
-- node in plan value enumeration: InjF exp". The inline spelling
-- `exp((gauge img) + Normal)` compiles to the exact lognormal, as do the
-- draw-bound affine shapes (`draw r = gauge img in 1.5 * (r + Normal) + 0.5`).
-- exp(N(mu, sqrt(sigma^2 + 1))):
--   [0.0, 1.0]: p(1.0) = 0.28209479, cdf(1.0) = 0.5
--   [0.5, 0.5]: p(2.0) = lognormal(0.5, sqrt 1.25) pdf at 2 = 0.17576985
-- Docs-repo task: draw-bound-gaussian-convolved-through-injf-crashes.
expect-failure: broken
p(1.0, (2, [0.0, 1.0]))=(0.282095, 1.0)
cdf(1.0, (2, [0.0, 1.0]))=(0.5, 0.0)
p(2.0, (2, [0.5, 0.5]))=(0.175770, 1.0)
