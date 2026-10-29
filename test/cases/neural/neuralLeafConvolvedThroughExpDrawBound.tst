-- The neural form of let-bindings/drawGaussianConvolvedThroughExp: a Gaussian
-- neural leaf (reader layout [mu, sigma]) draw-bound, convolved with a fresh
-- Normal, then pushed through `exp`. `r` is read once, so the in-place engine
-- measures `exp((gauge img) + Normal)` at the read (task
-- dispatch-on-law-certificates), the exact lognormal the inline spelling
-- compiles to. Before it, plan-guided enumeration and set-valued witnesses
-- both declined and the compile failed (docs-repo task
-- draw-bound-gaussian-convolved-through-injf-crashes; was a known-issues pin).
-- exp(N(mu, sqrt(sigma^2 + 1))):
--   [0.0, 1.0]: p(1.0) = 0.28209479, cdf(1.0) = 0.5
--   [0.5, 0.5]: p(2.0) = lognormal(0.5, sqrt 1.25) pdf at 2 = 0.17576985
p(1.0, (2, [0.0, 1.0]))=(0.282095, 1.0)
cdf(1.0, (2, [0.0, 1.0]))=(0.5, 0.0)
p(2.0, (2, [0.5, 0.5]))=(0.175770, 1.0)
