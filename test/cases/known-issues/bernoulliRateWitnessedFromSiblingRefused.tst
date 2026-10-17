-- A Bernoulli whose rate is a latent the first slot observes exactly. Given
-- the observation p is a point, so `Uniform < p` has a deterministic bound,
-- but the comparison is refused as two random operands. Blocks the
-- Beta-Bernoulli spelling draw p = Uniform in (p, (Uniform < p, Uniform < p)).
-- Unlike uniformBelowCorrelatedContinuousThreshold, p is point-witnessed
-- here, not observed through a set. Verified at b16b4d9 on dev. Docs task
-- comparison-against-point-witnessed-latent-refused.
-- Idealized: p((0.3, True)) = 0.3, p((0.3, False)) = 0.7 (dim 1).
expect-failure: refused "has no closed form for its two random operands"
