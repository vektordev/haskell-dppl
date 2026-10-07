p(True)=(0.34, 0.0)
p(False)=(0.66, 0.0)
cdf(False)=(0.66, 0.0)
cdf(True)=(1.0, 0.0)
-- A Bernoulli whose rate is itself random: after DrawSinking the threshold
-- is `draw b = .. in if b then 0.9 else 0.1`, enumerable and independent of
-- the fresh Uniform, so p(True) = sum_v P(t = v) * cdf_U(v)
-- = 0.3 * 0.9 + 0.7 * 0.1. Used to compile with only `generate` and no
-- diagnostic. Task uniform-below-random-threshold-no-forward.
