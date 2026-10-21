-- `0.0 * z` extracted into a helper: `h` returns the point 0.0 whatever its
-- argument (its law is JReturns), so the call is that point (task
-- dirac-law-point-lost-under-plus-or-helper). It answered p(0.0) impossible.
batched
p(0.0)=(1.0, 0.0)
p(1.0) is impossible
cdf(-0.5)=(0.0, 0.0)
cdf(0.5)=(1.0, 0.0)
