-- sq-inverse-drops-nonpositive-preimages on a continuous operand: sq's only
-- inverse is the positive root, so the density at 1.0 is half the chi^2_1
-- value (0.120985) and the CDF at 1.0 is Phi(1) = 0.841345 instead of
-- Phi(1) - Phi(-1). Verified at b16b4d9 on dev.
-- Idealized: chi^2 with one degree of freedom.
expect-failure: broken
p(1.0)=(0.2419707, 1.0)
cdf(1.0)=(0.6826895, 0.0)
