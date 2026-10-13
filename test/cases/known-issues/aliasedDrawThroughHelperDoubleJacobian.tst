-- Verified at e0efdc5: an alias of a witnessed draw, read through a helper
-- whose second field scales a fresh draw by the parameter, applies that
-- draw's change of variables twice (2x the density). Without the alias
-- (`main = draw x = Uniform in h x`) or without the helper (`draw y = x in
-- (y, y * Normal)`) it is right. Idealized: p((0.5, 0.2)) = 1 * 2 phi(0.4)
-- = (0.73654028, 2); the compiler answers 1.47308056. Found by the
-- rewrite-sequence property (TestRewrites.knownSequenceDivergences) on
-- higher-order/rewriteProbeHelperScaledNoise: alias introduction, then helper
-- extraction. Docs task
-- aliased-draw-through-helper-scaled-by-parameter-double-jacobian.
expect-failure: broken
p((0.5, 0.2))=(0.73654028, 2.0)
p((0.25, -0.1))=(1.47308056, 2.0)
