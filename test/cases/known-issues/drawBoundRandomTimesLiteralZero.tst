-- The sibling of rewriteProbeDrawZeroFactor with the *random* factor bound
-- instead of the zero: `0.0 * Normal` answers p(0.0) = (1.0, dim 0), but
-- verified at 2d50350 on dev this answers (0.0, dim 0) -- the point mass is lost
-- and nothing is flagged impossible. Found by the rewrite-invariance net's draw
-- introduction. Task draw-bound-random-factor-times-literal-zero-loses-dirac-mass.
expect-failure: broken
p(0.0)=(1.0, 0.0)
