-- higher-order/rewriteProbeHelperScaledNoise with the parameter aliased
-- twice and the argument bound by a draw first: the marginal p((0.5, ANY))
-- is the Uniform's density, 1.0 at dim 1; it answered dim 0, as
-- higher-order/aliasedParameterPlusZeroMarginalDim did. Found by the
-- rewrite-invariance sequence property (seed 20261015); was a known-issues
-- pin. Docs task aliased-parameter-plus-zero-marginal-loses-dim.
p((0.5, ANY))=(1.0, 1.0)
