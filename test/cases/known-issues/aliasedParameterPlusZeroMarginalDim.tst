-- higher-order/rewriteProbeHelperScaledNoise with the parameter aliased, the
-- noise drawn into a binding and `+ 0.0` added. The marginal p((0.5, ANY)) is
-- the Uniform's density, 1.0 at dim 1; verified on dev at 5ebe3dc
-- (interpreter) this answers 1.0 at dim 0. Without the `+ 0.0`, or without
-- the alias, it is dim 1. Point queries are right. Found by the
-- rewrite-invariance sequence property (seed 20261017: draw-intro,
-- plus-zero, alias-intro). Docs task aliased-parameter-plus-zero-marginal-loses-dim.
backends: interpreter, python
expect-failure: broken
p((0.5, ANY))=(1.0, 1.0)
