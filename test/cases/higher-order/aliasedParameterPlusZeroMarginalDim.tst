-- higher-order/rewriteProbeHelperScaledNoise with the parameter aliased, the
-- noise drawn into a binding, `+ 0.0` added, and the argument bound by a draw
-- first (the draw-intro rewrite of `main = f Uniform`). The marginal
-- p((0.5, ANY)) is the Uniform's density, 1.0 at dim 1. It answered dim 0:
-- the witness chain of u held steps toward other occurrences, and the
-- wildcard test over them read the ANY slot, so u took the
-- unevaluable-witness route and lost its own factor. Found by the
-- rewrite-invariance sequence property (seed 20261017); was a known-issues
-- pin. Docs task aliased-parameter-plus-zero-marginal-loses-dim.
p((0.5, ANY))=(1.0, 1.0)
