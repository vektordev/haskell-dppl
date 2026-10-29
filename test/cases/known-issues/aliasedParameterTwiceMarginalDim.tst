-- higher-order/rewriteProbeHelperScaledNoise with the parameter aliased
-- twice and no `+ 0.0`: the marginal p((0.5, ANY)) is the Uniform's density,
-- 1.0 at dim 1, and answers 1.0 at dim 0 (interpreter; the same on dev at
-- a36270b). One alias is dim 1. The known-issues/aliasedParameterPlusZero-
-- MarginalDim symptom without the `+ 0.0`. Found by the rewrite-invariance
-- sequence property (seed 20261015: alias-intro twice) once task
-- set-witness-walk-stops-at-identity-injf-wrapper's corpus additions moved
-- what it draws. Docs task aliased-parameter-plus-zero-marginal-loses-dim.
-- Since task named-callee-binding-not-floored (forward chaining's
-- per-invocation copy of f's body follows the draws in it) the direct call
-- `main = f Uniform` answers dim 1; the argument bound by a draw first,
-- `main = draw u = Uniform in f u` (the draw-intro rewrite of that call),
-- still answers dim 0, so the pin moved to it.
backends: interpreter, python
expect-failure: broken
p((0.5, ANY))=(1.0, 1.0)
