-- A draw-bound alias of the callee's parameter passed on to a helper that
-- reads the theta, with the caller binding the alias's name `t2` itself:
-- the anchor resolves to the alias in the entered callee body, and from there
-- to its value, not to the caller's `t2` (theta 5.0). Docs task
-- theta-anchor-through-callee-local-binding.
p(2.5, ThetaTree [5.0] [], ThetaTree [2.0] [])=(1.0, 1.0)
p(5.5, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.0, 1.0)
cdf(2.5, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.5, 0.0)
