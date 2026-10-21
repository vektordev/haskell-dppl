-- An alias of a witnessed draw, read through a helper whose second field
-- scales a fresh draw by the parameter: 1 * N(b; 0, a) = phi(b / a) / a.
-- The |1/y| change of variables of `y * Normal` was applied twice (the
-- outer witness's Jacobian multiplied the side recovery of the Normal; docs
-- task aliased-draw-through-helper-scaled-by-parameter-double-jacobian).
-- Found by the rewrite-sequence property on
-- higher-order/rewriteProbeHelperScaledNoise: alias introduction, then
-- helper extraction.
p((0.5, 0.2))=(0.73654028, 2.0)
p((0.25, -0.1))=(1.47308056, 2.0)
