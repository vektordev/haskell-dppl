-- A witnessed draw re-bound through an alias, next to a scaled fresh draw in
-- a sibling field. The density is phi(x0) * 2 phi(2 s), the 0.5 scaling's
-- |1/0.5| applied once. It used to be applied twice: the change of variables
-- multiplied every clause of the inversion path, the sibling's recovery
-- included, instead of the spine alone (ForwardChaining.jacobianClauses;
-- docs task aliased-draw-scaled-sibling-double-jacobian). Found by the
-- rewrite-invariance sweep over distributions/ouChainUnrolled.
slow
p((0.0, 0.0))=(0.31830989, 2.0)
p((1.0, 0.5))=(0.11709966, 2.0)
