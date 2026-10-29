p(3.0)=(0.5, 0.0)
p(0.0)=(0.19947, 1.0)
p(1.0)=(0.12099, 1.0)
-- An enumerated latent selecting between a fresh Normal and the atom 3.0
-- (task enumerated-sum-over-density-body). Given `b` the terms have
-- different dims, and the enumerated sum follows the binary mixture's rule:
-- the lowest dim among the possible terms wins. At 3.0 the atom's mass 0.5
-- (dim 0) outvotes the density; elsewhere the atom's term is impossible and
-- the answer is the density 0.5*phi(x) at dim 1.
