p((0.0, 0.0))=(0.079577, 2.0)
p((1.0, 0.0))=(0.048266, 2.0)
p((0.0, ANY))=(0.39894, 1.0)
-- The pair sibling of enumLetGatesFreshMixedDim (task
-- enumerated-sum-over-density-body): the terms' dims are 2 (both slots
-- continuous) and 1 (the second slot the atom 3.0), so the enumerated sum
-- keeps dims up to 2. At (x, 0) the atom's term is impossible and the answer
-- is 0.5*phi(x)*phi(0) at dim 2; with ANY in the second slot both terms are
-- 0.5*phi(x) at dim 1. The row where the dim-1 term outvotes the dim-2 one,
-- p((0.0, 3.0)) = (0.5*phi(0), dim 1), is a mixed atom/density point the
-- sampling sweep cannot estimate, so it is pinned by the TestInternals check
-- enumeratedSumLowestDimWins instead.
