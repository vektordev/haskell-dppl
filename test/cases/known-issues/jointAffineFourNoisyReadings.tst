-- A Gaussian random walk read through a Gaussian sensor at four steps (a
-- linear state-space model). The joint law of (y1..y4) is N(0, C) with
-- C_ij = min(i, j) + [i == j], so p at the origin is
-- (2 pi)^-2 det(C)^-1/2 = 0.00434410990990631, dim 4. The three-step version
-- compiles and is exact (experiments_nest linear-dynamics-trajectory-mle,
-- noisy_k3, 3.6e-15 vs an MVN oracle); four steps leave s1 sample-only:
-- "... has no affine Gaussian form flowing into one consumer or jointly into
-- at most 3 tuple fields ..." (ModalityInfer.jointAffineMaxSlots = 3).
-- Verified on dev at compiler f16f701. Ticket
-- joint-affine-more-than-three-fields; found by
-- exp-continuous-hybrid-simulation-retest.
backends: interpreter
expect-failure: broken
p((0.0, (0.0, (0.0, 0.0))))=(4.34410990990631e-3, 4.0)
