-- Verified at abc449c (and with the short-gaussian-trajectory-module-larger-than-long
-- change, which does not touch it): a Gaussian chain whose first step is
-- re-bound through an alias applies the third step's change of variables twice.
-- p((0.0, (0.0, 0.0))) answers 0.50795 = 2 x the idealized phi(0) * 2 phi(0) *
-- 2 phi(0) = 0.25397. Without the alias (draw s1 = Normal) it is right, and so
-- is the two-step chain with the alias. On the 0.45 / 0.2 trajectory the excess
-- is (1/sigma)^(K-2): 5x at K = 3, 25x at K = 4, 5^6 at K = 8. Found by the
-- rewrite-invariance sweep over let-bindings/gaussianTrajectory4
-- (TestRewrites.knownDivergences). Docs task
-- aliased-draw-chain-scaled-step-double-jacobian.
expect-failure: broken
p((0.0, (0.0, 0.0)))=(0.25397454373696393, 3.0)
p((0.0, (0.5, 1.0)))=(0.09343201322172633, 3.0)
