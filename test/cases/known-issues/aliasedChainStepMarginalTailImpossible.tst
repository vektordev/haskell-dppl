-- Verified at 3e87090 (plus the aliased-draw-scaled-sibling-double-jacobian
-- fix, which does not touch it): a four-step Gaussian chain whose third step
-- is re-bound through an alias answers the marginal over the last step as
-- impossible (0.0, flag set). The unaliased chain answers phi(0) phi(0.5)
-- phi(0.5) = 0.04944889 (dim 3), and so does the aliased chain with three
-- steps; the fully observed query (0.0, (0.5, (1.0, 1.0))) is right. Found by
-- the rewrite-invariance sweep over let-bindings/gaussianTrajectory4
-- (TestRewrites.knownDivergences). Docs task
-- aliased-chain-step-marginal-tail-impossible.
expect-failure: broken
p((0.0, (0.5, (1.0, ANY))))=(0.04944889338563758, 3.0)
