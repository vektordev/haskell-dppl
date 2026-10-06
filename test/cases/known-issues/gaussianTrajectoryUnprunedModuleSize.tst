-- An 8-step Gaussian random walk queried at its whole trajectory (the
-- program is let-bindings/gaussianTrajectory8). Without --pruneAnyChecks
-- each level's marginal-query handling re-tests the observed slots beneath
-- it, so the module is quadratic in the chain length: 110 KB here at
-- 5c4627b, against 19 KB with --pruneAnyChecks (73 / 110 / 155 KB at
-- K = 6 / 8 / 10, against 15 / 19 / 24 KB). Docs task
-- draw-chain-compile-time-polynomial-in-chain-length.
expect-failure: code-size above 60 KB
