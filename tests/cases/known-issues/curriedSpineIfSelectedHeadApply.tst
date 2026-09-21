-- CalleeNormalize's if-in-callee-position rewrite only reaches a
-- single Apply node, so a *curried* two-argument spine headed by an
-- if-selected lambda still crashes instead of distributing into its arms.
-- The condition here is deterministic (0.1 < 0.5 is True), so the idealized
-- result is the density of 1.0 + Normal, i.e. N(1, 1).
expect-failure: diagnostic "should resolve to a lambda"
