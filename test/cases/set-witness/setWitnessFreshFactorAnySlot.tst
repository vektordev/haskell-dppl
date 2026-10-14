-- The second field is x-free fresh randomness, measured as a factor of each
-- world (worldFactorFree) against its slot of the query. A wildcard slot used
-- to reach that measure as a point: the inverse of exp took log ANY, which
-- raised on every backend, and batched mode (eager selects) raised for the
-- whole bucketed batch. Found by Slow prop_Fuzz_BackendsAgree
-- --quickcheck-replay=1. A wildcard slot is now the factor's marginal, 1.
batched
p((0.2, ANY))=(1.0, 1)
p((0.7, ANY))=(1.0, 1)
p((ANY, 0.3)) is impossible
p((ANY, 2.0))=(0.5, 1)
p((0.7, 2.0))=(0.5, 2)
p((-0.5, ANY)) is impossible
