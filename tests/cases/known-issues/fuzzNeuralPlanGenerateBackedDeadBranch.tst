-- Found by the neural/plan-enumeration fuzz generator: both `if` arms are the identical literal `[[False]]`, so the result is
-- deterministic regardless of the random condition or the (unused) neural
-- read -- yet compilation still reaches the generate-backed-body guard and
-- crashes. Idealized: p([[False]]) = (1.0, 0). Pinned as `crash` rather than
-- `broken` since a correct row would need the mock-NN logit-envelope
-- parameter shape rather than a bare Symbol literal, which is not confirmed
-- here.
expect-failure: crash
