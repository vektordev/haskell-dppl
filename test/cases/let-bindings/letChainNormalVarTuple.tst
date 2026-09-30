-- The tuple twin of letChainNormalVar: the same let-chained PNormal Var, now
-- read twice, once through a comparison. y ~ N(1, 1), and the first slot is
-- determined by the second.
--
-- The two mismatched rows are impossible: the first slot contradicts the
-- second. They used to carry (0.0, 1.0, False), because y kept its stale
-- PNormal after x was recovered and the failed comparison zeroed the
-- probability without raising the structural flag. Since task
-- reinfer-body-under-recovered-bindings re-infers the body, `y > 0.0` is a
-- deterministic comparison whose failure raises it. The Uniform twin
-- (`draw x = Uniform in draw y = x + 1.0 in (y > 1.5, y)`) changed with it
-- and still answers identically.
backends: interpreter, julia, python, batched
p((True, 0.5))=(0.3520653, 1.0, False)
p((True, 1.0))=(0.3989423, 1.0, False)
p((False, -1.0))=(0.05399097, 1.0, False)
p((False, 0.5)) is impossible
p((True, -1.0)) is impossible
