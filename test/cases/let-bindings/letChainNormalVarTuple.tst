-- The tuple twin of letChainNormalVar: the same let-chained PNormal Var, now
-- read twice, once through a comparison. y ~ N(1, 1), and the first slot is
-- determined by the second.
--
-- The two mismatched rows carry (0.0, 1.0, False), not `is impossible`: the
-- failed comparison zeroes the probability through an indicator without
-- raising the structural flag. That is the long-standing behaviour of this
-- path, not something this program's fix introduced -- the Uniform twin
-- (`draw x = Uniform in draw y = x + 1.0 in (y > 1.5, y)`), which compiles
-- unchanged, answers identically.
backends: interpreter, julia, python, batched
p((True, 0.5))=(0.3520653, 1.0, False)
p((True, 1.0))=(0.3989423, 1.0, False)
p((False, -1.0))=(0.05399097, 1.0, False)
p((False, 0.5))=(0.0, 1.0, False)
p((True, -1.0))=(0.0, 1.0, False)
