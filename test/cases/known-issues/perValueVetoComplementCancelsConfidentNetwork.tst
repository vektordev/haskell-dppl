-- lm uniform (0.25 each); lmAnti puts 1.0 on token 1 and 1e-9 on each other
-- token (unnormalized on purpose: in float32 a softmax of 1 - 1e-9 rounds to
-- 1.0 with ~3e-10 on the rest, and the harness's float64 needs the exact 1.0
-- to show the same cancellation). The veto event (1, True) means c /= 1, so
-- the correct mass is 0.25 * (3 * 1e-9) = 7.5e-10, tiny but possible, flag
-- false. The compiler reads it as 1 - raw[1] = 0.0 and flags it impossible.
-- The pinned wrong value is that flag. Control (verified): with 0.999 in
-- place of 1.0 the mass is 2.5e-4 and not impossible. Verified at a38df67
-- (dev), interpreter and python. Task
-- per-value-veto-complement-cancels-confident-network.
backends: interpreter, python
expect-failure: wrong-result
p((1, True),(2, [0.25, 0.25, 0.25, 0.25]),(2, [0.000000001, 1.0, 0.000000001, 0.000000001])) is impossible
