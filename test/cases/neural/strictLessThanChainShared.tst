-- A strictly ascending chain of three digit reads, the program-guided
-- diffusion `ascending` constraint (task
-- strict-int-less-than-non-strict-when-operand-shared): x2 is shared by both
-- comparisons, and `x1 < x2` must stay strict once x2 is enumerated. With
-- a = b = [0.5, 0.5] and c = 2, only x1 = 0, x2 = 1 holds (0.25); the
-- inclusive CDF answered 0.75. With c = 1 the chain needs x2 < 1 and x1 < 0,
-- so nothing holds.
p(True, (2, [0.5, 0.5, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]), (2, [0.5, 0.5, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]), (2, [0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]))=(0.25, 0.0)
p(False, (2, [0.5, 0.5, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]), (2, [0.5, 0.5, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]), (2, [0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]))=(0.75, 0.0)
p(True, (2, [0.5, 0.5, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]), (2, [0.5, 0.5, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]), (2, [0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]))=(0.0, 0.0)
