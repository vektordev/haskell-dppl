-- Found while minimizing item 8 of docs task fuzz-admission-oracle-bugs: the
-- same shape with the field projected away by `snd` instead of tested
-- compiles, but answers p(True) = 0 and flags it impossible -- a silent wrong
-- result. `snd (exp h, True)` is True on every draw. Idealized: p(True) =
-- (1.0, 0).
backends: interpreter
expect-failure: broken
p(True)=(1.0, 0.0)
