-- The all-nullary twin of neuralAdtReadCount: two neural `Red | Blue` reads
-- combined with `++`. Enumerating each read's domain produces the `VADT "Red"`
-- constant the batched backend refused (task
-- batched-backend-refuses-neural-adt-constants); `Color` is a collapsed
-- enumeration there, so its `isRed` test is a per-element mask.
-- Point A: P(Red) = 0.3 and 0.6, so p(0) = 0.7*0.4, p(1) = 0.3*0.4 + 0.7*0.6.
backends: interpreter, julia, python, batched
p(0, (2, [0.3, 0.7]), (2, [0.6, 0.4]))=(0.28, 0.0)
p(1, (2, [0.3, 0.7]), (2, [0.6, 0.4]))=(0.54, 0.0)
p(2, (2, [0.3, 0.7]), (2, [0.6, 0.4]))=(0.18, 0.0)
p(0, (2, [1.0, 0.0]), (2, [0.5, 0.5])) is impossible
p(1, (2, [1.0, 0.0]), (2, [0.5, 0.5]))=(0.5, 0.0)
p(2, (2, [1.0, 0.0]), (2, [0.5, 0.5]))=(0.5, 0.0)
cdf(1, (2, [0.3, 0.7]), (2, [0.6, 0.4]))=(0.82, 0.0)
