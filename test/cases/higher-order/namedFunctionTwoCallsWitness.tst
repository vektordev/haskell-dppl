-- Two invocations of one named function, each recovering its own argument
-- (distinct per-invocation tags; task named-function-list-head-witness-not-recovered).
p(((0.0, 1.0), (1.0, 2.0)))=(0.09653235, 2.0, False)
p(((0.0, 1.0), (0.0, 1.0)))=(0.15915494, 2.0, False)
p(((0.0, 1.0), (0.0, 5.0))) is impossible
