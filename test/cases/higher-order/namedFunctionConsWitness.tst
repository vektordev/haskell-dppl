-- A named function whose random argument is a point witness at the head of the
-- list it returns (task named-function-list-head-witness-not-recovered). The
-- let spelling, `draw x = Normal in x : [x + Normal]`, gives the same numbers:
-- p([a, b]) = phi(a) phi(b - a), dimension 2. The rest of the body is folded in
-- by calling f's own probability function at the recovered witness.
p([0.0, 0.0])=(0.15915494, 2.0, False)
p([1.0, 0.5])=(0.08518950, 2.0, False)
p([0.5, ANY])=(0.35206533, 1.0, False)
p([0.0]) is impossible
p([]) is impossible
