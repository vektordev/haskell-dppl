-- The random argument comes first, so the application compiled at `mk Normal`
-- returns a closure over y; the folded body factor lives inside that closure
-- (task named-function-list-head-witness-not-recovered).
p([0.0, 1.0])=(0.39894228, 1.0, False)
p([0.5, 1.5])=(0.35206533, 1.0, False)
p([0.0, 2.0]) is impossible
