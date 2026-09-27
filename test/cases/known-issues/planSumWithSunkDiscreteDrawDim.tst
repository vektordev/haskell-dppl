-- A discrete sum reported as a density. DrawSinking moves both draws into the
-- operands of the plus -- (draw scene = readScene sym in numRed scene) +
-- (draw c = Uniform < 0.5 in if c then 1.0 else 0.0) -- so the plus is the
-- ordinary two-random-operand InjF rule, not the plan traversal (the left
-- operand is answered by the plan path, as a single reader). Both operands are
-- discrete and the masses are right, but the result carries dim 1. The count
-- has no DiscreteValues tag (Analysis refuses to tag through the recursive
-- numRed), which is presumably what sends the plus down its continuous
-- inversion. Reachable before task plan-path-coverage-for-over-budget-bodies by
-- the sunk spelling itself (checked at eef878b); found by that task's part-2
-- repro. Idealized: the same probabilities at dim 0.0 (0.5 * P(numRed = v) +
-- 0.5 * P(numRed = v - 1)). Task plan-sum-with-sunk-discrete-draw-reports-density.
expect-failure: wrong-result
p(2.0, (2, [0.3, 0.7, 0.2, 0.8, 0.5, 0.3, 0.2, 0.4, 0.6, 0.3, 0.7, 0.1, 0.6, 0.3, 0.5, 0.5, 0.4, 0.6, 0.25, 0.5, 0.25, 0.35, 0.65, 0.45, 0.55, 0.2, 0.45, 0.35, 0.55, 0.45, 0.35, 0.65, 0.3, 0.4, 0.3, 0.45, 0.55, 0.25, 0.75, 0.15, 0.55, 0.3, 0.6, 0.4, 0.5, 0.5, 0.4, 0.35, 0.25]))=(0.1622774486, 1.0)
p(1.0, (2, [0.3, 0.7, 0.2, 0.8, 0.5, 0.3, 0.2, 0.4, 0.6, 0.3, 0.7, 0.1, 0.6, 0.3, 0.5, 0.5, 0.4, 0.6, 0.25, 0.5, 0.25, 0.35, 0.65, 0.45, 0.55, 0.2, 0.45, 0.35, 0.55, 0.45, 0.35, 0.65, 0.3, 0.4, 0.3, 0.45, 0.55, 0.25, 0.75, 0.15, 0.55, 0.3, 0.6, 0.4, 0.5, 0.5, 0.4, 0.35, 0.25]))=(0.4802906062, 1.0)
p(0.0, (2, [0.3, 0.7, 0.2, 0.8, 0.5, 0.3, 0.2, 0.4, 0.6, 0.3, 0.7, 0.1, 0.6, 0.3, 0.5, 0.5, 0.4, 0.6, 0.25, 0.5, 0.25, 0.35, 0.65, 0.45, 0.55, 0.2, 0.45, 0.35, 0.55, 0.45, 0.35, 0.65, 0.3, 0.4, 0.3, 0.45, 0.55, 0.25, 0.75, 0.15, 0.55, 0.3, 0.6, 0.4, 0.5, 0.5, 0.4, 0.35, 0.25]))=(0.3352492985, 1.0)
