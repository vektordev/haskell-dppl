-- A SILENT wrong number. The plan path's value grouping (psMerge) is enabled
-- when the plan-bound variable occurs once in the observation, but that count
-- does not look inside a specialized callee: here the scene occurs once (the
-- call h scene), and h's body reads its parameter through two full numRed
-- folds. Both folds' results are grouped, each baking the scene's leaves into
-- a summed mass, and intersecting the two multiplies those masses. The inlined
-- twin (main = ... in if numRed scene > 0.5 then numRed scene else 0.0) has two
-- occurrences, keeps grouping off, and answers correctly. Pre-existing (same
-- value at eef878b); found by task plan-path-coverage-for-over-budget-bodies,
-- whose own inner-draw substitution had the same hole and fixed it for that
-- case (planReaderCount). Idealized: p(1.0) = P(numRed = 1) = 0.2900826155.
-- Task plan-value-grouping-double-counts-helper-reads.
expect-failure: wrong-result
p(1.0, (2, [0.3, 0.7, 0.2, 0.8, 0.5, 0.3, 0.2, 0.4, 0.6, 0.3, 0.7, 0.1, 0.6, 0.3, 0.5, 0.5, 0.4, 0.6, 0.25, 0.5, 0.25, 0.35, 0.65, 0.45, 0.55, 0.2, 0.45, 0.35, 0.55, 0.45, 0.35, 0.65, 0.3, 0.4, 0.3, 0.45, 0.55, 0.25, 0.75, 0.15, 0.55, 0.3, 0.6, 0.4, 0.5, 0.5, 0.4, 0.35, 0.25]))=(0.1365466126, 0.0)
