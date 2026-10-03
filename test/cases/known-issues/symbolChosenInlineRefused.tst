expect-failure: broken
p(True, (0, [0.9, 0.1]), (1, [0.2, 0.8]))=(0.375, 0.0)
p(False, (0, [0.9, 0.1]), (1, [0.2, 0.8]))=(0.625, 0.0)
-- Idealized: 0.25 * 0.9 + 0.75 * 0.2. Found by experiments_nest
-- exact-eig-question-asking. Task symbol-chosen-by-inline-coin-refused.
