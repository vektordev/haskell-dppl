expect-failure: diagnostic "Forward chaining failed to find a solution"
p([True, True], [0, 1])=(0.18, 0.0)
p([False, True], [0, 1])=(0.42, 0.0)
p([True, True], [0, 0])=(0.3, 0.0)
p([True, False], [0, 0])=(0.0, 0.0)
-- Idealized: h is ONE draw shared by every element, so asking field 0 twice
-- gives the same answer twice (the [0, 0] rows), unlike independent draws.
-- Found by experiments_nest exact-eig-question-asking. Task
-- map-lambda-over-shared-draw-refused.
