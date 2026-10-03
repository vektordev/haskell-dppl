backends: python
expect-failure: broken
p((True, [True, True, True, True, True, True, True, True, True, True, True]))=(0.17433922005000008, 0.0)
p((False, [True, True, True, True, True, True, True, True, True, True, True]))=(5.120000000000003e-08, 0.0)
p((ANY, [True, False, True, False, True, False, True, False, True, False, True]))=(8.75121185e-05, 0.0)
-- Idealized by brute force over the 2^12 readings. `backends: python`
-- because the failure is the emitted module not loading. Found by
-- experiments_nest exact-eig-question-asking. Task
-- chained-answers-exceed-python-paren-depth.
