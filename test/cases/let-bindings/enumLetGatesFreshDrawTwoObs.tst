backends: interpreter, julia, python, batched
p((True, (True, True)))=(0.216, 0.0)
p((True, (True, False)))=(0.054, 0.0)
p((False, (False, True)))=(0.252, 0.0)
p((False, (True, False)))=(0.042, 0.0)
p((ANY, (True, True)))=(0.244, 0.0)
p((ANY, (ANY, True)))=(0.52, 0.0)
-- Two independent noisy observations of one shared enumerated latent -- the
-- shape of the noisy-oracle question-asking model this task was filed for.
-- Given `b` the two observations are independent fresh draws, so e.g.
-- P(True, (True, True)) = 0.3 * 0.9 * 0.8 = 0.216, and marginalising `b`,
-- P(ANY, (True, True)) = 0.216 + 0.7 * 0.1 * 0.4 = 0.244. Task
-- enum-let-latent-gates-fresh-draw.
