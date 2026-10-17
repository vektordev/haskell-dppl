-- The same shape with the condition probability a run-time parameter,
-- t = 5e-10, between the two thresholds (a literal is folded by the
-- optimizer, whose threshold is the interpreter's). The interpreter (1e-10)
-- answers the right 1.0, while Python's isclose (|a - b| <= 1e-9) drops the
-- arm and answers (0.0, impossible), so the two backends disagree. Verified
-- at b16b4d9 on dev. Docs task if-condition-approx-zero-drops-tiny-branch-mass.
backends: python
expect-failure: broken
p(0.0000000002, 0.0000000005)=(1.0, 1.0)
