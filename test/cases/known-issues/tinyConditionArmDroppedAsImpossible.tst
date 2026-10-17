-- if-condition-approx-zero-drops-tiny-branch-mass, scaled so probTolerance
-- can see it: the then-arm's condition has probability 5e-11 and its body a
-- density of 2e10 on [0, 5e-11], so p(2e-11) = 1.0. The interpreter (OpApprox,
-- floatApproxEqThresh 1e-10) and Python (isclose, 1e-9) both treat the arm as
-- dead and answer (0.0, impossible). Verified at b16b4d9 on dev.
backends: interpreter, python
expect-failure: broken
p(0.00000000002)=(1.0, 1.0)
