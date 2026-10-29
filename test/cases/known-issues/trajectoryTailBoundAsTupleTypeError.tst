-- gaussianTrajectory4 with the tuple of its last three states bound by a draw
-- (the rewrite-invariance net's draw introduction at that site). The point
-- query runs into an interpreter type error, "Approx can only evaluate on two
-- floats: (VFloat 1.2, VTuple (VFloat 1.6) (VFloat 1.2))": an equality
-- guard compares the last state against the tuple holding it. With three
-- steps the same shape answers correctly. Verified on dev at compiler
-- 80ad468, and the same at 9fcdc9f and afb0173. The idealized row is
-- gaussianTrajectory4's own. Task
-- trajectory-tail-bound-as-tuple-type-error.
backends: interpreter
expect-failure: broken
ir-contract: violated "in main__m10_prob: cannot match (Float, Float) with Float"
p((2.5, (2.1, (1.6, 1.2))), ThetaTree [0.45, 0.2] [])=(13.97119230165127, 4.0)
