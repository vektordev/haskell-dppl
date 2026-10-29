-- gaussianTrajectory4 with the tuple of its last three states bound by a draw
-- (the rewrite-invariance net's draw introduction at that site); the full
-- point answers gaussianTrajectory4's own row. The equality guard on the
-- deterministic application (\z -> (s1, z)) (s2, (s3, s4)) used to read the
-- third and fourth fields of that four-deep tuple as a callee result's bc
-- and flag ('stripBranchCount'), and compared the last state against the
-- tuple holding it ("Approx can only evaluate on two floats"). Task
-- trajectory-tail-bound-as-tuple-type-error.
p((2.5, (2.1, (1.6, 1.2))), ThetaTree [0.45, 0.2] [])=(13.97119230165127, 4.0)
