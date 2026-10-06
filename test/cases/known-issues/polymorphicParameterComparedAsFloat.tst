-- Verified at bd494ae (dev): a parameter whose type inference leaves
-- polymorphic (nothing in the body constrains it) is compared against the
-- query with OpApprox, the float comparison (IRCompiler equalityGuardBody's
-- TVarR arm, and the cmpOp choices beside it). The interpreter refuses
-- OpApprox on anything but two floats, so every Bool or Int query fails at
-- run time with "Type error: Approx can only evaluate on two floats". Python's
-- and Julia's isclose happen to accept bools and ints (so the pin is
-- interpreter-only). Per-value queries
-- sidestep it by giving their helper a signature (task
-- per-value-query-over-enumerated-slot). Docs task
-- polymorphic-parameter-compared-as-float.
backends: interpreter
expect-failure: broken
p((True, True), True)=(1.0, 0.0)
p((True, False), True)=(0.0, 0.0)
