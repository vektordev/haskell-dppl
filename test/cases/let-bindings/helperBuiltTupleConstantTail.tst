-- A deterministic helper builds the four-deep output tuple of a two-step
-- Gaussian chain, with a constant tail: phi(0) phi(0.5) = 0.14045374 at dim 2
-- whether the last slot is observed at its constant or left ANY, impossible
-- off it. The probability function compares mk_gen(s1)(s2) against the
-- query, and 'stripBranchCount' used to read that call's four-deep tuple as
-- a callee's packed result and shift its last two fields: the interpreter
-- raised "Approx can only evaluate on two floats" on the point and answered
-- the ANY row as impossible. Found by the rewrite-invariance net's helper
-- extraction on let-bindings/trajectoryTailBoundAsTuple. Task
-- trajectory-tail-bound-as-tuple-type-error.
p((0.0, (0.5, (1.0, 2.0))))=(0.1404537443096252, 2.0)
p((0.0, (0.5, (1.0, ANY))))=(0.1404537443096252, 2.0)
p((0.0, (0.5, (1.0, 3.0))))=(0.0, 2.0)
