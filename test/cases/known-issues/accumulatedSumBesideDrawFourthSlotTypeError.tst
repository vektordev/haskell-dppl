-- A draw-bound running sum in slot 2, an independent draw in slot 3 and a
-- constant in slot 4. The point query at the origin should answer
-- (2 pi)^-3/2 = 0.06349363593424097 at dim 3 (s1 = 0, s2 = p2 - s1 = 0,
-- s3 = 0; the constant slot is a unit factor). The interpreter instead
-- stops with "Type error: Approx can only evaluate on two floats:
-- (VFloat 0.0,VTuple (VFloat 0.0) (VFloat 0.0))", and the Python module
-- with "unsupported operand type(s) for -: 'float' and 'T'" in isclose: the
-- equality guard on a deterministic slot reads a sub-sample one level
-- short. Inline `s1 + s2` in the tuple, or `Normal` in place of `draw s3`,
-- and it answers. The same error as known-issues/
-- trajectoryTailBoundAsTupleTypeError, reached without a tuple-valued draw:
-- the experiment shape is an in-program position accumulator
-- `draw p_k = p_{k-1} + s_k`, which answers at 3 slots and fails from 4.
-- Verified on dev at compiler f16f701. Ticket
-- trajectory-tail-bound-as-tuple-type-error (second trigger); found by
-- exp-continuous-hybrid-simulation-retest.
backends: interpreter, python
expect-failure: broken
ir-contract: violated "in main__m001_prob: cannot match (a, Float) with Float"
p((0.0, (0.0, (0.0, 0.0))))=(6.349363593424097e-2, 3.0)
