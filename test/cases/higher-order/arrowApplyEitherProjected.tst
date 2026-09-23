-- The Either sibling of arrowApplyTupleProjected: the callee is a lambda
-- extracted from a let-bound `left` literal. `fromLeftPartial` of a literal
-- `left` is the same static projection as `fst` of a literal tuple, and
-- reduces the same way. Note it is the *partial* extractor that projects;
-- the total `fromLeft` returns an Either and is deliberately not reduced.
-- The answer is the control's N(1, 1).
backends: interpreter, julia, python, batched
p(0.5)=(0.3520653, 1.0, False)
p(1.0)=(0.3989423, 1.0, False)
cdf(1.0)=(0.5, 0.0)
cdf(2.0)=(0.8413447, 0.0)
cdf(7.0)=(1.0, 0.0)
