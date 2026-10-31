-- plan-enumeration/planPairwiseAcrossTwoReads with the second read moved into
-- a helper that receives the first read's value. The plan traversal opens the
-- helper's `draw b` as a second plan (planOpenBinding) inside the
-- specialization, reading the helper's deterministic parameter as its symbol.
-- a ~ N(0,1), b ~ N(1,2): P(True) = Phi(1/sqrt(5)) = 0.672640, as inline.
-- Task plan-neural-read-inside-specialized-function (was a known-issues pin).
p(True, (2, [0.0, 1.0]), (2, [1.0, 2.0]))=(0.67264, 0.0)
p(False, (2, [0.0, 1.0]), (2, [1.0, 2.0]))=(0.32736, 0.0)
p(ANY, (2, [0.0, 1.0]), (2, [1.0, 2.0]))=(1.0, 0.0)
