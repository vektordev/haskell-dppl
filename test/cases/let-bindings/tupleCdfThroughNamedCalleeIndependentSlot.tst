-- docs task tuple-cdf-through-named-callee-measures-only-witnessed-slot: the
-- named-callee twin of tupleCdfThroughDrawIndependentSlot, with a
-- deterministic leading argument. The callee's integrate function measures the
-- constant and the independent Uniform slot at the recovered witness.
slow
p((0.5, (2.0, 0.5)))=(1.0, 2.0)
cdf((0.5, (2.0, 0.5)))=(0.25, 0.0)
cdf((0.5, (1.0, 0.5)))=(0.0, 0.0)
cdf((0.5, (3.0, 2.0)))=(0.5, 0.0)
cdf((2.0, (2.0, 0.5)))=(0.5, 0.0)
cdf((0.5, (2.0, -1.0)))=(0.0, 0.0)
cdf((0.5, ANY))=(0.5, 0.0)
