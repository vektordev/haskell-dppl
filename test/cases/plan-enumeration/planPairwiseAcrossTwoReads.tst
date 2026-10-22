-- A pairwise relation between continuous leaves of two SEPARATE neural reads
-- (one read per object -- the layout the CLEVR experiments use to keep plans
-- linear in the object count). The plan traversal opens the inner `draw b` as
-- a second plan in its own offset range (planOpenBinding), so the comparison
-- is the same pwPairs difference Gaussian as inside one read
-- (planEnumContPair). a ~ N(0,1), b ~ N(1,2):
-- P(a < b) = Phi(1/sqrt(5)) = 0.672640.
-- Task plan-pairwise-across-separate-neural-reads (was a known-issues pin).
p(True, (2, [0.0, 1.0]), (2, [1.0, 2.0]))=(0.67264, 0.0)
p(False, (2, [0.0, 1.0]), (2, [1.0, 2.0]))=(0.32736, 0.0)
p(ANY, (2, [0.0, 1.0]), (2, [1.0, 2.0]))=(1.0, 0.0)
cdf(False, (2, [0.0, 1.0]), (2, [1.0, 2.0]))=(0.32736, 0.0)
cdf(True, (2, [0.0, 1.0]), (2, [1.0, 2.0]))=(1.0, 0.0)
