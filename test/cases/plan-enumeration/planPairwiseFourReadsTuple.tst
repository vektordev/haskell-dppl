-- Four separate neural reads (three nested plans opened by planOpenBinding,
-- each in its own offset range), observed as a tuple of two disjoint pairwise
-- relations. The pairs are independent, so the joint is their product:
--   a ~ N(0,1), b ~ N(1,2):  P(a < b) = Phi(1/sqrt(5))  = 0.672640
--   c ~ N(2,1), d ~ N(0,1):  P(c < d) = Phi(-2/sqrt(2)) = 0.078650
-- A wildcard slot marginalises its pair out.
-- Task plan-pairwise-across-separate-neural-reads.
p((True, True), (2, [0.0, 1.0]), (2, [1.0, 2.0]), (2, [2.0, 1.0]), (2, [0.0, 1.0]))=(0.052903, 0.0)
p((False, False), (2, [0.0, 1.0]), (2, [1.0, 2.0]), (2, [2.0, 1.0]), (2, [0.0, 1.0]))=(0.301614, 0.0)
p((True, False), (2, [0.0, 1.0]), (2, [1.0, 2.0]), (2, [2.0, 1.0]), (2, [0.0, 1.0]))=(0.619737, 0.0)
p((False, True), (2, [0.0, 1.0]), (2, [1.0, 2.0]), (2, [2.0, 1.0]), (2, [0.0, 1.0]))=(0.025747, 0.0)
p((True, ANY), (2, [0.0, 1.0]), (2, [1.0, 2.0]), (2, [2.0, 1.0]), (2, [0.0, 1.0]))=(0.67264, 0.0)
p((ANY, True), (2, [0.0, 1.0]), (2, [1.0, 2.0]), (2, [2.0, 1.0]), (2, [0.0, 1.0]))=(0.07865, 0.0)
p(ANY, (2, [0.0, 1.0]), (2, [1.0, 2.0]), (2, [2.0, 1.0]), (2, [0.0, 1.0]))=(1.0, 0.0)
