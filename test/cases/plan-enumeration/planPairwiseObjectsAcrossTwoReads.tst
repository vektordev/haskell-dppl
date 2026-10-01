-- planPairwiseAcrossTwoReads over ADT objects, one neural read per object,
-- with existence guards. Object plan: [NoObj, Obj] flags, Color slots, then
-- Position's x (mu, sigma) and y (mu, sigma).
--   a: P(Obj) = 0.8, x ~ N(0, 1)      b: P(Obj) = 0.6, x ~ N(1, 2)
-- P(True) = 0.8 * 0.6 * Phi(1/sqrt(5)) = 0.48 * 0.672640 = 0.322867
-- P(False) = 1 - 0.322867 = 0.677133
-- y and the colours are never constrained, so they integrate out.
-- Task plan-pairwise-across-separate-neural-reads, acceptance criterion 2.
p(True, (2, [0.2, 0.8, 0.3, 0.3, 0.4, 0.0, 1.0, 5.0, 1.0]), (2, [0.4, 0.6, 0.1, 0.1, 0.8, 1.0, 2.0, 0.0, 1.0]))=(0.322867, 0.0)
p(False, (2, [0.2, 0.8, 0.3, 0.3, 0.4, 0.0, 1.0, 5.0, 1.0]), (2, [0.4, 0.6, 0.1, 0.1, 0.8, 1.0, 2.0, 0.0, 1.0]))=(0.677133, 0.0)
p(ANY, (2, [0.2, 0.8, 0.3, 0.3, 0.4, 0.0, 1.0, 5.0, 1.0]), (2, [0.4, 0.6, 0.1, 0.1, 0.8, 1.0, 2.0, 0.0, 1.0]))=(1.0, 0.0)
