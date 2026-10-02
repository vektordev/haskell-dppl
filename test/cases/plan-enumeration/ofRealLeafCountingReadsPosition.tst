-- ofRealLeafCountingInlineReads with a `match` that also reads the continuous
-- leaf (task of-annotation-continuous-leaf-disables-enumeration, acceptance
-- criterion 2): an object counts if it is green AND px > 0.5. The plan engine
-- measures the px constraint as a Gaussian tail inside each world.
--   read 1: [0.2, 0.8, 0.5, 0.5, 0, 1]:   q1 = 0.8 * 0.5  * (1 - Phi(0.5))    = 0.123415
--   read 2: [0.4, 0.6, 0.75, 0.25, 1, 2]: q2 = 0.6 * 0.25 * (1 - Phi(-0.25)) = 0.089806
--   p(0) = (1-q1)(1-q2) = 0.797862, p(1) = 0.191054, p(2) = q1 q2 = 0.011083
p(0, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.797862, 0.0)
p(1, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.191054, 0.0)
p(2, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.011083, 0.0)
p(ANY, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(1.0, 0.0)
cdf(1, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.988917, 0.0)
