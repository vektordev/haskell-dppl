-- Two enumerated Int leaves of one read compared, returned as Bool (task
-- enumerated-int-pair-comparison-no-probability). Used to be generate-only while
-- `if fst p < snd p then 1 else 0` was exact; the plan engine now couples two
-- enumerated leaves (one world per value of the left leaf).
-- Logits [a0..a3, b0..b3]; P(True) = sum_{i<j} a_i b_j = 0.15.
p(True, (2, [0.1, 0.2, 0.3, 0.4, 0.4, 0.3, 0.2, 0.1]))=(0.15, 0.0)
p(False, (2, [0.1, 0.2, 0.3, 0.4, 0.4, 0.3, 0.2, 0.1]))=(0.85, 0.0)
cdf(False, (2, [0.1, 0.2, 0.3, 0.4, 0.4, 0.3, 0.2, 0.1]))=(0.85, 0.0)
