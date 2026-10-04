p((True, Face True False True), (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6]))=(0.2185920000000001, 0.0)
p((True, Face ANY True ANY), (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6]))=(0.3400000000000001, 0.0)
p((True, Face False False False), (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6]))=(0.10639200000000006, 0.0)
p((True, Face ANY ANY ANY), (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6]))=(1.0, 0.0)
-- Per field: P(heard_j = yes) = q_j*0.9 + (1-q_j)*0.2, independent across
-- fields; the first component is the literal True.
