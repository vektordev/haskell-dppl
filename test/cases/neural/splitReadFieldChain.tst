p(Ans True False True False True True False, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.3024, 0.0)
p(Ans ANY ANY ANY True ANY ANY ANY, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.13999999999999999, 0.0)
p(Ans ANY True ANY ANY ANY False True, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.0116, 0.0)
p(Ans ANY ANY ANY ANY ANY ANY ANY, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(1.0, 0.0)
p(Ans True True ANY False ANY ANY ANY, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.0, 0.0)
p(Ans False ANY ANY ANY False ANY ANY, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.096, 0.0)
p(Ans ANY ANY False ANY True ANY ANY, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.07999999999999999, 0.0)
-- Brute force over the 2^4 readings of (a, b, c, e); the fifth row is
-- impossible (a and b force pab). Task split-read-field-leaf-rebuilt-per-world.
