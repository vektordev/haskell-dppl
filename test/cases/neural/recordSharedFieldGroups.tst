p(Ans True True True False True, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.0044800000000000005, 0.0)
p(Ans True False ANY True True, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.252, 0.0)
p(Ans ANY True True False False, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.046799999999999994, 0.0)
p(Ans ANY ANY ANY ANY ANY, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(1.0, 0.0)
p(Ans False False False False True, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.006720000000000003, 0.0)
p(Ans True True True True False, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9]))=(0.0, 0.0)
-- Brute force over the 2^4 readings; the last row is impossible (a2 forces q2).
-- Task answer-record-shared-fields-enumerated-jointly.
