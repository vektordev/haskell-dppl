slow
p(Ans True True True False True True False, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9, 0.35, 0.65]))=(0.007385631839999999, 0.0)
p(Ans True ANY False ANY ANY True True, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9, 0.35, 0.65]))=(0.07161000000000002, 0.0)
p(Ans ANY True True False False False ANY, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9, 0.35, 0.65]))=(0.02425764, 0.0)
p(Ans ANY ANY ANY ANY ANY ANY ANY, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9, 0.35, 0.65]))=(1.0, 0.0)
p(Ans False False False True True True True, (2, [0.7, 0.3, 0.2, 0.8, 0.6, 0.4, 0.1, 0.9, 0.35, 0.65]))=(0.006293955360000002, 0.0)
-- Brute force over the 2^5 readings: sum_w P(w) prod_slot P(answer | truth(w)).
-- Task answer-record-shared-fields-enumerated-jointly.
