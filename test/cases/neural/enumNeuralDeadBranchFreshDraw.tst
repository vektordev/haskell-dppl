p([[False]], (2, [0.7, 0.3, 0.4, 0.6]))=(1.0, 0.0)
p([[True]], (2, [0.7, 0.3, 0.4, 0.6])) is impossible
-- Formerly known-issues/fuzzNeuralPlanGenerateBackedDeadBranch (found by the
-- neural/plan-enumeration fuzz generator): both `if` arms are the literal
-- `[[False]]`, so the result is deterministic whatever the fresh draw in the
-- condition or the unused neural read. The enumerated body used to be refused
-- as generate-backed; it is now measured by the ordinary rules with `s` fixed
-- (task enum-let-latent-gates-fresh-draw).
