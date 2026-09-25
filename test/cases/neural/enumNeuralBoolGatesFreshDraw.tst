backends: interpreter, julia, python, batched
p(2, (2, [0.7, 0.3]))=(0.35, 0.0)
p(1, (2, [0.7, 0.3]))=(0.35, 0.0)
p(0, (2, [0.7, 0.3]))=(0.3, 0.0)
cdf(1, (2, [0.7, 0.3]))=(0.65, 0.0)
-- Formerly known-issues/fuzzNeuralPlanGenerateBackedOpenQuestion (found by the
-- neural/plan-enumeration fuzz generator, 68% of its crashes): an enumerated
-- neural Bool read gating a fresh coin flip. Given `s` the body is an
-- ordinary `if` over fixed `s`, so it is measured by the ordinary rules
-- rather than refused as generate-backed (task
-- enum-let-latent-gates-fresh-draw): p(2) = 0.7 * 0.5, p(0) = 0.3.
