slow
batched
p((ANY, (ANY, True)))=(0.5, 0.0)
p((0.5, (0.5, True)))=(0.042270589238047857, 2.0)
p((ANY, (0.5, False)))=(0.1325017661720143, 1.0)
-- Two Gaussian fields sharing w beside an independent coin. Formerly
-- known-issues/maskTableOverpromisesRefusedFunction: --marginals said
-- Integrate, but no engine took the binding of w. The joint affine engine
-- (design affine-gaussian-forms M2) answers every mask.
