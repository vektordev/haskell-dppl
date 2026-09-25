backends: interpreter, julia, python, batched
p((True, True))=(0.485, 0.0)
p((True, False))=(0.015, 0.0)
p((False, True))=(0.135, 0.0)
p((False, False))=(0.365, 0.0)
-- Two nested enumerated latents, the fresh draw in one arm and the outer
-- latent in the other: P(False, True) = 0.5 * 0.3 * 0.9 = 0.135 and
-- P(False, False) = 0.5 * (0.3 * 0.1 + 0.7) = 0.365. The delegated body sees
-- BOTH `b` and `c` as fixed (`recoveredVars`). Task
-- enum-let-latent-gates-fresh-draw.
