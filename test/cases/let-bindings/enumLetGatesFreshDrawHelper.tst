backends: interpreter, julia, python, batched
p((True, True))=(0.45, 0.0)
p((True, False))=(0.05, 0.0)
p((False, True))=(0.05, 0.0)
p((False, False))=(0.45, 0.0)
p((ANY, True))=(0.5, 0.0)
-- The noisy observation spelled through a non-recursive helper: `noisy b`
-- is a random `noisy_gen` call under the enumeration of `b`, which is handed
-- to the ordinary rules as a `noisy_prob` call with `b` fixed. The call's dim
-- is a runtime projection, so the delegation is admitted on the result TYPE
-- (Bool has no Float leaf, so its probability is always a mass). Only a call
-- into a function on a call cycle stays refused. Task
-- enum-let-latent-gates-fresh-draw.
