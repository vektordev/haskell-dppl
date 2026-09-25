backends: interpreter, julia, python, batched
p((True, True))=(0.45, 0.0)
p((True, False))=(0.05, 0.0)
p((False, True))=(0.05, 0.0)
p((False, False))=(0.45, 0.0)
p((True, ANY))=(0.5, 0.0)
p((ANY, True))=(0.5, 0.0)
-- An enumerable let-bound latent (`b`) used as the CONDITION of an `if` whose
-- ARMS draw fresh randomness: the noisy observation of a shared hidden latent.
-- `toIREnumerate` compiles an enumerated body forward, which is exact only
-- when it is deterministic given the enumerated latents; this one is not, and
-- used to be refused as a "generate-backed fallback" misdiagnosed as unbounded
-- self-recursion. It is now handed to the ordinary inference rules with `b`
-- fixed at its enumerated value (`forwardOrInfer`), where the `if` selects an
-- arm and measures it. The values are those of the hoisted respelling
--   draw b = Uniform < 0.5 in draw n = Uniform < 0.9 in (b, if b then n else (not n))
-- which always compiled. Task enum-let-latent-gates-fresh-draw.
