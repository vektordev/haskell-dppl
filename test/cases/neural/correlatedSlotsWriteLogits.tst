p((True, True))=(0.5, 0.0)
p((True, False))=(0.0, 0.0)
p((False, True))=(0.0, 0.0)
p((False, False))=(0.5, 0.0)
writeLogits_len=4
writeLogits_at(indexOf(True))~=0.5
writeLogits_at(indexOf(False))~=0.5
-- Task warn-correlated-slots: one Bool latent read by both fields. The joint
-- puts no mass on (True, False), but writeLogits encodes each slot from its
-- own marginal, so the vector is [0.5, 0.5, 0.5, 0.5] and denotes the product
-- of marginals (0.25 on each outcome). Compiling it emits the correlated-slots
-- warning; the writeLogits rows pin that the warning leaves the vector alone.
-- WriteLogitsRoundtrip.DensityAgreement skips this endpoint (its read-back is
-- the product of marginals by design).
