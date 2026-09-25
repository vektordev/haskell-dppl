backends: interpreter, julia, python, batched
p((True, True))=(0.45, 0.0)
p((True, False))=(0.05, 0.0)
p((False, True))=(0.05, 0.0)
p((False, False))=(0.45, 0.0)
p((False, ANY))=(0.5, 0.0)
p((ANY, False))=(0.5, 0.0)
-- The sibling of enumLetGatesFreshDrawArms: the fresh draw is the CONDITION of
-- the `if` and the arms read the enumerated latent `b`, so given `b` this is
-- the ordinary two-arm mixture over a fresh Bernoulli. Same model, respelled,
-- same values. Task enum-let-latent-gates-fresh-draw.
