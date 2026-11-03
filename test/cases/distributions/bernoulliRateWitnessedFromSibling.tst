p((0.3, True))=(0.3, 1.0)
p((0.3, False))=(0.7, 1.0)
p((0.8, True))=(0.8, 1.0)
p((1.5, True))=(0.0, 1.0)
-- A Bernoulli whose rate is a latent the first slot observes exactly: given
-- the observation p is a point (witnessed), so `Uniform < p` has a fixed
-- bound. ModalityInfer's compareGround admits a witnessed operand as a fixed
-- bound. Task comparison-against-point-witnessed-latent-refused.
