p((0.5, True))=(0.5, 1.0)
p((0.2, True))=(0.2, 1.0)
p((0.2, False))=(0.8, 1.0)
p((0.2, ANY))=(1.0, 1.0)
-- p is bound outside the binding of q and read once, in the comparison: it
-- is measured in place there, through q's binding, as P(p < q) by its CDF.
-- (ANY, True) is P(p < q) for two uniforms, a convolution, and stays
-- refused. Task comparison-of-two-witnessed-latents-finite-slot-mask-refused.
