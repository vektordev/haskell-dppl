p((0.3, (0.5, True)))=(1.0, 2.0)
p((0.3, (0.5, False)))=(0.0, 2.0)
p((0.7, (0.5, False)))=(1.0, 2.0)
p((ANY, (0.5, True)))=(0.5, 1.0)
p((ANY, (0.5, False)))=(0.5, 1.0)
p((ANY, (0.2, True)))=(0.2, 1.0)
-- Both operands of the comparison are recovered as points from the other
-- slots, so the comparison is an indicator given the observation. Task
-- comparison-against-point-witnessed-latent-refused.
-- With p unobserved only q is witnessed: p is measured in place at its one
-- read, through the binding of q, as P(p < q) by its CDF. Task
-- comparison-of-two-witnessed-latents-finite-slot-mask-refused.
