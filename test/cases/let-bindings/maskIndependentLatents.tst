p((0.3, 0.5))=(1.0, 2.0)
p((ANY, 0.5))=(1.0, 1.0)
p((0.3, ANY))=(1.0, 1.0)
p((ANY, 1.5)) is impossible
-- Design witnessed-per-query-capability, program I. Both slots read a
-- let-bound latent, so both are enumerated, although they are independent:
-- masking one leaves the other's latent with no occurrence, which the
-- dead-binding arm drops. (ANY, 0.5) used to refuse, naming x.
