p((0.2, 0.5))=(1.0, 2.0)
p((ANY, 0.5))=(1.0, 1.0)
p((0.2, ANY))=(1.0, 1.0)
-- Design witnessed-per-query-capability, program S (self-contained sibling).
-- Slot 1 reads a let-bound latent and is enumerated; slot 2 draws inline and
-- is self-contained, so its own ANY is the existing per-field guard. Masking
-- slot 1 drops x as a dead binding. (ANY, 0.5) used to refuse, naming x.
