p((1.5, 0.5))=(1.0, 2.0)
p((ANY, 0.5))=(1.0, 1.0)
p((1.5, ANY))=(1.0, 1.0)
p((0.5, 0.5)) is impossible
p((ANY, 1.5)) is impossible
-- Design witnessed-per-query-capability, program S (shifted witness). Masking
-- the shifted slot leaves x and z without an occurrence; both are dropped.
-- This crashed at `(VAny, VFloat 1.0)` until task fc-inverse-refuses-on-any-input.
