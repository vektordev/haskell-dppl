p((0.9, (0.4, 0.5)))=(1.0, 2.0)
p((ANY, (0.4, 0.5)))=(1.0, 2.0)
p((0.9, (ANY, 0.5)))=(1.0, 2.0)
p((0.9, (0.4, ANY)))=(1.0, 2.0)
p((ANY, (ANY, 0.5)))=(1.0, 1.0)
p((1.5, (0.4, 0.5))) is impossible
-- Design witnessed-per-query-capability, program N (task per-mask-variants-by-pruning).
-- The sum slot is recovered from (x, y), so masking it leaves both latents
-- witnessed by the remaining slots: the variant compiled from (HOLE, (x, y))
-- answers at dim 2. This crashed at `(VAny, VFloat 0.5)` before task
-- fc-inverse-refuses-on-any-input and refused after it. Masking the sum and
-- x leaves y alone (dim 1); masking both inner slots leaves the convolution
-- x + y, which the dispatcher refuses (pinned in TestInternals).
