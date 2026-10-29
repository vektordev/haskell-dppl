-- A two-component Gaussian mixture plus independent Gaussian noise, which is
-- again a Gaussian mixture. Inline, main has no probability variant and no
-- recorded reason; the draw-bound spelling is refused ("no inference engine
-- applies to the binding of 'x'"). Verified at b16b4d9 on dev. Since docs task
-- bottom-verdict-records-no-refusal-reason the inline spelling is refused too,
-- naming the outer `+` and its operands' laws.
-- Idealized: 0.5 N(1; 0, 1.25) + 0.5 N(1; 3, 1.25).
expect-failure: broken
p(1.0)=(0.1556143, 1.0)
