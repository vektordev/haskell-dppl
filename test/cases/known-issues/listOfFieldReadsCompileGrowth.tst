-- A list literal of N field reads of one neural read, [x1 f, .., xN f]. Each
-- field is read once, so this is N independent Bernoulli slots. Its compile
-- time grows about 2-3x per element past N = 10: 0.7 / 0.8 / 1.4 / 4.5 / 38 s
-- at N = 8 / 10 / 12 / 14 / 16 (wall, incl. ~0.6 s stack start-up, -I), at
-- 8822d68. The same reads as a record (data Ans = Ans a1::Bool ..; Ans (x1 f)
-- ..) compile in 1.5 s at N = 16. Docs task
-- list-of-field-reads-compile-exponential.
expect-failure: growth above polynomial 2
knob: N = 4, 6, 8, 10, 12, 14
metric: alloc
flags: --noIntegrate
