-- The simplest Bottom verdict: a sum of two random leaves of different
-- families. main compiles generate only, and the probability query says
-- "it is either intractable for that mode or was suppressed by the
-- --noProbability flag": no reason is recorded. Normal * Normal,
-- max Normal Normal and Uniform + Uniform behave the same. Verified at
-- b16b4d9 on dev. Docs task bottom-verdict-records-no-refusal-reason, which
-- added the reason pinned below (the `+` and its operands' laws); the open
-- capability question is whether such a sum should answer at all.
-- Idealized density at 0.5: Phi(0.5) - Phi(-0.5) = 0.382925.
expect-failure: refused "has no inference rule for its operands"
