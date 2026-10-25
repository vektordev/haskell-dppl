-- The simplest Bottom verdict: a sum of two random leaves of different
-- families. main compiles generate only, and the probability query says
-- "it is either intractable for that mode or was suppressed by the
-- --noProbability flag": no reason is recorded. Normal * Normal,
-- max Normal Normal and Uniform + Uniform behave the same. Verified at
-- b16b4d9 on dev. Docs task bottom-verdict-records-no-refusal-reason. The
-- pin cannot see a reason being added (no-code only checks absence); move
-- it to `refused "..."` once one is.
-- Idealized density at 0.5: Phi(0.5) - Phi(-0.5) = 0.382925.
expect-failure: no-code probability
