-- Two latents, both point-recovered: b = s1 / 3 from the second slot and
-- a = s0 - 3b from the first. The density must be phi(a) phi(b) |1/3|, but
-- the first slot's path also multiplies in the derivative of the clause that
-- recovers b (ForwardChaining.derivativeOfPath folds over every clause of the
-- path, the other latent's recovery included), so b's 1/3 is applied twice:
-- 0.017508 = phi(0.1)^2 / 9 at (0.4, 0.3). (a + b, 3b) and (a + 3b, b) are
-- right; (3b, 2a + 3b) is off by 1/3 too, and (a + exp b, exp b) by 1/e^b.
-- Same at -O0. Verified at b16b4d9 on dev. Docs task
-- forwardchaining-path-derivative-includes-other-latents-jacobian.
-- Idealized: phi(0.1)^2 / 3.
expect-failure: broken
p((0.4, 0.3))=(0.0525238, 2.0)
