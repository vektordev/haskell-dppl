-- Two latents, both point-recovered: b = s1 / 3 from the second slot and
-- a = s0 - 3b from the first. The density is phi(a) phi(b) |1/3|: b's
-- recovery is a side operand of a's path and supplies its value, not its
-- derivative (ForwardChaining.jacobianClauses). It used to answer
-- phi(0.1)^2 / 9. Docs task
-- forwardchaining-path-derivative-includes-other-latents-jacobian.
p((0.4, 0.3))=(0.0525238, 2.0)
