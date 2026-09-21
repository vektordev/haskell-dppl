-- An `if` condition that draws *fresh* randomness independent of the
-- bound variable `x` crashes the set-witness engine instead of being treated
-- as an even mixture over the two arms. Idealized: a flat density of 0.5 on
-- (0, 2), e.g. p(1.0) = (0.5, 1); outside (0, 2) it is impossible, e.g.
-- p(3.0) is impossible.
expect-failure: diagnostic "set-valued witness construction failed"
