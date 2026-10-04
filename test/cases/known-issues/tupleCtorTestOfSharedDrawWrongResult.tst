expect-failure: broken
p((True, Face True False))=(0.56, 0.0)
p((True, Face False False))=(0.24, 0.0)
p((True, Face ANY True))=(0.2, 0.0)
-- Idealized: isFace heard is always True, so P((True, Face a b)) = P(x0 = a) * P(x1 = b)
-- with P(x0 = True) = 0.7, P(x1 = True) = 0.2. Interpreter at 5025074 (and at 595b70b, before it): 1.0 at every row.
