-- neuralReadQueriedOutsideDomain through point inversion: (1, 0) recovers
-- y = -1, outside readD's domain, and Python answers 0.2 * 0.4 = 0.08 (the
-- negative index). Verified at b16b4d9 on dev. Docs task
-- neural-read-query-outside-domain-unchecked.
-- Idealized: impossible.
expect-failure: broken
p((1, 0), (2, [0.1, 0.2, 0.3, 0.4]), (2, [0.1, 0.2, 0.3, 0.4])) is impossible
