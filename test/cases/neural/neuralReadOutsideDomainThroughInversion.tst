-- neuralReadQueriedOutsideDomain through point inversion: (1, 0) recovers
-- y = -1, outside readD's domain, so the point is impossible (Python used to
-- answer 0.2 * 0.4 = 0.08 by the negative index). Docs task
-- neural-read-query-outside-domain-unchecked.
p((1, 0), (2, [0.1, 0.2, 0.3, 0.4]), (2, [0.1, 0.2, 0.3, 0.4])) is impossible
p((1, 7), (2, [0.1, 0.2, 0.3, 0.4]), (2, [0.1, 0.2, 0.3, 0.4])) is impossible
p((1, 4), (2, [0.1, 0.2, 0.3, 0.4]), (2, [0.1, 0.2, 0.3, 0.4])) = (0.08, 0)
