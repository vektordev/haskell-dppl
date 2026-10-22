-- The CLEVR "exist with a predicate input" shape over objects that carry a
-- continuous position: a query colour c read once, shared by per-object
-- matches through a curried helper, `match c (readAttrs s)` (task
-- of-annotation-continuous-leaf-disables-enumeration). c is enumerated
-- densely; inside its loop it is fixed, so each match is a plan-engine call
-- with a deterministic leading argument, and px integrates out.
-- P(c = Red) = 0.3. Per read q = P(Obj) * P(color = c):
--   c = Red:   q1 = 0.4, q2 = 0.45      c = Green: q1 = 0.4, q2 = 0.15
-- p(k) = 0.3 * P(k | Red) + 0.7 * P(k | Green)
p(0, (2, [0.3, 0.7]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.456, 0.0)
p(1, (2, [0.3, 0.7]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.448, 0.0)
p(2, (2, [0.3, 0.7]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.096, 0.0)
p(ANY, (2, [0.3, 0.7]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(1.0, 0.0)
cdf(1, (2, [0.3, 0.7]), (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.904, 0.0)
