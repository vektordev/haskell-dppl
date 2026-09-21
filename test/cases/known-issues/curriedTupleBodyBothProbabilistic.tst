-- Verified at commit 704d41f on dev, at -O0: a curried
-- lambda spine (`(\x -> \y -> (x, y)) Normal Normal`) whose body is a tuple
-- only measures the field fed by the *last* applied argument -- every other
-- field's constraint is silently dropped, so the answer is independent of x
-- entirely. Idealized (correct, product of two independent standard-normal
-- densities at dim 2):
--   p((0.0, 0.0))    = (0.15915494, 2.0)
--   p((5.0, 0.0))    = (5.9311527e-7, 2.0)
--   p((-100.0, 0.0)) = (0.0, 2.0)
--   p((0.0, 1.0))    = (0.096532353, 2.0)
-- The rows below pin the currently-wrong value the bug actually produces
-- (always phi(y) at dim 1, ignoring x).
expect-failure: wrong-result
p((0.0, 0.0))=(0.39894228, 1.0)
p((5.0, 0.0))=(0.39894228, 1.0)
p((-100.0, 0.0))=(0.39894228, 1.0)
p((0.0, 1.0))=(0.24197072, 1.0)
