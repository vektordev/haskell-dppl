-- The deterministic-condition if split inside a named function, nested, with
-- the condition reading a leading parameter bound at the call (t = 1.0): the
-- middle arm [x, x + 1.0] is taken, so p([a, a + 1]) = phi(a), dim 1
-- (task witness-through-deterministic-if-over-list-arms).
p([0.3, 1.3])=(0.38138782, 1.0)
p([0.0, 1.0])=(0.39894228, 1.0)
p([0.3, 1.2]) is impossible
p([0.3]) is impossible
