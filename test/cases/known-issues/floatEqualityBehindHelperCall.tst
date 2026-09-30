-- The same deterministic sum compared with the query, inline and behind a
-- call. Inline (`main a = a + 0.2`, and the corpus's floatEquality) the
-- comparison is float-tolerant and p(0.3 | a = 0.1) = 1.0; verified at 2d50350 on
-- dev the helper call compares exactly, and 0.1 + 0.2 /= 0.3, so it answers
-- impossible. An alias (`draw y = a in y + 0.2`) does the same. Found by the
-- rewrite-invariance net on floatEquality. Task
-- float-equality-tolerance-lost-behind-call-or-alias.
expect-failure: broken
p(0.3, 0.1)=(1.0, 0.0)
