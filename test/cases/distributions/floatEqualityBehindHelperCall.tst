p(0.3, 0.1)=(1.0, 0.0)
p(0.4, 0.1) is impossible
-- The same deterministic sum compared with the query, inline and behind a
-- call. Inline (`main a = a + 0.2`, and the corpus's floatEquality) the
-- comparison is float-tolerant and p(0.3 | a = 0.1) = 1.0; behind the call it
-- compared exactly, and 0.1 + 0.2 /= 0.3, so it answered impossible. The
-- deterministic-application arm compared with a bare `==`; task
-- reinfer-body-under-recovered-bindings moved it onto equalityGuard, as every
-- other deterministic leaf is compared. Was known-issues pin of task
-- float-equality-tolerance-lost-behind-call-or-alias.
