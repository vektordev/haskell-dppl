-- docs ticket nested-continuous-equality-guards-compile-memory-blowup: a
-- continuous point guard (`x == 0.0`) whose else arm tests the same draw
-- against an inequality and then another point (`1.0 < x`, `1.0 == x`) does
-- not finish compiling its probability or integrate variant, and retains
-- about a third of what it allocates until the heap gives out (the rewrite
-- variant it was found as: 3.1 GB resident after 9.3 GB allocated, at
-- cf769b6). Generate compiles at once. Found as the compare-negate rewrite of
-- setWitnessContinuousEqualsThenInterval, which OOM-killed the Slow
-- RewriteInvarianceCorpus sweep.
expect-failure: hang
cap: 20s, 400 MB
