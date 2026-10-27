-- The same EAN-style checksum fold as discreteCdfPmfEnumerationTwin, by list
-- depth N. Each level's DP step is emitted as its own unrolled block of
-- per-state assignments, so the module grows with the depth where one looped
-- kernel would be constant: 187 / 239 / 342 / 553 / 819 KB at N = 4 / 5 / 6 /
-- 8 / 10, compiling in 2.5 / 3.6 / 7.4 / 28 / 78 s, at 29afbca. Docs task
-- plan-rerolling-recursion-levels.
expect-failure: growth above linear
knob: N = 4, 5, 6
metric: code-size
cap: 30 s, 8000 MB
