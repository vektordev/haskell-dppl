-- N disjoint groups of a record of answers over one neural read: group i is
-- (a_i, b_i, a_i && b_i), so each of a_i, b_i is read by two slots and no
-- field is shared across groups. The groups are independent given the read,
-- so the cost should be linear in N (each group is a 4-pattern sum). The
-- emitted module instead grows by about 3x per group: 14 / 21 / 39 / 102 /
-- 380 KB at N = 2..6
-- (-I), and N = 7 runs past 6 GB in the compiler, at 8822d68.
-- In the experiments' Guess-Who pool (a 24-face board, per-value query) the
-- same structure costs ~2^(shared fields) per query at run time. Docs task
-- answer-record-shared-fields-enumerated-jointly.
expect-failure: growth above polynomial 2
knob: N = 2, 3, 4, 5, 6
metric: code-size
flags: --noIntegrate
