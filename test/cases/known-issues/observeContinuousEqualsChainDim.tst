expect-failure: broken
backends: interpreter, python
p(Right 0)=(0.3989422804014327, 1.0)
p(Right 1)=(0.24197072451914337, 1.0)
p(Right ANY)=(0.640913004920576, 1.0)
-- The program the review of task
-- sampling-matches-pdf-continuous-equality-density asked to pin. Its values
-- are right -- p(Right 0)/p(Right 1) is the likelihood ratio N(0)/N(1), and
-- p(Left ()) is 1.0 -- but each `Right` row is a density reported at dim 0.
-- `observe` binds `v` to the inner value, which is enumerable over {0, 1, 2},
-- and the enumerated sum over it reports a mass whatever its body; the
-- density guard that would catch this is omitted for a result type with no
-- Float leaf. Task enumerated-sum-over-density-body. The same program without
-- `observe` answers the same values at dim 1
-- (set-witness/setWitnessContinuousEqualsChain). Rows state the idealized
-- values; only the currently-wrong rows are listed.
