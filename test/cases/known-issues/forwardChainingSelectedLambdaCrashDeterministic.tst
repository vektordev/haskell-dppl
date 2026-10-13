-- Same root cause as forwardChainingSelectedLambdaCrash,
-- fully deterministic variant (no probabilistic value anywhere). `mk True`
-- selects `\x -> x + 1.0`, applied to 3.0 gives 4.0 deterministically -- the
-- idealized row below states that value. This used to crash in
-- ForwardChaining's constructEquivalenceClauses, forced by the
-- conditional-annotation pass. That pass is gone (task
-- engine-applicability-as-data), nothing on this program's path forces the
-- clauses any more, and the interpreter answers the row. The emitted Python
-- module still fails: its generate calls `mk.generate(True, 3.0)`, one
-- argument too many for the selected lambda. The pin is therefore on Python
-- only, with the mechanism left unpinned (`broken`).
backends: python
slow
expect-failure: broken
p(4.0)=(1.0, 0.0)
