-- The saturating-counter spelling of sceneCountConditionalEdit: the count is
-- threaded through a helper, bump (bump (bump 0 o1) o2) ..., instead of a
-- flat sum. The flat sum's fix (absorbing each slot's branch observation into
-- that slot's summand, scene-count-conditional-edit-exponential) needs the
-- summands as separate operands; here the accumulator is case-split through
-- the call, so the branch worlds still clash with the count's groups and the
-- plan engine (budget 0) reruns ungrouped: 104 KB, 217 KB, 620 KB at
-- N = 3, 4, 5. Docs task saturating-count-conditional-edit-exponential.
expect-failure: growth above polynomial 2
knob: N = 2, 3, 4, 5
metric: code-size
flags: --materializationBudget 0
