-- A tuple-valued draw re-bound by an alias (`draw s = t`) and read back field
-- by field. Without the alias (`(fst t, snd t)`) the answer is 0.25; verified
-- at 2d50350 on dev the alias gives 0.5, one field's constraint only. Found by
-- the rewrite-invariance net (alias and draw introduction on
-- drawDestructuredShared, tupleRoundtrip). Task
-- structured-draw-reread-through-binder-drops-field.
expect-failure: broken
p((True, False))=(0.25, 0.0)
