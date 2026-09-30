-- A tuple-valued draw passed to a helper that projects one field. Inline
-- (`(fst e, snd e)`) the answer is N(0.3) * U(0.7) = 0.3814 at dim 2; verified at
-- 2d50350 on dev the helper gives the same number at dim 1, and at (0.0, -0.5), off
-- the Uniform's support, 0.3989 instead of impossible: the second field's
-- constraint is dropped. Found by the rewrite-invariance net's helper
-- extraction (setWitnessTupleDisjointFields, letBoundEitherDestructure,
-- tupleRoundtrip, drawDestructuredShared). Task
-- structured-draw-reread-through-binder-drops-field.
expect-failure: broken
p((0.3, 0.7))=(0.38138781546052414, 2.0)
