-- A tuple-valued draw passed to a helper that projects one field. Inline
-- (`(fst e, snd e)`) the answer is N(0.3) * U(0.7) = 0.3814 at dim 2; the
-- helper gave the same number at dim 1, and at (0.0, -0.5), off the Uniform's
-- support, 0.3989: the read through the helper recovered `e` as a projection
-- of a let-bound tuple, which ForwardChaining.mergeExpr kept as an opaque
-- whole value over `snd e`'s field (tasks
-- structured-draw-reread-through-binder-drops-field,
-- fst-of-pair-wrapper-loses-structured-draw-constraint).
p((0.3, 0.7))=(0.38138781546052414, 2.0)
p((0.0, -0.5)) is impossible
p((0.0, 1.5)) is impossible
