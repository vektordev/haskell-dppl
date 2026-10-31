-- data-structures/tupleCtorTestOfSharedDraw with its draw re-bound by an
-- alias, the shape draw introduction gives it. Inline, (True, Face True
-- False) is the fields' product 0.56; through the alias every True first
-- slot answers 1.0, no field constrained (helper extraction of `isFace heard`
-- or of the tuple does the same). Verified on dev at c88cc2a, and the same
-- 1.0 at 831c3d6, where the variant's False row crashed on the VAnyExcept
-- witness, which hid it from the rewrite sweep. Task
-- structured-draw-reread-through-binder-drops-field.
expect-failure: broken
p((True, Face True False))=(0.56, 0.0)
p((True, Face False False))=(0.24, 0.0)
