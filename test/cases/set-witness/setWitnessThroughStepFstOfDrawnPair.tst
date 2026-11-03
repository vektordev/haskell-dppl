-- set-witness/setWitnessThroughStepFstPair with the pair bound by a draw
-- around the projection (draw v = (x, 0.0) in fst v, the draw-introduction
-- rewrite at fst). Where the two-stage walk through the binding fails, the
-- walk enters it in place (Lang.enterInPlace). Must agree with
-- setWitnessThroughStepFstPair row for row.
-- Task set-witness-projection-through-introduced-draw.
p((0.3, 1.0)) is impossible
p((0.7, 0.0)) is impossible
p((0.7, 1.0))=(1.0, 1.0)
p((0.3, 0.0))=(1.0, 1.0)
p((ANY, 1.0))=(0.5, 0.0)
p((ANY, 0.0))=(0.5, 0.0)
p((0.7, ANY))=(1.0, 1.0)
p((0.3, ANY))=(1.0, 1.0)
