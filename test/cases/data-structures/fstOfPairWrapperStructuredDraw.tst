-- Task fst-of-pair-wrapper-loses-structured-draw-constraint. A tuple draw
-- read twice, once through the identity wrapper fst (e, 0.0). That read
-- recovers `e` as the first field of the let-bound tuple `(e', ANY)`, which
-- ForwardChaining.mergeExpr took for an opaque whole value and kept over the
-- other read's `(ANY, snd)`: the Uniform's coordinate went unobserved, and
-- p((0.3, 0.7)) answered at dim 1. `exposeConstruct` now resolves the
-- projection to the tuple so the two reads merge field by field. Mirrored on
-- the snd side by sndOfPairWrapperStructuredDraw.
p((0.3, 0.7))=(0.38138781546052414, 2.0)
p((0.3, -0.5)) is impossible
p((0.0, 1.5)) is impossible
