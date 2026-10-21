-- Task fst-of-pair-wrapper-loses-structured-draw-constraint:
-- fstOfPairWrapperStructuredDraw with the wrapper applied twice. The read
-- recovers `e` through a chain of let-bound tuples and projections, which
-- ForwardChaining.exposeConstructIR must follow to its end (a depth bound of
-- 8 steps stopped short here and answered at dim 1).
p((0.3, 0.7))=(0.38138781546052414, 2.0)
p((0.3, -0.5)) is impossible
