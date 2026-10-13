-- A tuple draw read twice, once through the identity wrapper fst (e, 0.0):
-- the density loses a dimension. The unwrapped spelling
-- `draw e = (Normal, Uniform) in (fst e, snd e)` answers (0.3814, dim 2), and
-- so does the singly-read `fst (e, 0.0)`; this one answers dim 1. Verified at
-- 3b72682 on dev, interpreter. Found by the rewrite-invariance net's tuple-law
-- family (pair-fst) over set-witness/setWitnessTupleDisjointFields,
-- drawDestructuredShared, letBoundEitherDestructure and
-- observeMaybePayloadRightAny (TestRewrites.knownDivergences). Docs task
-- fst-of-pair-wrapper-loses-structured-draw-constraint.
backends: interpreter, python
expect-failure: broken
p((0.3, 0.7))=(0.38138781546052414, 2.0)
