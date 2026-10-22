-- The nested-tuple twin of tensorHeadLayout (decision D6): the same verbatim
-- logits and the same numbers, so the tensor head and the tuple head share
-- one logit layout.
batched
p((2.0, 1.0), (2, [2.0, 0.5, 0.0, 1.0]))=(0.19306471, 2.0)
p((1.0, -1.0), (2, [2.0, 0.5, 0.0, 2.0]))=(0.01900835, 2.0)
p((0.3, 0.0), (2, [0.5, 0.25, -1.0, 1.5]))=(0.24677704, 2.0)
