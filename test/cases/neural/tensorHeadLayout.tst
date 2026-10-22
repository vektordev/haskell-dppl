-- Layout compatibility of a tensor head (decision D6 of design
-- tensors-in-core-language, task tensor-gaussian-heads-rd-diffusion): a
-- Tensor[2] Float head reads its verbatim logits element-major,
-- [mu_1, sigma_1, mu_2, sigma_2], which is the layout of its nested-tuple
-- spelling. Its twin tensorHeadLayoutTupleTwin pins the same rows on
-- (Float, Float) under the same logits; the two must stay identical.
batched
p([|2.0, 1.0|], (2, [2.0, 0.5, 0.0, 1.0]))=(0.19306471, 2.0)
p([|1.0, -1.0|], (2, [2.0, 0.5, 0.0, 2.0]))=(0.01900835, 2.0)
p([|0.3, 0.0|], (2, [0.5, 0.25, -1.0, 1.5]))=(0.24677704, 2.0)
