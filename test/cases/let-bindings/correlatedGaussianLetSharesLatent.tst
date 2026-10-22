batched
p((0.0, 0.0))=(0.09188814923696537, 2.0)
p((0.5, 0.5))=(0.08454117847609571, 2.0)
p((0.5, -1.0))=(0.0512768167539898, 2.0)
p((ANY, 0.5))=(0.2650035323440286, 1.0)
p((0.5, ANY))=(0.2650035323440286, 1.0)
-- A Gaussian latent read by two outputs: (a, b) is bivariate normal with
-- covariance [[2,1],[1,2]] (design affine-gaussian-forms M2, the joint
-- affine engine at the binding of x). At the origin the correlated density
-- 1/(2 pi sqrt 3) = 0.0918882 differs from the decorrelated 1/(4 pi) =
-- 0.0795775: a rewrite that drops the correlation fails here. A field
-- observed ANY is marginalised out (N(0, sqrt 2)). The joint CDF has no
-- closed form, so the integrate variant is refused.
