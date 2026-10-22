slow
p((0.5, 0.5))=(0.0702268721548126, 2.0)
p((0.0, 0.0))=(0.0795774715459477, 2.0)
cdf((0.5, 0.5))=(0.40725226355997063, 0.0)
-- (x + y, x - y) shares both latents, but its coefficient vectors are
-- orthogonal: the covariance is diag(2, 2), so the fields are independent
-- N(0, sqrt 2) and the joint CDF is a product (design affine-gaussian-forms
-- section 4, row 9).
