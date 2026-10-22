slow
batched
p((0.0, 0.0), 1.0)=(0.09188814923696537, 2.0)
p((0.0, 0.0), 2.0)=(0.05305164769729845, 2.0)
p((0.0, 0.0), 0.0)=(0.15915494309189535, 2.0)
-- The shared latent scaled by a parameter: covariance [[1+th^2, th^2],
-- [th^2, 1+th^2]] is only known at run time, so the Cholesky pivots are
-- checked there (design affine-gaussian-forms M2). At th = 0 the fields
-- decouple: 1/(2 pi).
