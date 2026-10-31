-- normalThroughFunctionParam with the callee's parameter aliased through a
-- draw (the alias-introduction rewrite): main m is N(3 m, 6). The Gaussian
-- catch-all takes `shifted m 2.0 * 3.0` on its affine law and builds it
-- with the affine algebra, which enters the call and the draw as the
-- bindings they are; the scalar extractor, which reads a helper's normal
-- function, has none for a body with a draw and refused this (task
-- gaussian-catch-all-dispatch-on-codegen-law).
p(3.0, 1.0)=(0.0664904, 1.0)
p(0.0, 1.0)=(0.0586776, 1.0)
p(-6.0, -2.0)=(0.0664904, 1.0)
cdf(3.0, 1.0)=(0.5, 0.0)
cdf(0.0, 1.0)=(0.3085375, 0.0)
