-- distributions/collapseMixture with the threshold drawn into a binding (its
-- draw-intro rewrite): the moments are the same, mu = 3, sigma^2 = 4.75.
-- The generate function binds the inlined probability of the condition, a
-- literal-lambda redex returning a packed (p, (dim, (bc, flag))), and
-- stripBranchCount read it as a callee's result while leaving it four fields
-- wide: sampling crashed with "Condition is not a boolean: VTuple (VFloat 1.0)
-- (VBool False)" (regression of 415173b, task
-- trajectory-tail-bound-as-tuple-type-error; found by Slow.RewriteIntegration).
p(3.0)=(0.183047, 1.0)
p(0.0)=(0.070978, 1.0)
cdf(3.0)=(0.5, 0.0)
