p(1.4)=(0.19552134698772797, 1.0, False)
p(1.0)=(0.19947114020071635, 1.0, False)
p(-3.0)=(2.699548325659403e-2, 1.0, False)
-- Row 7 of design law-carrying-modality's evidence table, the rewritten half
-- of `main = draw x = Normal in x * 2.0 + 1.0`: the result is N(1, 2).
-- Crashed with "toIRNormalParams: cannot extract Normal params" until task
-- reinfer-body-under-recovered-bindings: once x was recovered, the old
-- syntactic re-typing left y at its standalone PNormal, and `y + 1.0` went to
-- the Gaussian catch-all with a bare local Var. Re-inference binds y Exact.
