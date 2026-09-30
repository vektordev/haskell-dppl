p((0.5, 1.1))=(0.13975322833741527, 2.0, False)
-- Task let-alias-of-random-binding-crashes-toirnormalparams, fixed by task
-- reinfer-body-under-recovered-bindings (law-carrying-modality M1). `p1` is a
-- pure alias of `s1`, and the aliased value also feeds further randomness
-- (`p1 + s2`). Until re-inference replaced the syntactic re-typing, p1 kept
-- s1's standalone PNormal after s1 was recovered, so toIRNormalParams was
-- handed a bare `Var "p1"`. Writing `s1` for `p1` always compiled.
-- s1 = 0.5, s2 = 0.6, s2 - s1 = 0.1, so p = phi(0.5) * phi(0.1).
-- Found by experiments_nest linear-dynamics-trajectory-mle.
