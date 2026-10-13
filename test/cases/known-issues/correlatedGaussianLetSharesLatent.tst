-- A Gaussian latent read by two outputs (x used in both `a` and `b`) has a
-- closed-form bivariate density -- covariance [[2,1],[1,2]] -- that nothing
-- in the compiler represents yet (design affine-gaussian-forms M2). Since
-- task affine-form-as-law-certificate the modality pass sees it: the tuple's
-- fields share the marginal latent x, its certificate says so
-- (JSharedLatent), and the tuple types Bottom, so the probability and
-- integrate variants are absent and generate still works. Before that it was
-- admitted Integrate and refused in set-witness construction. Since task
-- engine-applicability-as-data the binding of x is typed first: no engine
-- applies to it (its two readers are two consumers), so it is bound
-- sample-only, with that reason recorded on the absent variants. See
-- TestRejection.SetWitnessSharedLatent for the fuller regression on the same
-- gap (a differently-shaped sibling program, and generate surviving).
slow
expect-failure: refused "no inference engine applies to the binding of 'x'"
