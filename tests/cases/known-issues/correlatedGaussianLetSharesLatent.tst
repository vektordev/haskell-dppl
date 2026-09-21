-- A Gaussian latent read by two outputs (x used in both `a` and `b`) has a
-- closed-form bivariate density -- covariance [[2,1],[1,2]] -- that nothing
-- in the compiler represents yet, so the set-witness engine's eager `error`
-- takes the whole compile down instead of the compiler either answering the
-- correlated density or declining gracefully. See
-- TestRejection.SetWitnessSharedLatent for the fuller, multi-assertion
-- regression on the same defect (it additionally checks a differently-shaped
-- sibling program and that the refusal is eager enough to kill `generate`).
expect-failure: diagnostic "set-valued witness construction failed"
