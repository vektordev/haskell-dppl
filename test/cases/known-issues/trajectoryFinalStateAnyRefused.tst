-- An ANY on the final state of a recursive trajectory (the OU chain of
-- distributions/ouChainRecursive). The final state feeds no further factor,
-- so the marginal is the trajectory density without its last factor:
-- p([a, b, ANY]) = N(a; 0, 1) N(b; 0.9 a, 0.5) at dimension 2. The query ends
-- in the runtime error "cannot compute marginal: the argument of 'step' is
-- unobserved (ANY in its witnessing slot)": the witness of step's parameter is
-- the head of the list it returns, and the else arm reads the parameter again,
-- so the binding is not a sink, although at this call the condition selects
-- the base arm [x]. The neural trajectory (neural/diffusionToy1D) refuses
-- p([1.0, 0.0, ANY]) the same way. Found by design diffusion-models-wishlist;
-- docs task trajectory-final-state-any-refused.
expect-failure: broken
p([0.0, 0.0, ANY])=(0.31830989, 2.0)
p([0.5, 0.2, ANY])=(0.24789999, 2.0)
