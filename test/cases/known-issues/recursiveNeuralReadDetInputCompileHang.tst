-- docs ticket recursive-neural-read-det-input-compile-hang: the recursive
-- trajectory step whose next state is a network read at a deterministic input
-- (`mu t`, or `mu 0.0`) never finishes compiling; modality inference
-- completes and IR compilation runs into the cap. The same step at a
-- witnessed input (`mu x`, neural/neuralTrajectoryScalar) or with an
-- arithmetic next state (`x + mu 0.0`, distributions/ouChainRecursive) compiles.
expect-failure: hang
cap: 3s
