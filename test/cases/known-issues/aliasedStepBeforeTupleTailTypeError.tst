-- helperBuiltTupleConstantTail with its last Gaussian step aliased
-- (`draw y = s2 in mk s1 y`), the AliasIntro rewrite at that site. The original
-- answers phi(0) phi(0.5) at dim 2. Same message as the resolved
-- trajectory-tail-bound-as-tuple-type-error, new shape. Verified at 8924628
-- on dev. Docs task alias-before-helper-built-tuple-tail-approx-type-error.
ir-contract: violated "cannot match (Float, Float) with Float"
backends: interpreter
expect-failure: broken
p((0.0, (0.5, (1.0, 2.0))))=(0.1404537443096252, 2.0)
