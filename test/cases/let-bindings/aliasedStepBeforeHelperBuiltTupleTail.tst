-- helperBuiltTupleConstantTail with its last Gaussian step aliased
-- (`draw y = s2 in mk s1 y`), the AliasIntro rewrite at that site: the same
-- answers, phi(0) phi(0.5) at dim 2. The probability function binds the
-- redex (\y -> mk_gen(s1)(y)) s2 to compare it against the query, and
-- 'stripBranchCount' read that redex as a callee's packed result (it is not
-- itself a call of a generate function) and shifted its last two fields:
-- the interpreter raised "Approx can only evaluate on two floats". Task
-- alias-before-helper-built-tuple-tail-approx-type-error.
p((0.0, (0.5, (1.0, 2.0))))=(0.1404537443096252, 2.0)
p((0.0, (0.5, (1.0, ANY))))=(0.1404537443096252, 2.0)
p((0.0, (ANY, (1.0, 2.0))))=(0.3989422804014327, 1.0)
p((0.0, (0.5, (1.0, 3.0))))=(0.0, 2.0)
