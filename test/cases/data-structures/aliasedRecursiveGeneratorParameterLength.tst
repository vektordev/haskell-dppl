-- recursiveLengthOfRecursiveList with the recursive generator's parameter
-- aliased (`rollout k = draw j = k in ..`), the AliasIntro rewrite at that
-- site: the same answer. Analysis unrolls `rollout 3` by substituting the
-- constant for `k`; it now substitutes a let-bound closed constant inside the
-- unrolled body too, so `j == 0` still decides the arm and `rollout (j - 1)`
-- still unrolls. It was refused ("no inference engine applies to the
-- parameter bound by the call of 'len'"). Task
-- alias-of-recursive-helper-parameter-refuses-with-random-argument.
p(True)=(0.75, 0.0)
p(False)=(0.25, 0.0)
