-- The set-witness engine through a named top-level function rather than a
-- `let`-bound lambda (the sibling is let-bindings/letProbAbsNormal). Was a
-- known issue ("the lambda is applied through higher-order machinery") until
-- task binding-resolver-one-application-rule.
batched
p(0.5)=(0.70413065, 1.0, False)
p(1.0)=(0.48394145, 1.0, False)
p(-0.5) is impossible
p(ANY)=(1.0, 0.0, False)
cdf(1.0)=(0.68268949, 0.0)
