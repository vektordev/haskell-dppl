-- ifRootDeterministicConditionAnyHead with the condition on a parameter of a
-- named function (docs task if-root-deterministic-condition-any-marginal-refused).
-- f's observation splits on t < 0.5; main = f 2.0 takes the else arm, x : [x],
-- so p([ANY, a]) = phi(a) at dimension 1, and the one-element then arm is
-- impossible for a two-element query.
p([ANY, 0.5])=(0.35206533, 1.0)
p([ANY, 0.0])=(0.39894228, 1.0)
p([0.5, ANY])=(0.35206533, 1.0)
p([0.5, 0.5])=(0.35206533, 1.0)
p([ANY]) is impossible
