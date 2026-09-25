backends: interpreter, julia, python, batched
p(True)=(0.41, 0.0)
p(False)=(0.59, 0.0)
cdf(False)=(0.59, 0.0)
cdf(True)=(1.0, 0.0)
-- The noisy-observation shape with the `if` at the root of the enumerated
-- body, so it reaches `toIREnumerate`'s IfThenElse equation rather than its
-- fallback: P(True) = 0.3*0.9 + 0.7*0.2 = 0.41. Task
-- enum-let-latent-gates-fresh-draw.
