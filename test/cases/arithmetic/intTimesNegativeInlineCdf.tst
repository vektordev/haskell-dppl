-- The inline spelling of drawBoundIntTimesNegative: the same three cdf
-- defects through the single-inverse InjF path rather than forward chaining
-- (task cdf-through-discrete-inverse-wrong; this answered cdf(-6) = 0.5,
-- cdf(-12) = 1.0 and cdf(-7) impossible).
p(-6)=(0.5, 0.0)
p(-12)=(0.5, 0.0)
cdf(-6)=(1.0, 0.0)
cdf(-7)=(0.5, 0.0)
cdf(-12)=(0.5, 0.0)
cdf(-13)=(0.0, 0.0)
