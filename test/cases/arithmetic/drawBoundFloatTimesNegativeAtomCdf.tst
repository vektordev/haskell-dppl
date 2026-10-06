-- A decreasing Float transform of a discrete operand: the flipped CDF is
-- P(v >= x), and 1 - CDF(x) is only P(v > x), losing the atom at x
-- (task cdf-through-discrete-inverse-wrong; answered 0.5 and 0.0).
cdf(-6.0)=(1.0, 0.0)
cdf(-7.0)=(0.5, 0.0)
cdf(-12.0)=(0.5, 0.0)
cdf(-12.5)=(0.0, 0.0)
