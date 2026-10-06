-- Found by the admission-totality fuzz oracle (docs task
-- fuzz-admission-oracle-bugs, item 9). Forward chaining inverted the Int
-- product with the Float `mult` inverse (`OpDiv 1.0 (-6)` crashed the
-- optimizer); it now resolves `mult` to `multI` by the node's type, as
-- IRCompiler does.
-- The cdf rows (task cdf-through-discrete-inverse-wrong) need all three parts
-- of that fix: the negative factor flips the CDF (v * -6 <= s is v >= s/-6),
-- the flip keeps the atom at the bound (P(v >= 2), not P(v > 2)), and a
-- non-multiple bound rounds up instead of being "impossible" (-7 -> v >= 2).
p(-6)=(0.5, 0.0)
p(-12)=(0.5, 0.0)
p(-7) is impossible
cdf(-6)=(1.0, 0.0)
cdf(-5)=(1.0, 0.0)
cdf(-7)=(0.5, 0.0)
cdf(-12)=(0.5, 0.0)
cdf(-13)=(0.0, 0.0)
