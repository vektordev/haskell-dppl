-- `neg` declares derivative -1, so its CDF is flipped too, and lost the atom
-- at the bound the same way (task cdf-through-discrete-inverse-wrong).
p(-1.0)=(0.5, 0.0)
cdf(-1.0)=(1.0, 0.0)
cdf(-1.5)=(0.5, 0.0)
cdf(-2.0)=(0.5, 0.0)
cdf(-2.5)=(0.0, 0.0)
