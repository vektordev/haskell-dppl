-- Two integer quotients in one forward-chaining inverse, of opposite signs
-- (v * -2 * 3, values -12 and -6). Each step's rounding follows the sign of
-- the inverse from the observation through that step, not its own factor:
-- the outer step (3) rounds down, the inner (-2) up
-- (task cdf-through-discrete-inverse-wrong).
cdf(-13)=(0.0, 0.0)
cdf(-12)=(0.5, 0.0)
cdf(-8)=(0.5, 0.0)
cdf(-7)=(0.5, 0.0)
cdf(-6)=(1.0, 0.0)
