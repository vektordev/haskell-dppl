-- A positive Int factor needs no flip, but a bound that is not a multiple of
-- it rounds down: v * 6 <= 7 is v <= 1. The exact-division guard answered it
-- impossible (task cdf-through-discrete-inverse-wrong).
cdf(5)=(0.0, 0.0)
cdf(6)=(0.5, 0.0)
cdf(7)=(0.5, 0.0)
cdf(11)=(0.5, 0.0)
cdf(12)=(1.0, 0.0)
cdf(-1)=(0.0, 0.0)
