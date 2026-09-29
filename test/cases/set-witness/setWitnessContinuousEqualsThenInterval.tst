-- The complement of a point meeting an interval (task
-- sampling-matches-pdf-continuous-equality-density): `x /= 0.0` intersected
-- with `x > 1.0` or `x <= 1.0`. Used to crash on `OpLessThan VAnyExcept ..`.
-- The removed point has no mass, so each interval keeps its full CDF mass:
-- p(1) = 1 - Phi(1), p(2) = Phi(1), both dim 0.
p(0)=(0.3989422804014327, 1.0)
p(1)=(0.15865525393145707, 0.0)
p(2)=(0.8413447460685429, 0.0)
