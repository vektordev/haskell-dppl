-- An affine operand under `==`, constant on the left. Unguarded inverses
-- (plus/mult) crashed the same way as exp's guarded one: the False-polarity
-- VAnyExcept sentinel reached the inverse arithmetic (b - 1.0, b / 2.0).
p(0.0)=(1.0, 0.0, False)
p(2.0) is impossible
