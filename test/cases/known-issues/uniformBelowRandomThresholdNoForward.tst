expect-failure: no-code
p(True)=(0.5, 0.0)
p(False)=(0.5, 0.0)
-- A Bernoulli whose rate is itself random: `Uniform < t` with `t` depending
-- on an enumerated latent. Compiles with exit 0 and NO diagnostic, but Main
-- gets only `generate` -- the probability function is silently absent. Same
-- for `draw x = Uniform in (x < 0.5, Uniform < x)`. The hand-spelled
-- equivalent `if b then Uniform < 0.9 else Uniform < 0.1` compiles and
-- answers. Idealized value: 0.5*0.9 + 0.5*0.1. Found by experiments_nest
-- exact-eig-question-asking. Task uniform-below-random-threshold-no-forward.
