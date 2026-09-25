-- Task shared-enumerated-latent-loses-per-slot-factorization: a two-argument
-- helper whose LAST argument is an enumerable random draw and whose first is
-- fixed. Analysis used to refuse to tag a curried spine, and probability mode
-- then tried to invert the observation through `match Red` and failed ("set-
-- valued witness construction failed"), although the one-argument spelling
-- `match (readC s)` compiled. The spine is now enumerated over its last
-- argument (IRCompiler.enumerateCurriedArgument).
-- p(1) = P(readC s = Red).
backends: interpreter, julia, python, batched
p(1, (2, [0.6, 0.3, 0.1]))=(0.6, 0.0)
p(0, (2, [0.6, 0.3, 0.1]))=(0.4, 0.0)
p(2, (2, [0.6, 0.3, 0.1])) is impossible
cdf(0, (2, [0.6, 0.3, 0.1]))=(0.4, 0.0)
