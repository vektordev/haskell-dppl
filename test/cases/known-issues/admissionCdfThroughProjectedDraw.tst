-- Found by the admission-totality fuzz oracle (docs task
-- fuzz-admission-oracle-bugs, item 5). `main` is the constant 2.0 behind a
-- projection that discards a draw-bound Uniform. It is typed Deterministic and
-- p() answers correctly, but every cdf() query dies in the interpreter with
-- `Expression must be the CDF of a valid distributionVAny`: the discarded
-- component's CDF is asked for at the wildcard. Idealized: a point mass at 2.0.
backends: interpreter
expect-failure: broken
cdf(2.0)=(1.0, 0.0)
cdf(3.0)=(1.0, 0.0)
