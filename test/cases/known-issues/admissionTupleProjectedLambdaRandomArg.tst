-- Found by the admission-totality fuzz oracle (docs task
-- fuzz-admission-oracle-bugs, item 2). A lambda projected out of a tuple whose
-- other component is random, applied to a random argument: `main` is typed
-- Integrate, and IRCompiler's Apply equation cannot resolve the callee's chain
-- name to a lambda. With a deterministic first component
-- (`snd (1.0, \x -> Uniform)`) the same program is refused gracefully instead.
-- Idealized: `main` is just Uniform, p(0.5) = (1.0, 1).
expect-failure: diagnostic "should resolve to a lambda"
