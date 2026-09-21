-- The set-witness engine is unreachable when the folded expression is
-- applied through a *named top-level function* rather than a `let`-bound
-- lambda, so absN's tagged-invocation call site fails to construct a
-- witness. The `let`-bound sibling (tests/cases/set-witness/letProbAbsNormal)
-- compiles and gives the idealized values this program should also produce:
-- p(0.0) = (0.79788456, 1), p(0.5) = (0.70413065, 1), p(1.0) = (0.48394145, 1),
-- p(-0.5) is impossible.
expect-failure: diagnostic "the lambda is applied through higher-order machinery"
