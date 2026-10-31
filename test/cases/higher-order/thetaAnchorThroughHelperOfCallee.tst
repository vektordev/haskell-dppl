-- The helper-extract of thetaArgumentNotCallerNamesake: the theta read sits
-- in a helper the callee calls. The set-witness engine compiles inner's body
-- with its parameter `ts` renamed to the argument, but the anchor was
-- fetched from the program as written and read `ts` by name, i.e. the
-- caller's (theta 5.0): p(2.5) answered 0.0. Docs task
-- theta-anchor-through-callee-local-binding.
p(2.5, ThetaTree [5.0] [], ThetaTree [2.0] [])=(1.0, 1.0)
p(5.5, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.0, 1.0)
cdf(2.5, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.5, 0.0)
