-- A theta read through a draw-bound alias inside a called function: the
-- anchor `theta t2 @ 0` is materialized at the call site, and the alias's
-- equivalence clause names the callee's untagged argument, so `t2` is never
-- resolved to the call's argument: "Could not find name in TypeEnv: t2".
-- Without the call (main thetas = draw t2 = thetas in ..) it answers 1.0.
-- Verified at 5c16258 on callee-body-name-sensitive-across-call. Docs task
-- theta-anchor-through-callee-local-binding.
expect-failure: diagnostic "Could not find name in TypeEnv"
p(2.5, ThetaTree [2.0] [])=(1.0, 1.0)
