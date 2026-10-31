-- A theta read through a draw-bound alias inside a called function: the
-- anchor `theta t2 @ 0` is materialized at the call site, and the alias's
-- equivalence clause exists only untagged (the per-invocation copy does not
-- chain through the anchor), so `t2` was never resolved to the call's
-- argument: "Could not find name in TypeEnv: t2". The alias's value lies in
-- the same function body, so it is resolved under the same invocation tag.
-- Docs task theta-anchor-through-callee-local-binding.
p(2.5, ThetaTree [2.0] [])=(1.0, 1.0)
p(5.5, ThetaTree [2.0] [])=(0.0, 1.0)
cdf(2.5, ThetaTree [2.0] [])=(0.5, 0.0)
