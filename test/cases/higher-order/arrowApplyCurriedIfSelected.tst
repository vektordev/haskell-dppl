-- The curried twin of arrowApplyIfSelected: a two-argument spine whose head is
-- an if-selected lambda. The outer Apply's callee is itself an Apply, so it
-- takes rewriteApply's fallthrough; distributing the if only reaches the inner
-- node, and without re-dispatching on the rewritten callee the outer node is
-- left with an `if` in callee position, which crashed forward chaining with
-- "should resolve to a lambda". The condition is deterministic, so the answer
-- is the then arm's 1.0 + Normal ~ N(1, 1), the same family as its siblings.
backends: interpreter, julia, python, batched
p(0.5)=(0.3520653, 1.0, False)
p(1.0)=(0.3989423, 1.0, False)
cdf(1.0)=(0.5, 0.0)
cdf(2.0)=(0.8413447, 0.0)
cdf(7.0)=(1.0, 0.0)
