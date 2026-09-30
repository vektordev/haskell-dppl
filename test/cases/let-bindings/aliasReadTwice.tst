p((0.5, 1.5))=(1.0, 1.0, False)
p((0.25, 1.25))=(1.0, 1.0, False)
p((0.5, 1.4)) is impossible
p((1.5, 2.5)) is impossible
-- One syntactic occurrence of x, read twice through the alias y. Task
-- reinfer-body-under-recovered-bindings: once x is recovered, re-inference
-- types y Deterministic, so the body holds no random source, and the witness
-- fold's sink test must count x's uses through the binder. Otherwise the query
-- (ANY, 1.5) treats the binding as a sink and evaluates `VAny + 1.0`; it
-- must refuse ("cannot compute marginal"), which a .tst row cannot state, so
-- that is pinned in TestInternals' "witnessed-inference ANY refusal" group.
