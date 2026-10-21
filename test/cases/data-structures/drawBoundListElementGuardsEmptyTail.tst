batched
p([(0.1, True), (0.2, False)])=(0.004850793548307211, 2.0)
p([(0.3, False), (0.4, True)])=(0.004389179509675788, 2.0)
-- A list of draw-bound tuple elements under --batched. The emptiness test of
-- the draw binding's witness guard reaches batched codegen as a select
-- (`select (not (sample == [])) True False`, bound by CSE), which used to be
-- emitted as an eager torch.where, so the non-empty arm's hoisted ANY guards
-- (`if not(isAny((sample)[0]))`) ran unguarded and indexed the empty tail at
-- the end of every sequence: "IndexError: InferenceList index out of range".
-- The batched backend now demotes a select over a structural condition back
-- to a Python if, and the census labels that "Batched:structural select", so
-- these rows always run on the batched backend. The inline spelling
-- (`(Normal, Uniform < 0.5) : main`) never hit it. This is the shape of a
-- marked point process (a draw-bound event consed onto the recursion). Task
-- batched-draw-bound-list-element-reads-empty-tail.
