-- A list of draw-bound tuple elements under --batched. The emptiness test of
-- the draw binding's witness guard reaches codegen as
-- where_anchored(logical_not(asmask(sample == [])), True, False), which
-- `structural` does not recognise, so the non-empty arm's hoisted ANY guards
-- (`if not(isAny((sample)[0]))`) run unguarded and index the empty tail at
-- the end of every sequence: "IndexError: InferenceList index out of range".
-- The inline spelling (`(Normal, Uniform < 0.5) : main`) batches and matches
-- these rows; the interpreter and scalar Python answer them. This is the
-- shape of a marked point process (a draw-bound event consed onto the
-- recursion), found by the publication-exploration follow-up while checking
-- whether the C4 TPP program batches. Verified at 4f496c1 on dev. Docs task
-- batched-draw-bound-list-element-reads-empty-tail.
backends: batched
expect-failure: broken
p([(0.1, True), (0.2, False)])=(0.004850793548307211, 2.0)
p([(0.3, False), (0.4, True)])=(0.004389179509675788, 2.0)
