-- maskSwappedWrapper (let-bindings corpus) with f's call bound by `draw z = f`
-- first, which is the rewrite-invariance net's draw-intro variant. (0.7, 0.6)
-- needs x = 0.3 and x = 0.6 at once, so it is impossible, and the
-- un-rewritten program says so. Verified at ed239ed on dev, interpreter: this
-- form answers 1.0 at dim 1 by default. At --marginalSlots 0 it refuses
-- ("binding 'x' is unobserved"), so f's per-mask variants turn the old
-- refusal into a silent wrong answer. Task
-- mask-variants-silence-reread-refusal-into-wrong-result.
expect-failure: broken
p((0.7, 0.6)) is impossible
