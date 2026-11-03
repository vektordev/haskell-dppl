-- The (ANY, _, _) mask variant of a deterministic-condition if root is
-- if c then [ANY] else ANY : [x, x]. x is read twice in the else arm, so it
-- needs the per-arm witness split, and the pruned then arm leaves x dead, which
-- leaves the split without an inverse: the mask is Bottom and the query a
-- runtime refusal. The value is x : [x, x], so p([ANY, a, a]) = phi(a), dim 1,
-- as on draw x = Normal in x : [x, x]. Docs task
-- if-root-mask-variant-dead-arm-blocks-witness-split.
expect-failure: broken
p([ANY, 0.5, 0.5])=(0.35206533, 1.0)
