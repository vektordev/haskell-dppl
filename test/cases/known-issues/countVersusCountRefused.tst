-- Two counts produced by a recursive function, compared with each other.
-- Both have finite support, but neither carries a static value domain, so
-- the comparison is refused as two random operands. `cnt 2 == 1` (one side
-- deterministic) answers. Found by the publication-exploration C1 pilot
-- (W7, VLP's gt? predicate). Verified at b16b4d9 on dev. Docs task
-- comparison-of-two-recursive-counts-refused.
-- Idealized: p(True) = 0.5 * 0.75 + 0.5 * 0.25 = 0.5.
expect-failure: refused "has no closed form for its two random operands"
