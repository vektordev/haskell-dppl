-- Two counts produced by a recursive function with two recursive calls,
-- compared with each other, both deeper than the enum annotation unrolls. A
-- call on constant arguments unrolls as a tree within a fixed fuel (each
-- level's calls share it), so a two-call recursion reaches about six levels:
-- `cnt 2 > cnt 1` and `cnt 8 > cnt 1` (one side enumerated, the other
-- measured by its CDF) answer, but here neither side has a value domain and
-- the comparison is refused as two random operands. Docs task
-- comparison-of-two-recursive-counts-refused (residual).
-- Idealized: p(True) = P(Bin(9, 0.5) > Bin(8, 0.5)) = 0.5.
expect-failure: refused "has no closed form for its two random operands"
