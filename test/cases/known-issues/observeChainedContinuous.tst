-- Verified at commit 8bb0a44 on dev: chaining a second observation onto the Maybe
-- produced by a first, over a continuous base. The discrete twin compiles and
-- is right (either-maybe/observeChainedDiscreteInline), and so does the same
-- truncation to (0, 1) written against the Normal directly
-- (either-maybe/observeTwoSidedInterval). Here the set-witness fallback cannot
-- propagate the observation onto m through `fromRightPartial m` and refuses.
-- Idealized: p(Right 0.5) = (phi(0.5), 1) = (0.35206533, 1.0),
--   p(Right 1.5) = 0, p(Left ()) = 1 - (Phi(1) - Phi(0)) = (0.65865525, 0.0),
--   p(Right ANY) = (0.34134475, 0.0).
expect-failure: diagnostic "neither point-invertible"
