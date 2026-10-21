-- A Uniform draw read through two aliases, beside a fresh Normal scaled by the
-- alias: 1 * N(b; 0, a) = phi(b / a) / a. With two aliases the outer witness's
-- change of variables used to also carry |1 / fst sample|, the Jacobian of
-- the mult inverse that recovers the Normal (1/a too large). Found by
-- Slow.RewriteSequences seed 20261017 (probe5, draw-intro then alias-intro).
-- Docs task double-aliased-draw-parameter-scaled-sibling-double-jacobian.
p((0.5, 0.2))=(0.73654028, 2.0)
p((0.25, 0.2))=(1.15876621, 2.0)
