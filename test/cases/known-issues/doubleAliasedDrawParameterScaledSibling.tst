-- A Uniform draw read through two aliases, beside a fresh Normal scaled by the
-- alias. The right density is 1 * N(b; 0, a) = phi(b / a) / a. One alias
-- (draw x = z in (x, x * Normal)) answers it. With two, the outer witness's
-- change of variables also carries |1 / fst sample|, the Jacobian of the
-- mult inverse that recovers the Normal, so the answer is 1/a times too large:
-- 1.4731 at (0.5, 0.2), 4.6351 at (0.25, 0.2). Found by Slow.RewriteSequences
-- seed 20261017 (probe5, draw-intro then alias-intro). Docs task
-- double-aliased-draw-parameter-scaled-sibling-double-jacobian.
expect-failure: broken
p((0.5, 0.2))=(0.73654028, 2.0)
p((0.25, 0.2))=(1.15876621, 2.0)
