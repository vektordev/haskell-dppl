-- A comparison slot ahead of the slot that point-recovers x = s1 / 3: the
-- comparison's indicator path carries x's recovery derivative, so the
-- density picks up |1/3| twice. p((True, 0.5)) answers 0.043716 = phi(0.5;
-- 0, 3) / 3, while p((ANY, 0.5)) answers the right 0.131147, and so does the
-- order (x, x > 0.0). With exp Normal and (x > 2.0, x) at 3.0 the error is
-- 1/x. Verified at b16b4d9 on dev. Docs task
-- forwardchaining-path-derivative-includes-other-latents-jacobian.
-- Idealized: phi(0.5; 0, 3) = 0.131147.
expect-failure: broken
p((True, 0.5))=(0.1311466, 1.0)
