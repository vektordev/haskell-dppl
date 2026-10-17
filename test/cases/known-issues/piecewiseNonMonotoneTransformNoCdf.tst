-- A piecewise transform whose two arms are each monotone but fold onto the
-- same range. The density is right (p(1.0) = phi(1) + phi(-0.5)/2 =
-- 0.418003), but the cumulative variant is refused: "the observation has no
-- set-valued inverse in cumulative mode". Found by the
-- publication-exploration inversion explorer. Verified at b16b4d9 on dev.
-- Docs task piecewise-nonmonotone-transform-no-cdf.
-- Idealized: cdf(1.0) = Phi(1) - Phi(-0.5) = 0.532807.
expect-failure: refused "has no set-valued inverse in cumulative mode"
