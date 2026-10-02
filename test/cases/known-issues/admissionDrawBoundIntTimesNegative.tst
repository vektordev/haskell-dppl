-- Found by the admission-totality fuzz oracle (docs task
-- fuzz-admission-oracle-bugs, item 9). A draw-bound enumerable Int multiplied
-- by an Int literal (any sign; `v * 6` crashes the same way): `main` is typed Integrate, and the compile dies
-- folding the inverse's derivative, `OpDiv (VFloat 1.0) (VInt (-6))` -- a
-- Float numerator over an Int factor. The inline spelling `d * (-6)`, with no
-- draw, answers correctly. Idealized: p(-6) = (0.5, 0), p(-12) = (0.5, 0).
expect-failure: diagnostic "Error during forceOp optimizer: OpDiv"
