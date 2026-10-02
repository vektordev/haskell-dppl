-- Found by the admission-totality fuzz oracle (docs task
-- fuzz-admission-oracle-bugs, item 8). A constructor test over a value built
-- from a draw-bound Uniform through `exp`: `main` is typed Integrate, and the
-- compile dies in the optimizer (`forceUnaryOp`), folding the inverse of `exp`
-- applied to the wildcard the test leaves in the field. Idealized: the test
-- always holds, p(True) = (1.0, 0).
expect-failure: diagnostic "Error during forceUnaryOp optimizer"
