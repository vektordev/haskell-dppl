-- Found by the admission-totality fuzz oracle (docs task
-- fuzz-admission-oracle-bugs, item 3). An if-selected function value whose
-- else-arm is a lambda projected out of a tuple: `main` is typed Integrate,
-- and the compile dies in compareValueExpr on the arrow type. The sibling with
-- two lambda-literal arms compiles (the pointwise-lifted arrow mixture) and
-- answers p(1.0) = 0.5. Idealized: p(1.0) = (0.5, 0), p(3.0) = (0.5, 0).
expect-failure: diagnostic "Comparison not implemented for type: TArrow"
