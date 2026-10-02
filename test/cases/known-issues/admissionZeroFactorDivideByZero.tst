-- Found by the admission-totality fuzz oracle (docs task
-- fuzz-admission-oracle-bugs, item 6). An Int product whose constant factor is
-- zero only after folding (`4 * 0`) multiplies an enumerable die inside a
-- comparison: `main` is typed Integrate and the compile dies with Haskell's
-- `divide by zero`, the inverse of the multiplication dividing by the folded
-- factor. A literal `0 * d` is refused gracefully (generate-backed) instead.
-- Idealized: the zero term vanishes, so p(True) = P(d1 < d3) = 0.25.
expect-failure: diagnostic "divide by zero"
