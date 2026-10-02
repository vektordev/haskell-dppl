-- Found by the admission-totality fuzz oracle (task
-- admission-totality-property; docs task fuzz-admission-oracle-bugs, item 1).
-- `main` is typed Integrate and compiles, but its probability function dies at
-- run time with `Prelude.!!: index too large`: the field accessor `mb` is
-- evaluated on the `Zero` value of the enumerated draw, where it has no
-- field, even though it sits under the `isTwo v0` test. Idealized: both
-- outcomes of the draw give False, so p(False) = 1.
backends: interpreter
expect-failure: broken
p(False)=(1.0, 0.0)
