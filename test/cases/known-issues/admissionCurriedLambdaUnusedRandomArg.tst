-- Found by the admission-totality fuzz oracle (docs task
-- fuzz-admission-oracle-bugs, item 7). A curried lambda literal applied to a
-- deterministic first argument and a random second one it ignores: `main` is
-- typed Integrate, and the compile dies on the internal invariant `Could not
-- find name in TypeEnv: a` -- the first parameter is read in a scope that never
-- bound it. Idealized: `main` is the constant 0.0, p(0.0) = (1.0, 0).
expect-failure: diagnostic "Could not find name in TypeEnv"
