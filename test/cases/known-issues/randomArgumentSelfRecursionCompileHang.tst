-- docs ticket random-argument-self-recursion-compile-hang: a self-recursion
-- that stops only on a coin and passes a random argument to itself never
-- finishes compiling the probability or integrate function; modality inference
-- completes and IR compilation runs into the cap. The argument need not be read
-- (here `s` is unused); a Bool coin, an Int if-coin and `Normal` all hang. A
-- deterministic argument (`gen s`, `gen (not s)`) compiles at once, and adding a
-- decreasing counter turns it into the central generate-backed refusal.
-- Idealized p([True]) = 0.9 * 0.1 = 0.09.
expect-failure: hang
cap: 3s
