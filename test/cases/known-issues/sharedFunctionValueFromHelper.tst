-- A helper whose result is a randomly selected function, bound once and
-- applied twice: both calls share one draw, so the idealized answer is
-- p((2, 3)) = 0.5 and p((4, 6)) = 0.5. The arrow-result eta expansion (task
-- arrow-result-main-entry-points) deliberately leaves `pick` alone here,
-- since expanding it would draw once per call. ForwardChaining no longer
-- crashes resolving `h` to `pick` (task
-- forward-chaining-named-function-returns-selected-lambda); the compile is
-- now refused by the central generate-backed guard, because `Var pick`
-- projects Deterministic and main's probability body would call pick_gen.
-- The capability gap is tracked by docs-repo task
-- shared-draw-of-random-function-value.
expect-failure: broken
p((2.0, 3.0))=(0.5, 0.0)
p((4.0, 6.0))=(0.5, 0.0)
