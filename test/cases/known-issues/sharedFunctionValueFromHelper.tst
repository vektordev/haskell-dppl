-- A helper whose result is a randomly selected function, bound once and
-- applied twice: both calls share one draw, so the idealized answer is
-- p((2, 3)) = 0.5 and p((4, 6)) = 0.5. The arrow-result eta expansion (task
-- arrow-result-main-entry-points) deliberately leaves `pick` alone here,
-- since expanding it would draw once per call, and ForwardChaining still
-- crashes resolving `h` to `pick`, which is not a lambda. Tracked by docs-repo
-- task forward-chaining-named-function-returns-selected-lambda.
expect-failure: diagnostic "to be a Lambda"
