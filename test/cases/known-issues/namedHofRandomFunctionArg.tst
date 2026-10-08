-- Verified at d258b02 on dev (ticket named-hof-random-function-argument-miscompiled):
-- a randomly selected function passed to a *named* higher-order function
-- compiles, but probability/integrate call `app.generate` with the lifted
-- mixture lambda as its only argument and then index and apply the result.
-- The interpreter stops with "Fst is not a tuple: VFloat 0.5", Python with
-- "App.generate() missing 1 required positional argument: 'x'". The same
-- program with the callee inlined as a lambda literal answers correctly
-- (higher-order/arrowApplyRandomFunction). Rows are the idealized values.
expect-failure: broken
p(4.0)=(0.5, 0.0, False)
p(6.0)=(0.5, 0.0, False)
p(5.0) is impossible
cdf(5.0)=(0.5, 0.0)
