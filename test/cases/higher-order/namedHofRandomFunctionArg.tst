-- A randomly selected function passed to a *named* higher-order function with
-- a second, deterministic argument (task
-- named-hof-random-function-argument-miscompiled). `app g x` compiles as
-- `(app g) x`; the inner application's result is itself a function, and the
-- probabilistic-argument arm used to project `fst` out of that closure, so
-- probability/integrate died at run time (interpreter: "Fst is not a tuple",
-- Python: "App.generate() missing 1 required positional argument"). Same values
-- as the lambda-literal spelling, higher-order/arrowApplyRandomFunction.
-- Slow like that twin: its batched generate selects between two closures with
-- torch.where and raises (task batched-select-between-functions-raises).
slow
p(4.0)=(0.5, 0.0, False)
p(6.0)=(0.5, 0.0, False)
p(5.0) is impossible
cdf(3.0)=(0.0, 0.0)
cdf(5.0)=(0.5, 0.0)
cdf(6.0)=(1.0, 0.0)
