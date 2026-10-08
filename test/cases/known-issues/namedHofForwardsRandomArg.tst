-- Verified at d258b02 on dev (ticket helper-calls-helper-random-arg, the
-- higher-order form): a named function applying its function parameter to a
-- random parameter has no probability path, the same "tagged invocation"
-- refusal as a helper forwarding a random argument to a helper. The verdict
-- is PNormal and correct; the inlined form (\f -> f Normal) (\x -> x + 1.0)
-- answers (higher-order/arrowApplyLambdaArg). twice and compose refuse the
-- same way. Idealized: Normal + 1.0, p(0.5) = 0.3520653267642995.
expect-failure: refused "tagged invocation"
