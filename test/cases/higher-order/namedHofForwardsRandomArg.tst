-- A named function applying its function parameter to a random parameter
-- (task helper-calls-helper-random-arg, the higher-order form). Was a known
-- issue ("tagged invocation") until task binding-resolver-one-application-rule:
-- the set-witness engine enters the call through the function parameter's
-- bound lambda. Its inlined twin is higher-order/arrowApplyLambdaArg.
-- Normal + 1.0.
p(0.5)=(0.35206533, 1.0, False)
p(1.0)=(0.39894228, 1.0, False)
p(ANY)=(1.0, 0.0, False)
cdf(1.0)=(0.5, 0.0)
