-- A helper forwarding its random parameter to another helper (task
-- helper-calls-helper-random-arg). Was a known issue ("tagged invocation")
-- until task binding-resolver-one-application-rule: the set-witness engine
-- now consumes a named callee's binding. Uniform + 3.0.
p(3.5)=(1.0, 1.0, False)
p(5.0) is impossible
p(ANY)=(1.0, 0.0, False)
cdf(3.5)=(0.5, 0.0)
cdf(5.0)=(1.0, 0.0)
