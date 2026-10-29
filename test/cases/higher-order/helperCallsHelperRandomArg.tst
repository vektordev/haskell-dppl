-- A helper forwarding its random parameter to another helper (task
-- helper-calls-helper-random-arg). Was a known issue ("tagged invocation")
-- until task binding-resolver-one-application-rule: the set-witness engine
-- now consumes a named callee's binding. Uniform + 3.0.
-- p(3.0) and p(4.0) pin the support edges, both closed with density 1; the
-- sampler window straddles an edge, so those rows opt out of it.
p(3.5)=(1.0, 1.0, False)
p(5.0) is impossible
p(3.0)=(1.0, 1.0, False) no-sample
p(4.0)=(1.0, 1.0, False) no-sample
p(ANY)=(1.0, 0.0, False)
cdf(3.5)=(0.5, 0.0)
cdf(5.0)=(1.0, 0.0)
