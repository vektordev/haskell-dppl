-- A function forwarding its predicate parameter to `observe` (task
-- observe-predicate-as-argument), as observeKeyword. Was a known issue
-- ("tagged invocation") until task binding-resolver-one-application-rule: the
-- call binds its random leading argument first, and the set-witness engine
-- enters `p v` through the predicate parameter's bound lambda.
p(Right 1)=(0.3, 0.0, False)
p(Left ())=(0.7, 0.0, False)
p(Right 0) is impossible
