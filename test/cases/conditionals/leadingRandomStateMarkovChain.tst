-- decreasingRecursionMarkovChain with the random state as the LEADING
-- argument of the self-call: enumerated like a last argument where the binding
-- engines refuse
-- (leadingEnumerableArgument, docs task
-- random-leading-argument-into-recursion-refused), so the answer does not
-- depend on parameter order. State distribution after three transitions from
-- False: 0.2, 0.34, 0.438.
p(True)=(0.438, 0.0)
p(False)=(0.562, 0.0)
