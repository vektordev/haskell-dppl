-- The user-ADT sibling of arrowApplyEitherProjected: a field accessor applied
-- to a literal constructor application, where the field holds a function.
-- Unlike the Either and tuple shapes this one was not refused at compile time
-- -- the accessor was dropped entirely and the whole VADT applied, dying in
-- the interpreter with "Expression is not a closure". Reducing `a k` to the
-- lambda it denotes before annotation removes the shape before that path is
-- reached. Deterministic: (\x -> x + 1.0) 3.0 = 4.0.
backends: interpreter, julia, python, batched
p(4.0)=(1.0, 0.0, False)
p(5.0) is impossible
cdf(3.0)=(0.0, 0.0)
cdf(4.0)=(1.0, 0.0)
cdf(5.0)=(1.0, 0.0)
