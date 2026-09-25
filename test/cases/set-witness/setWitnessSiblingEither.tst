-- The tuple sits under a unary constructor: the transport passes through
-- fromRight and then fst, and the sibling is dropped just the same.
backends: interpreter, julia, python, batched
p(Right (0.3, 1.0)) is impossible
p(Right (0.7, 0.0)) is impossible
p(Right (0.7, 1.0))=(1.0, 1.0)
p(Right (0.7, ANY))=(1.0, 1.0)
p(Left ())=(0.5, 0.0)
