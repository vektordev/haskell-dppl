backends: interpreter, python
expect-failure: broken
cdf(2)=(1.0, 0.0)
cdf(5)=(1.0, 0.0)
-- Idealized values. At 1860933 the interpreter answers (0.0, 0.0, False) at
-- both points (cdf(1) = 1.0 is right). Task head-cdf-uses-equality.
