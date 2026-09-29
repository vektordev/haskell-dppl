backends: python
expect-failure: broken
p(True)=(0.3660323412732292, 0.0)
p(False)=(0.6339676587267709, 0.0)
-- 100 nested `if`s. The scalar Python backend emits each nested conditional
-- as a nested `if` statement, one indentation level apiece, and CPython
-- refuses more than 100 levels: the module fails to load with
-- "IndentationError: too many levels of indentation" (90 nested ifs load).
-- The same ceiling applies with an enumerated `draw` around the chain, since
-- the deep-line spill emits the enumerated body as statements too.
-- Idealized value: 0.99^100. `backends: python` is load-bearing: the
-- interpreter already returns the idealized value. Task
-- python-nested-conditionals-exceed-indentation-limit.
