backends: python
expect-failure: broken
p(Nil)=(0.7, 0.0)
-- A constructor named `Any` gets the test `isAny`, which the emitted module
-- defines over the runtime's own `isAny` (the wildcard test). The new one
-- calls `isAny` first, i.e. itself: every probability query raises
-- "RecursionError: maximum recursion depth exceeded". Julia overflows its
-- stack the same way; `backends: python` because the harness evaluates no
-- Julia pins, and the interpreter already gives the idealized value. Found
-- by the typed fuzz generator's generated ADT names (prop_Fuzz_BackendsAgree).
-- Task adt-constructor-name-shadows-runtime.
