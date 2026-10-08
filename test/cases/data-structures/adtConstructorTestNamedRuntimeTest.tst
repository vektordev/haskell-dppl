backends: interpreter, julia, python
p(True)=(0.3, 0.0, False)
p(False)=(0.7, 0.0, False)
-- The source-level test of a constructor named Any, which the backends emit
-- as isAny_ beside the runtime's own isAny (adtConstructorNamedRuntimeTest).
-- Task adt-constructor-name-shadows-runtime.
