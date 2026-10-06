-- main's parameter stays a type variable, so its comparison against the
-- query is IRCompiler.leafEqIR's run-time dispatch. A float must keep
-- OpApprox's tolerance there (0.30000000000000004 is one ulp from 0.3): a
-- plain OpEq for type variables would answer 0 on the first row, and the
-- former OpApprox-for-everything failed the Bool row in the interpreter.
-- Sibling of polymorphicParameterCompared (docs task
-- polymorphic-parameter-compared-as-float).
backends: interpreter, julia, python, batched
p(0.3, 0.30000000000000004)=(1.0, 0.0)
p(0.3, 0.31)=(0.0, 0.0)
p(True, True)=(1.0, 0.0)
p(True, False)=(0.0, 0.0)
p(7, 7)=(1.0, 0.0)
