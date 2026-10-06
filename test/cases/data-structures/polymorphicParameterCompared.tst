-- main's parameter is left a type variable (nothing in the body constrains
-- it), so its comparison against the query cannot be OpApprox, the float
-- comparison: the interpreter refuses OpApprox on anything but two floats,
-- and every Bool or Int query failed with "Approx can only evaluate on two
-- floats". A type-variable leaf now dispatches at run time (IRCompiler.leafEqIR):
-- OpApprox for a float, OpEq otherwise. Formerly the known-issues pin
-- polymorphicParameterComparedAsFloat; docs task
-- polymorphic-parameter-compared-as-float.
backends: interpreter, julia, python, batched
p((True, True), True)=(1.0, 0.0)
p((True, False), True)=(0.0, 0.0)
p((False, False), False)=(1.0, 0.0)
p((3, 3), 3)=(1.0, 0.0)
p((3, 4), 3)=(0.0, 0.0)
p((0.5, 0.5), 0.5)=(1.0, 0.0)
p((0.5, 0.25), 0.5)=(0.0, 0.0)
p(((1, True), (1, True)), (1, True))=(1.0, 0.0)
p(((1, True), (1, False)), (1, True))=(0.0, 0.0)
