-- A theta read directly in a callee compiled by the set-valued witness
-- engine (a comparison), the caller binding the parameter's name `ts` to
-- another ThetaTree: the anchor read the caller's `ts` (theta 5.0, p(True)
-- answered 0.0), and with no `ts` in the caller the compile crashed on an
-- unbound name. Docs task theta-anchor-through-callee-local-binding.
p(True, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.7000000000000002, 0.0)
p(False, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.2999999999999998, 0.0)
