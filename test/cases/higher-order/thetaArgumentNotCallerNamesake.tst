-- The other side of thetaParameterRenamedAcrossCurriedCall: the caller binds
-- the callee's parameter name `ts` to a different ThetaTree than the one it
-- passes. The theta anchor read `ts` by name and so took the caller's (theta
-- 5.0, p(2.5) answered 0.0); it must read the argument `thetas` (theta 2.0).
-- Docs task callee-body-name-sensitive-across-call.
p(2.5, ThetaTree [5.0] [], ThetaTree [2.0] [])=(1.0, 1.0)
p(5.5, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.0, 1.0)
cdf(2.5, ThetaTree [5.0] [], ThetaTree [2.0] [])=(0.5, 0.0)
cdf(3.0, ThetaTree [5.0] [], ThetaTree [2.0] [])=(1.0, 0.0)
