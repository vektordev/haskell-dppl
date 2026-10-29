-- higher-order/lambdaThetaInverse with inner's parameter renamed from
-- `thetas` to `ts`. The theta read is an anchor of the inverse through the
-- call, materialized at the call site; it used to be compiled under the
-- callee's parameter name, which only the caller's namesake made bind ("Could
-- not find name in TypeEnv: ts"). Docs task
-- callee-body-name-sensitive-across-call.
p(2.5, ThetaTree [2.0, 0.0, 0.0, 0.0] [])=(1.0, 1.0)
p(0.5, ThetaTree [2.0, 0.0, 0.0, 0.0] [])=(0.0, 1.0)
cdf(2.5, ThetaTree [2.0, 0.0, 0.0, 0.0] [])=(0.5, 0.0)
cdf(3.0, ThetaTree [2.0, 0.0, 0.0, 0.0] [])=(1.0, 0.0)
