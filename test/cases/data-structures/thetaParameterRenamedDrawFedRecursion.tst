-- A ThetaTree helper parameter (u) named unlike its argument (th), called in
-- a draw whose value feeds the recursive call. The theta read is an anchor of
-- the inverse through `g th`, materialized at the call site under the
-- callee's parameter name: "Could not find name in TypeEnv: u". Found by the
-- publication-exploration density probes. Docs task
-- callee-body-name-sensitive-across-call.
p([], ThetaTree [1.0] [])=(0.5, 0.0)
p([1.5], ThetaTree [1.0] [])=(0.08801633169107488, 1.0)
p([1.5, 0.2], ThetaTree [1.0] [])=(0.012748793897978592, 2.0)
