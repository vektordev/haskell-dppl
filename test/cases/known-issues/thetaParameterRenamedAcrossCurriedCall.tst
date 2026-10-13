-- higher-order/lambdaThetaInverse with inner's parameter renamed from
-- `thetas` to `ts`: the compile throws "Could not find name in TypeEnv". It
-- compiles when the caller's argument and the callee's parameter share a name
-- (both `thetas`, or both `ts`), so the callee's body is compiled where only
-- the caller's names are bound. A Float parameter (`inner ts x = x + ts`)
-- compiles under either name. Verified at 3b72682 on dev. Found by the
-- rewrite-invariance net's alpha-rename family. Docs task
-- callee-body-name-sensitive-across-call.
expect-failure: diagnostic "Could not find name in TypeEnv"
p(2.5, ThetaTree [2.0, 0.0, 0.0, 0.0] [])=(1.0, 1.0)
