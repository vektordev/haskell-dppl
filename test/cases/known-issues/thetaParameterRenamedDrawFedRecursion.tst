-- callee-body-name-sensitive-across-call, reached without a curried call: a
-- ThetaTree helper parameter (u) named unlike its argument (th), called in a
-- draw whose value feeds the recursive call. Both the probability and the
-- integrate compile throw the IRCompiler invariant "Could not find name in
-- TypeEnv: u". Renaming u to th compiles; so does passing prev instead of e,
-- or dropping the draw. Found by the publication-exploration density probes
-- (an observed-mark Markov point process). Verified at b16b4d9 on dev.
expect-failure: diagnostic "Could not find name in TypeEnv"
