-- Deterministic sibling of namedHelperReturnsSelectedLambda: `(mk True) 3.0`
-- is 4.0. Was the known-issues pin forwardChainingSelectedLambdaCrashDeterministic:
-- the interpreter already answered, but the emitted Python called
-- `mk.generate(True, 3.0)` with one argument too many for mk's generate. mk is
-- now eta-expanded to take both (task arrow-result-main-entry-points).
p(4.0)=(1.0, 0)
p(3.0) is impossible
