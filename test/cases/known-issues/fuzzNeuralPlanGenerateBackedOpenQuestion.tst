-- Found by the neural/plan-enumeration fuzz generator (68% of its crashes): a nested
-- enumerated conditional gated by a neural Bool read hits the
-- generate-backed-body guard. Whether this program *should* compile is an
-- open design question in the doc itself (it resembles the corpus's own
-- planEnumInlineBool.ppl, which does compile) -- no idealized value is
-- pinned, only that the current uncaught crash is wrong regardless of which
-- way that question is resolved.
expect-failure: crash
