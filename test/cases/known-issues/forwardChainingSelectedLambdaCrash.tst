-- ForwardChaining's constructEquivalenceClauses crashes
-- when a *named top-level function*'s return value is an if-selected lambda,
-- since its callee-side resolution expects the chain name to already be a
-- Lambda. `b` is deterministically True here, so the idealized result is
-- either a correct compile of the single statically-known branch (Normal
-- shifted by 1.0), or a clean, named refusal -- not the current uncaught
-- `error` panic.
expect-failure: diagnostic "to be a Lambda"
