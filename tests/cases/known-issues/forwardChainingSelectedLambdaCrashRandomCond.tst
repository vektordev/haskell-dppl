-- Same root cause as forwardChainingSelectedLambdaCrash,
-- with `b` now itself random (Uniform < 0.5). Idealized result is a 50/50
-- mixture of (Normal+1.0) and (Normal*2.0), or a clean named refusal if that
-- needs the arrow-lift mixture combinator on top of this fix. The doc states
-- this variant "fails identically" without requoting the exact message for
-- this specific program, so the mechanism is pinned generically here rather
-- than to the crash's exact text.
expect-failure: crash
