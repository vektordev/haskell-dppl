p((0.3, 0.7))=(1.0, 1.0)
p((ANY, 0.7))=(1.0, 1.0)
p((0.3, ANY))=(1.0, 1.0)
p((0.3, 0.6)) is impossible
p((ANY, 1.5)) is impossible
-- Design witnessed-per-query-capability, program B (from
-- deconstruction-inverse-marginals). Forward chaining seeded at the full
-- observation recovers x from the first slot; with that slot masked, the
-- variant re-witnesses x by inverting `1.0 - x` at the second. (ANY, 0.7)
-- used to refuse, naming x.
