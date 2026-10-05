p((0.7, 0.3))=(1.0, 1.0)
p((0.7, ANY))=(1.0, 1.0)
p((ANY, 0.3))=(1.0, 1.0)
p((0.7, 0.6)) is impossible
p((ANY, 1.5)) is impossible
-- Design witnessed-per-query-capability; acceptance A of the design it
-- supersedes, deconstruction-inverse-marginals: a thin wrapper that destructures
-- a correlated tuple and swaps its slots re-targets which slot may be queried
-- ANY. Program B (maskComplementSlot) behind a swap: main's variant for
-- (ANY, _) re-witnesses x from the slot that is still observed. At
-- --marginalSlots 0 the (ANY, 0.3) row refuses naming the destructured binding.
