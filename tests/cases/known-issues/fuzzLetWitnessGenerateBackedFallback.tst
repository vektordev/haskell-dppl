-- Found by the let/set-witness fuzz generator (~7% of its crashes): probability-mode
-- compilation of an enumerated conditional reaches a generate-backed
-- fallback, since forward-compiling the expression draws fresh randomness
-- rather than being deterministic given the enumerated latents. Idealized
-- behavior: a graceful `Left` refusal for probability/integrate while
-- `generate` still compiles -- no numeric value is at issue.
expect-failure: diagnostic "probability-mode compilation reached a generate-backed fallback"
