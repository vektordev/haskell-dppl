-- An EAN-style weighted checksum fold (weights 1,3,1,3,...) over a neural
-- digit list of depth 4, returning the Int sum. main's integrate and forward
-- each emit the whole sample-independent enumeration: the same 152 DP
-- statements and the same per-sum-value mass terms, differing only in the 73
-- read-off guards (`k == sample` vs `not (k > sample)`). 187 KB here at
-- 29afbca, about 53 KB of it per method; sharing the enumeration between the
-- two would bring it to roughly 135 KB. Re-rolling the per-level DP (docs
-- task plan-rerolling-recursion-levels) would also shrink it, so check which
-- fix tripped this. Docs task discrete-cdf-and-pmf-emit-the-enumeration-twice.
expect-failure: code-size above 160 KB
