-- Task plan-fold-result-through-helper-crashes. A deterministic helper
-- applied to a plan-path fold's result (`isValid (checksumSum 1 ds)`) takes
-- the compile down with an uncaught `error`: plan-guided lazy enumeration
-- refuses the call argument (`Apply`) instead of treating the helper as a
-- deterministic post-map of the fold's value. At depth <= 3 the list is under
-- the materialization budget, dense enumeration applies, and it compiles --
-- so the repro needs depth 4. Found by experiments_nest
-- barcode-checksum-decoding (exp-barcode-checksum-decoding) at f4ea495.
expect-failure: diagnostic "call argument is neither a plan slice"
