-- Found by the admission-totality fuzz oracle (docs task
-- fuzz-admission-oracle-bugs, item 4). The negation of a log-normal keeps the
-- PLogNormal family in the modality engine, but its support is negative, so
-- toIRLogNormalParams has no (mu, sigma) to read off and crashes the compile.
-- Idealized: the density of -X for X ~ LogNormal(0, 1), p(-1.0) =
-- (0.3989422804014327, 1).
expect-failure: diagnostic "toIRLogNormalParams"
