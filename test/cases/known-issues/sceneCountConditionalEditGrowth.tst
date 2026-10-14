-- "If at least two objects are metal, make every metal object rubber" over an
-- N-slot product read. The count is a flat sum of per-slot indicators, the
-- shape plan-flat-sum-over-product-exponential made linear for a counting
-- *query*; as the guard of a Scene-valued edit the -O2 module still grows
-- 2.4-4.4x per slot (48 KB, 70 KB, 169 KB, 742 KB, 2.0 MB at N = 2..6) at
-- 8b8223d. A saturating-counter spelling (`bump c o`, min(c, 2)) fails the
-- same way. The CLEVR version (10 slots) runs out of 2 GB. Found by
-- experiments_nest symbolic-latent-scene-editing. Docs task
-- scene-count-conditional-edit-exponential.
expect-failure: growth above polynomial 2
knob: N = 2, 3, 4, 5
metric: code-size
