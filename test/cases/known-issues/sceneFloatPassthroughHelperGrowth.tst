-- A per-slot recolour over an N-slot product read, the object's Float leaf
-- passed through. Every slot is edited independently, yet the -O2 module
-- grows ~3x per slot (35 KB, 73 KB, 203 KB, 643 KB at N = 2..5; N = 6 does
-- not finish in 60 s under a 2 GB cap) at 8b8223d. Without the Float field
-- the same program is linear (79 KB at N = 6, 100 KB at N = 8). The CLEVR
-- scene version (4 discrete fields + a 3-Float Position, 10 slots) runs out
-- of 2 GB. Found by experiments_nest symbolic-latent-scene-editing. Docs
-- task scene-float-passthrough-edit-exponential.
expect-failure: growth above polynomial 2
knob: N = 2, 3, 4
metric: code-size
