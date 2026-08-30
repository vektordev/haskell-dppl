-- Degenerate same-latent shape: both tuple slots recover the one latent x, so
-- the support is the manifold b == 2a. Companion witness of
-- multi-path-recovery-unmaterialized-crash; it used to crash on the
-- unoptimized path only, so keep this pinned at both optimization levels.
backends: interpreter, julia, python, batched
p((0.3, 0.6))=(1.0, 1.0, False)
p((0.3, 0.7))=(0.0, 1.0, True)
p((1.4, 2.8))=(0.0, 1.0, True)
