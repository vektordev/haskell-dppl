-- A named function whose random argument is a point witness at the head of the
-- list it returns. The let spelling of the same program,
-- `let x = Normal in x : [x + Normal]`, compiles and gives the idealized value
-- p([0.0, 0.0]) = (0.15915494, 2); called through a named top-level function it
-- throws instead. Blocks every recursive trajectory program, including the
-- OU chain (known-issues/ouChainRecursive) and design diffusion-models-wishlist's
-- M2 denoiser chain.
expect-failure: diagnostic "set-valued witness construction failed"
