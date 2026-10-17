-- A Markov chain over N marks spelled with one literal recursive call per
-- (prev, next) pair, its branch conditions comparing Uniform against a
-- Float parameter. 0.24 s at N = 2, 12 s at N = 3 (b16b4d9). With the
-- constant 0.5 in place of p the same family is 0.09 s / 0.24 s, and a
-- generate-only compile (-P -I) is as slow as the full one, so the cost is
-- before IRCompiler. The research programs (theta-valued rates, a mixture
-- duration per mark) took 2.5 s / 124 s at N = 2 / 3, and a 16-mark
-- renewal chain 1876 s. Found by the publication-exploration density and
-- C4 work. Docs task markov-branch-random-rate-compile-exponential.
expect-failure: growth above polynomial 3
knob: N = 2, 3, 4
metric: alloc
cap: 1.5 s, 2000 MB
