-- A bare neural Int read over an explicit V-value domain. The emitted module
-- is linear in V (about 60 bytes per value) but the compile's allocation is
-- about V^2: 115 MB / 353 MB / 1.5 GB / 6.2 GB at V = 500 / 1000 / 2000 /
-- 4000 (0.1 / 0.2 / 0.8 / 2.5 s), at 3f3726a. Not the agreement's V^2 (fixed in
-- 5303e29): there is no comparison here. `main ctx t = draw c = lm ctx in
-- t == c` is cheap (81 MB at V = 4000), so it is something the plain read's
-- variants do per value. Docs task neural-int-read-compile-quadratic-in-domain
-- (found by experiments_nest llm-decoding-operator-stack: row 1's compile
-- 31 s at V = 8000, unfinished after 20 min at V = 50257).
expect-failure: growth above linear
knob: V = 250, 500, 1000, 2000
metric: alloc
