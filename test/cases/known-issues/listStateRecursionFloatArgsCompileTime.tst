-- docs ticket list-state-recursion-compile-time-per-float-argument: a
-- self-recursion over a (stack list, Int, Int) state with five recursive call
-- sites compiles in ~1.2 s when its three branch rates are literals, but with
-- the rates threaded through as Float arguments (pEnd pOpen pClose, passed on
-- unchanged) the compile grows ~6x per argument (0/1/2/3 arguments: 1.3 s /
-- 7.3 s / 45 s / > 4 min at 2a6a773). This is the three-argument spelling.
-- Found by exp-llm-lookahead-constraints (composition spelling 1).
expect-failure: hang
cap: 10s
