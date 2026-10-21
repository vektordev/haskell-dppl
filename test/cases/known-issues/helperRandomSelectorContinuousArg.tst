-- Was a ForwardChaining crash (a named helper returning an if-selected
-- lambda). Since task arrow-result-main-entry-points eta-expands `mk` into
-- `mk b p = (if b then .. else ..) p`, the compile no longer crashes and the
-- program is exactly the first-order `mk b x = if b then x + 1.0 else x * 2.0;
-- main = mk (Uniform < 0.5) Normal`, whose probability variant is refused:
-- the set-valued witness engine cannot propagate the observation onto the
-- random Bool argument past the continuous one. The idealized answer is the
-- even mixture of N(1, 1) and N(0, 2). Tracked by docs-repo task
-- helper-random-selector-with-continuous-argument-refused.
expect-failure: refused "set-valued witness construction failed"
