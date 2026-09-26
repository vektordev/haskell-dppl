-- The constant is outside exp's image, so the inverse's applicability guard
-- fails: no x makes exp x == -1.0, the True arm is unreachable (1.0 is
-- impossible rather than a density) and the False outcome is certain -- the
-- WFull world of equalityWorlds, not the complement of a point.
p(0.0)=(1.0, 0.0, False)
p(1.0) is impossible
