p(True)=(0.4, 0.0)
p(False)=(0.6, 0.0)
-- The list form of recursiveCountComparison (VLP's gt? between two object
-- counts): each count recurses over a constant list of probabilities. The
-- left count is 0/1/2 with mass 0.4/0.5/0.1, the right 0/1 with 0.6/0.4, so
-- p(True) = 0.6 * 0.6 + 0.4 * 0.1. Task comparison-of-two-recursive-counts-refused.
