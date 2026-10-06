-- Sibling of pointFreeAliasCalledWithArgument: a transitive alias (alias2 = alias =
-- coin), and three independent invocations of the same lambda in one body -- two
-- through aliases, one direct. Each must get its own tagged copy of coin's body,
-- so the three draws stay independent: p(True; x) = x * 0.5 * 0.8.
p(True, 0.3)=(0.12, 0.0)
p(False, 0.3)=(0.88, 0.0)
p(True, 1.0)=(0.4, 0.0)
