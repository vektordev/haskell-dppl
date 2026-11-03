p(True)=(0.5, 0.0)
p(False)=(0.5, 0.0)
-- Two counts produced by a recursive function with two recursive calls (one
-- per arm of a random condition), compared with each other. The enum
-- annotation unrolls a call on constant arguments as a tree, each level's
-- calls sharing the unrolling fuel, so both counts get a value domain and the
-- comparison is measured. p(True) = 0.5 * 0.75 + 0.5 * 0.25. Used to be
-- refused as "no closed form for its two random operands". Task
-- comparison-of-two-recursive-counts-refused.
