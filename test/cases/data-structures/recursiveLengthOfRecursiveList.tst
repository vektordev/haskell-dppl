p(True)=(0.75, 0.0)
p(False)=(0.25, 0.0)
-- A recursive consumer (len) of a recursively generated random list. The enum
-- annotation unrolls `rollout 3` (constant arguments, one recursive call) into
-- its list domain {[], [1], [1,1], [1,1,1]}, so len's argument is enumerated.
-- Lengths 0/1/2/3 have mass 0.5/0.25/0.125/0.125. Used to be refused by the
-- set-valued witness engine ("set-valued witness construction failed for the
-- binding of 'xs'"). Task recursive-consumer-of-recursive-random-list-refused.
