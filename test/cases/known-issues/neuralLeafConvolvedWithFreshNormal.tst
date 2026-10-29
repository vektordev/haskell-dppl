-- A plan-enumerated (neural) *continuous* leaf combined arithmetically with a
-- fresh continuous draw in the same expression. The convolution of the leaf's
-- transported bound with the fresh Normal has no closed form in the
-- plan-guided transport, and the probability variant is dropped. Since
-- bottom-verdict-records-no-refusal-reason it records the reason that `+` has
-- no inference rule for a random operand and a Gaussian one (before, it
-- reported only "'main' has no compiled probability function"; contrast
-- neuralLeafComparedAgainstRandomThreshold, whose comparison arm *does* say
-- why). Multiplying instead of adding (`(snd o) * (Normal * 0.5)`) fails the
-- same way through the same channel.
--
-- This is the residue of tasks/neural-leaf-cannot-coexist-with-fresh-
-- continuous-randomness, whose broader claim -- that *any* fresh randomness
-- anywhere in a plan-enumerated body is refused -- was lifted by 81125d5 /
-- 86fb4cd. Fresh randomness in a sibling branch, under a discrete neural
-- gate, or downstream of a threshold on the leaf all compile exactly now;
-- only the arithmetic combination pinned here remains.
slow
expect-failure: refused "NeST computes no density or CDF for this combination"
