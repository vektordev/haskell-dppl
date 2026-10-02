-- ofRealLeafCountingReadsPosition with the threshold passed as a leading
-- argument of a curried helper, `match 0.5 (readAttrs t)` (task
-- of-annotation-continuous-leaf-disables-enumeration). The applied lambda is
-- the helper's inner one, whose body reads the outer parameter `t`; the plan
-- engine binds `t` to its (deterministic) argument under a fresh name. main's
-- own first parameter is also called `t`, so binding the helper's `t` by its
-- source name would read the symbol instead of the threshold.
--   read 1, t = 0.5: q1 = 0.8 * 0.5  * (1 - Phi(0.5))  = 0.123415
--   read 2, t = 0.0: q2 = 0.6 * 0.25 * (1 - Phi(-0.5)) = 0.103844
p(0, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.785666, 0.0)
p(1, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.201533, 0.0)
p(2, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.012801, 0.0)
p(ANY, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(1.0, 0.0)
cdf(1, (2, [0.2, 0.8, 0.5, 0.5, 0.0, 1.0]), (2, [0.4, 0.6, 0.75, 0.25, 1.0, 2.0]))=(0.987199, 0.0)
