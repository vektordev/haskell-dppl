-- A continuous `==` reached through an InjF with an
-- applicability guard (here `exp`, whose inverse guards `b > 0`) crashes on
-- the False arm -- the False-polarity VAnyExcept sentinel gets substituted
-- into the guard itself (`b > 0` becomes `VAnyExcept > 0.0`), which has no
-- VAnyExcept case, at both -O0 and -O2. `plus`/`mult`/`neg`/`double` have
-- `IRConst True` guards and so don't hit this. Idealized, stated exactly in
-- the doc's acceptance criteria: exp(x) == 1.0 iff x == 0.0, a
-- null-probability event, so main is 0.0 almost surely: p(0.0) = (1.0, 0.0).
expect-failure: broken
p(0.0)=(1.0, 0.0)
