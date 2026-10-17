-- A neural Int read queried at a value outside its `of` domain. The direct
-- read indexes the logit vector with the query value unchecked
-- (AutoNeural's makeProbRec / indexOf): in Python p(-1) answers 0.4 (a
-- negative index reads the last logit) and p(4) raises IndexError; with
-- `of [5, 7, 9]` p(4) = p(8) = 0.3. Through point inversion,
-- draw x = readD a in draw y = readD b in (x, x ++ y) gives p((1, 0)) = 0.08
-- and a total mass of 2.51 over a grid. The enumeration path guards with
-- isPossible. Verified at b16b4d9 on dev. Docs task
-- neural-read-query-outside-domain-unchecked.
-- Idealized: impossible.
expect-failure: broken
p(-1, (2, [0.1, 0.2, 0.3, 0.4])) is impossible
p(4, (2, [0.1, 0.2, 0.3, 0.4])) is impossible
