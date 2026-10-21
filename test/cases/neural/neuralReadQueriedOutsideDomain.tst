-- A neural Int read queried at a value outside its `of` domain is
-- impossible. AutoNeural's makeProbRec guards the logit read with a
-- membership test; before that, indexOf indexed the logit vector unchecked:
-- Python answered p(-1) = 0.4 (a negative index reads the last logit) and
-- raised IndexError on p(4), the interpreter crashed with "Index out of
-- bounds". Docs task neural-read-query-outside-domain-unchecked.
p(-1, (2, [0.1, 0.2, 0.3, 0.4])) is impossible
p(4, (2, [0.1, 0.2, 0.3, 0.4])) is impossible
p(0, (2, [0.1, 0.2, 0.3, 0.4])) = (0.1, 0)
p(3, (2, [0.1, 0.2, 0.3, 0.4])) = (0.4, 0)
