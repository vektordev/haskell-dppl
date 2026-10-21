-- A neural read over a non-naturals domain queried between and outside its
-- values: indexOf folds to a select chain whose last arm takes no
-- comparison, so p(4) and p(8) used to answer the last slot (0.3). Docs task
-- neural-read-query-outside-domain-unchecked.
p(4, (2, [0.2, 0.5, 0.3])) is impossible
p(8, (2, [0.2, 0.5, 0.3])) is impossible
p(7, (2, [0.2, 0.5, 0.3])) = (0.5, 0)
p(9, (2, [0.2, 0.5, 0.3])) = (0.3, 0)
