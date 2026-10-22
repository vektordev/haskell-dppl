p([((4, 2.5), [1])])=(1.0, 0.0)
p([(ANY, [1])])=(1.0, 0.0)
p([((ANY, 2.5), [1])])=(1.0, 0.0)
p([((4, ANY), [1])])=(1.0, 0.0)
p([((4, 2.5), [ANY])])=(1.0, 0.0)
p([((3, 2.5), [1])])=(0.0, 0.0)
p([((3, ANY), [1])])=(0.0, 0.0)
p([((ANY, 2.5), [2])])=(0.0, 0.0)
-- A list query is answered by an OpEq of the query against the literal. The
-- interpreter's OpEq used to compare tuple *fields* with Haskell's structural
-- (==), so an ANY nested inside a tuple field (an inner tuple slot, or a list
-- element inside a tuple) answered impossible while Python and Julia answered
-- 1.0 (docs task interpreter-eq-nested-tuple-ignores-any). Found by
-- prop_Fuzz_BackendsAgree; the two original findings are
-- nestedTupleAnyUnderHeadOfIf and nestedTupleAnyUnderSndHead.
