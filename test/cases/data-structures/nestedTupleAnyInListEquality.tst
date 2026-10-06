backends: interpreter
expect-failure: broken
p([((ANY, 2.5), [1])])=(1.0, 0.0, False)
p([((4, ANY), [1])])=(1.0, 0.0, False)
p([((4, 2.5), [ANY])])=(1.0, 0.0, False)
-- Verified at commit 1860933 on dev (task interpreter-eq-nested-tuple-ignores-any).
-- A query against a structured literal is answered by an OpEq of the query
-- against the literal. The interpreter's OpEq compares tuple *fields* with
-- Haskell's structural (==) instead of recursing through its own ANY-aware
-- comparison, so an ANY nested one level inside a tuple field (an inner tuple
-- slot, or a list element inside a tuple) is compared as VAny == VInt 4 and
-- answers impossible. Python and Julia recurse ANY-aware and answer 1.0.
-- Found by prop_Fuzz_BackendsAgree via
--   main = head (if True then [((-4, -8.48), Stop)] else [((if Uniform < 0.5 then 2 else 1, -6.92), Stop)])
-- at ((ANY, -8.48), Stop). Point query p([((4, 2.5), [1])]) = (1.0, 0.0) is right.
-- Idealized: every row above is (1.0, 0.0); the interpreter answers "is impossible".
