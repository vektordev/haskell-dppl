p(((-4, -8.479733117671657), Stop))=(1.0, 0.0)
p(((ANY, -8.479733117671657), Stop))=(1.0, 0.0)
p(((-4, ANY), Stop))=(1.0, 0.0)
p(((-4, -8.479733117671657), ANY))=(1.0, 0.0)
p(((2, ANY), Stop))=(0.0, 0.0)
-- Fuzz finding (prop_Fuzz_BackendsAgree seed 426637/800596, docs task
-- interpreter-eq-nested-tuple-ignores-any): inverting head over a list-valued
-- if compares ListCont q AnyList against each arm, so an ANY inside the inner
-- tuple reached the interpreter's OpEq tuple case, which compared fields with
-- structural (==) and answered impossible. The direct-field ANY row was right.
