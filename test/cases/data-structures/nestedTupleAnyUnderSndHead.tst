p((False, (True, False)))=(1.0, 0.0)
p((ANY, (True, False)))=(1.0, 0.0)
p((False, ANY))=(1.0, 0.0)
p((False, (True, ANY)))=(1.0, 0.0)
p((ANY, (False, False)))=(0.0, 0.0)
-- Fuzz finding (prop_Fuzz_BackendsAgree, docs task
-- interpreter-eq-nested-tuple-ignores-any): inverting snd then head turns the
-- query into ListCont (ANY, q) AnyList, so a tuple field holding a nested ANY
-- reached the interpreter's OpEq tuple case and answered impossible.
