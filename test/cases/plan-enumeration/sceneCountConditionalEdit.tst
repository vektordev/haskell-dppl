-- "If at least two objects are metal, make every metal object rubber" over a
-- 4-slot product read (task scene-count-conditional-edit-exponential). The
-- default compile enumerates the 625 scenes densely; PlanEngineMatchesDense
-- checks the plan engine (budget 0), where each branch's per-slot
-- observation is absorbed into that slot's summand of the count. Logits per
-- object: [Nil, Obj, Rubber, Metal, Small, Large]. Values from brute-force
-- enumeration of the 625 scenes in Python. no-normalization: the output
-- support is several hundred scenes, more than the sampler's draws cover.
no-normalization
p(Scene (Obj Rubber Small) (Obj Rubber Large) (Obj Rubber Small) (Obj Rubber Large), (2, [0.3, 0.7, 0.4, 0.6, 0.5, 0.5, 0.1, 0.9, 0.2, 0.8, 0.7, 0.3, 0.5, 0.5, 0.9, 0.1, 0.4, 0.6, 0.2, 0.8, 0.35, 0.65, 0.25, 0.75]))=(0.0092058120, 0.0)
p(Scene (Obj Rubber Small) Nil (Obj Rubber Small) (Obj Rubber Large), (2, [0.3, 0.7, 0.4, 0.6, 0.5, 0.5, 0.1, 0.9, 0.2, 0.8, 0.7, 0.3, 0.5, 0.5, 0.9, 0.1, 0.4, 0.6, 0.2, 0.8, 0.35, 0.65, 0.25, 0.75]))=(0.0023646000, 0.0)
p(Scene (Obj Metal Small) Nil (Obj Rubber Small) Nil, (2, [0.3, 0.7, 0.4, 0.6, 0.5, 0.5, 0.1, 0.9, 0.2, 0.8, 0.7, 0.3, 0.5, 0.5, 0.9, 0.1, 0.4, 0.6, 0.2, 0.8, 0.35, 0.65, 0.25, 0.75]))=(0.0007560000, 0.0)
p(Scene (Obj Metal Small) (Obj Metal Large) Nil Nil, (2, [0.3, 0.7, 0.4, 0.6, 0.5, 0.5, 0.1, 0.9, 0.2, 0.8, 0.7, 0.3, 0.5, 0.5, 0.9, 0.1, 0.4, 0.6, 0.2, 0.8, 0.35, 0.65, 0.25, 0.75]))=(0.0, 0.0)
p(Scene Nil Nil Nil Nil, (2, [0.3, 0.7, 0.4, 0.6, 0.5, 0.5, 0.1, 0.9, 0.2, 0.8, 0.7, 0.3, 0.5, 0.5, 0.9, 0.1, 0.4, 0.6, 0.2, 0.8, 0.35, 0.65, 0.25, 0.75]))=(0.003, 0.0)
p(Scene Nil (Obj Rubber Large) (Obj Metal Small) (Obj Rubber Large), (2, [0.3, 0.7, 0.4, 0.6, 0.5, 0.5, 0.1, 0.9, 0.2, 0.8, 0.7, 0.3, 0.5, 0.5, 0.9, 0.1, 0.4, 0.6, 0.2, 0.8, 0.35, 0.65, 0.25, 0.75]))=(0.0000680400, 0.0)
