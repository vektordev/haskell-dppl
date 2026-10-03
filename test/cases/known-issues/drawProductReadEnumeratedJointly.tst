expect-failure: diagnostic "set-valued witness construction failed for the binding of 'truth'"
p(Face True False ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY, (0, [0.8, 0.2, 0.3, 0.7, 0.6, 0.4, 0.1, 0.9, 0.5, 0.5, 0.9, 0.1, 0.2, 0.8, 0.7, 0.3, 0.4, 0.6, 0.55, 0.45, 0.35, 0.65, 0.65, 0.35, 0.15, 0.85, 0.85, 0.15]))=(0.4484, 0.0)
p(Face False False False ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY, (0, [0.8, 0.2, 0.3, 0.7, 0.6, 0.4, 0.1, 0.9, 0.5, 0.5, 0.9, 0.1, 0.2, 0.8, 0.7, 0.3, 0.4, 0.6, 0.55, 0.45, 0.35, 0.65, 0.65, 0.35, 0.15, 0.85, 0.85, 0.15]))=(0.05380799999999995, 0.0)
p(Face ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY ANY, (0, [0.8, 0.2, 0.3, 0.7, 0.6, 0.4, 0.1, 0.9, 0.5, 0.5, 0.9, 0.1, 0.2, 0.8, 0.7, 0.3, 0.4, 0.6, 0.55, 0.45, 0.35, 0.65, 0.65, 0.35, 0.15, 0.85, 0.85, 0.15]))=(1.0, 0.0)
-- Idealized: P(heard_j = yes) = q_j*0.9 + (1-q_j)*0.2 per field, independent
-- across fields, ANY fields contributing 1. Found by experiments_nest
-- exact-eig-question-asking (CelebA Guess-Who model). Fixing the plan engine's
-- coverage of `Uniform < parameter` would also flip this pin without fixing
-- the joint enumeration; the task's acceptance is the per-field cost, not
-- this pin alone. Task draw-product-read-enumerated-jointly.
