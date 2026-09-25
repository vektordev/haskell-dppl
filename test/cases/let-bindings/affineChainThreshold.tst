p(1)=(0.06481599459794407, 0.0)
p(0)=(0.9351840054020559, 0.0)
-- Gate G0.2's probe1_unrolled_symbolic (experiments_nest gate0-feasibility):
-- a threshold on the *endpoint* of an ungated chain, not a chain gated on its
-- own state (that is continuous-recursive-gate-witness-failure's shape, and
-- stays Bottom). s3 ~ N(0.81, 0.5*sqrt(1 + 0.81 + 0.6561)), so
-- P(s3 > 2) = 1 - Phi((2 - 0.81)/0.785...); agrees with the inlined
-- probe4_letfree_threestep oracle recorded on that task.
