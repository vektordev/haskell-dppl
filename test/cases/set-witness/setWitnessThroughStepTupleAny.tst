-- The identity-wrapped |Normal| mixture in a tuple field, queried at a
-- wildcard: the plus step reads ANY, so the mixture's set is unconstrained
-- there. Task set-witness-walk-stops-at-identity-injf-wrapper.
slow
p((0.7, 1.0))=(0.6245078667335225, 1.0)
p((0.7, 0.0)) is impossible
p((ANY, 1.0))=(1.0, 0.0)
p((ANY, 0.0)) is impossible
