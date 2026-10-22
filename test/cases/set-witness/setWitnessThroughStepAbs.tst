-- distributions/letProbAbsNormal's |Normal| with an identity step (+ 0.0)
-- around the if-mixture. The mixture reads x twice, so the whole body does
-- not transport; the set-witness walk transports the observation through the
-- plus step onto the mixture and then inverts the mixture onto x. Used to be
-- refused ("no inference engine applies"). Task
-- set-witness-walk-stops-at-identity-injf-wrapper.
p(0.7)=(0.6245078667335225, 1.0)
p(-0.3) is impossible
cdf(0.7)=(0.5160726955538539, 0.0)
cdf(-0.3)=(0.0, 0.0)
