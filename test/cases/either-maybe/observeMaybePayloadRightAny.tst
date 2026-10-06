-- A Maybe whose Just payload is itself the draw-bound Maybe m (the shape
-- `observe (observe Normal (> 0)) isRight` desugars to). p(Right ANY) is
-- P(v > 0) = 0.5: `isRight m` witnesses m = Right ANY and `right m` at
-- Right ANY a bare ANY, and the set-witness point-point merge keeps the former
-- (task maybe-payload-right-any-marginal-zero, fixed by
-- materialization-budget-zero-observe-any-wrong; it used to answer 0, the bare
-- ANY failing the two witnesses' equality guard). Point queries were always
-- right. The discrete-payload twin (`right 1.0` instead of `right v`) is
-- known-issues/fuzzUnionMultiValuesOppositeEither.
p(Right Right 0.5)=(0.35206533, 1.0)
p(Left ())=(0.5, 0.0)
p(Right ANY)=(0.5, 0.0)
p(ANY)=(1.0, 0.0)
