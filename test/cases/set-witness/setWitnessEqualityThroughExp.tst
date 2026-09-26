-- A continuous `==` whose bound-variable operand passes through an InjF with
-- an applicability guard (exp's inverse guards b > 0). The False outcome used
-- to be transported as a point -- the VAnyExcept sentinel -- through log and
-- its guard, crashing optimizer and interpreter alike (task
-- set-witness-exp-equality-guard-vanyexcept-crash). It is now the complement
-- of the True outcome's witness on x itself: exp x == 1.0 iff x == 0.0, a
-- null event, so main is 0.0 almost surely. The True arm's density
-- convention (p(1.0)) is task sampling-matches-pdf-continuous-equality-density
-- and deliberately not pinned here.
p(0.0)=(1.0, 0.0, False)
p(2.0) is impossible
