-- The repro of docs task drawn-tuple-mixture-field-read-dangles-at-o0:
-- helperDiscardsComparedMixture with the tuple mixture drawn. The helper's
-- parameter is recovered as a chain-made wildcard (fst discards it), and the
-- operand snd z was measured at that wildcard anyway, which at -O0 read the
-- unbound draw name ("Variable z not declared"). A wildcard witness now
-- reads the operand's marginal, one, without compiling into it (task
-- any-slot-through-injf-inverse-reaches-condition). Interpreter Unoptimized
-- is the -O0 check.
p(0)=(1.0, 0.0)
p(1) is impossible
