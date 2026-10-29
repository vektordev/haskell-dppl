-- A random Bool state (a two-state Markov chain, `trans fog`) passed as the
-- LEADING argument of a call whose callee recurses, through two mutually
-- recursive functions (step -> cont -> step). Found by the
-- publication-exploration rare-event probe (runs2.ppl, a run of consecutive
-- misses under Markov-switching fog). It was refused by the set-valued witness
-- engine because enumeration only marginalised a curried call's last
-- argument; since task random-leading-argument-into-recursion-refused the
-- leading argument is enumerated (leadingEnumerableArgument), and the program
-- stops where its swapped spelling (`cont n (trans fog)`) stops: the
-- generate-backed-fallback guard, which admits only a direct self-call that
-- changes an argument, not mutual recursion (ticket
-- neural-read-mutual-recursion-refused covers the same guard).
-- Idealized: p(True) = 0.2 + 0.8 * 0.2 = 0.36.
expect-failure: refused "which is on a recursive call cycle"
p(True)=(0.36, 0.0)
p(False)=(0.64, 0.0)
