-- namedFunctionTwoRandomArgs with each parameter re-bound through a
-- beta-redex inside the curried helper: it answers what `f x y = (x, y)`
-- answers. Refused set-valued witness construction for the binding of the
-- leading parameter until named-callee-binding-not-floored (814c061), whose
-- per-invocation copy of a callee's body follows the bindings inside it
-- (docs task alias-of-curried-helper-parameter-refuses-with-random-arguments).
p((0.0, 0.0))=(0.15915494, 2.0, False)
p((0.5, -1.0))=(0.08518950, 2.0, False)
