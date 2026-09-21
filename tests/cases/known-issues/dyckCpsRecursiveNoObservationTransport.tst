-- A mutually-recursive continuation-passing-style generator for
-- balanced-parenthesis (Dyck) strings has no way for an observation to
-- transport through the recursive call -- the framework has no
-- density-passing-style machinery yet. This is a genuine open design gap,
-- not a mechanical bugfix: the doc's own directive is that this program
-- should keep failing loudly (no idealized value is claimed), even once the
-- G0/G1/G2 gaps in this same doc are fixed.
expect-failure: diagnostic "set-valued witness construction failed"
