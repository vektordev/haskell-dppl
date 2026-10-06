-- A curried lambda spine whose body is a tuple measures every field, not only
-- the one fed by the last-applied argument: the answer is the product of two
-- independent standard-normal densities at dim 2. Formerly a known-issues
-- wrong-result pin (always phi(y) at dim 1, ignoring x).
p((0.0, 0.0))=(0.15915494, 2.0)
p((5.0, 0.0))=(5.9311527e-7, 2.0)
p((-100.0, 0.0))=(0.0, 2.0)
p((0.0, 1.0))=(0.096532353, 2.0)
