-- --marginals reports the mask (ANY, ANY) as Integrate, but main's whole
-- probability function is refused ("no inference engine applies to the
-- binding of 'w'"), so even that query fails. The table also says Bottom for
-- (ANY, _), where the remaining slots are a Gaussian and a coin. Verified at
-- b16b4d9 on dev. Docs task admitted-binding-refused-by-engine-construction.
-- Idealized: p((ANY, (ANY, True))) = 0.5.
expect-failure: broken
p((ANY, (ANY, True)))=(0.5, 0.0)
