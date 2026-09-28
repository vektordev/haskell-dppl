-- Task let-alias-of-random-binding-crashes-toirnormalparams. Verified at
-- f4ea495 on dev: `p1` is a pure alias of `s1`, and the aliased value also
-- feeds further randomness (`p1 + s2`), so toIRNormalParams is handed a bare
-- `Var "p1"` typed PNormal and calls `error` with an AST dump. Writing `s1`
-- for `p1` compiles and is right (`draw s1 = Normal in draw s2 = s1 + Normal
-- in (s1, s1 + s2)`). Found by experiments_nest
-- linear-dynamics-trajectory-mle (exp-continuous-hybrid-simulation-retest).
-- Idealized: s1 = 0.5, s2 = 0.6, s2 - s1 = 0.1, so
--   p((0.5, 1.1)) = phi(0.5) * phi(0.1) = (0.13975322833741527, 2.0)
expect-failure: diagnostic "cannot extract Normal params"
