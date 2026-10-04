-- Verified at commit 592e4b2 on dev: a helper that forwards its (random)
-- parameter to another helper has no probability path, and the refusal is
-- eager, so `generate` is lost too. Inlining either helper compiles.
-- Found while writing polyNestedTwoTypes (design polymorphic-monomorphization);
-- reproduces with no polymorphism involved. Idealized: Uniform + 3.0,
--   p(3.5) = (1.0, 1.0)
expect-failure: refused "tagged invocation"
