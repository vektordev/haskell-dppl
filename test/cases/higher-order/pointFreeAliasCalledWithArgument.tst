-- Calling a point-free alias of a top-level function with an argument. Forward
-- chaining used to crash on it ("expected chain name ... to be a Lambda") because
-- the alias's arrow-typed body is the Var `coin`, not a lambda; it now resolves the
-- alias to coin's lambda (ForwardChaining.resolveTopLevelLambda). Docs task
-- point-free-alias-called-with-argument-crashes-forward-chaining.
p(True, 0.3)=(0.3, 0.0)
p(False, 0.3)=(0.7, 0.0)
