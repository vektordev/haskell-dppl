backends: python
expect-failure: broken
p(True)=(0.03988322153843628, 0.0)
p(False)=(0.9601167784615637, 0.0)
-- 24 nested `if`s whose conditions are noisy reads of one enumerated latent
-- `b`. The Python backend emits the whole chain as ONE expression, ~10
-- bracket levels per `if`, and CPython's parser refuses more than 200: the
-- module fails to load with "SyntaxError: too many nested parentheses" (at
-- 18 nested ifs it loads, depth 191; at 20 it does not). Without the shared
-- `draw b` the same chain loads at depth 40. Idealized value:
-- 0.5*0.9^24 + 0.5*0.1^24. Found by experiments_nest
-- exact-eig-question-asking (noisy oracle). Task python-emitted-expression-exceeds-parser-nesting.
