-- set-witness/setWitnessSiblingConst with the then-arm's first field
-- spelled x + 0.0. Masking that field (ANY) recovers x through plus's inverse
-- as the ANY value itself, which the condition then compares at run time:
-- "Type error: less than can only compare two numbers ... (VAny, VFloat
-- 0.5)". The unwrapped program answers (0.5, dim 0). Verified at 3b72682 on
-- dev, interpreter. Found by the rewrite-invariance net's injf-identity
-- family. Docs task any-slot-through-injf-inverse-reaches-condition.
backends: interpreter
expect-failure: broken
p((ANY, 1.0))=(0.5, 0.0)
