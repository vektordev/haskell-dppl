-- A constant that folds to NaN (0/0 here; 0 * 1e400 and 1e400 - 1e400 do
-- the same) hangs the compiler before the first stage dump:
-- Analysis.annotateEnumsProg iterates Utils.fixpoint, whose (==) test never
-- holds for a DiscreteValues tag containing VFloat NaN, since NaN /= NaN.
-- Found probing the boundary-value fuzz leaves. Docs task
-- nan-constant-hangs-enum-annotation-fixpoint.
expect-failure: hang
cap: 2 s, 500 MB
