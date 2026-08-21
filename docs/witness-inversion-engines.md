# Witness inversion engines for non-invertible observations

Two engines in `IRCompiler.hs` handle `let`-bindings whose observation can't
be point-inverted onto the bound variable via ordinary forward chaining.

## Set-valued witnesses

`setWitnessApply` fires when every path to the binding crosses a comparison
or `if`: the observation inverts into guarded constraint-set worlds
(intervals from comparisons, measured as CDF differences; case splits from
conditionals; intersections across multiple occurrences) — e.g.

```
let x = Normal in if x < 0.0 then 0.0 - x else x
```

yields the `|Normal|` density `2φ(y)`. Bodies drawing fresh randomness
alongside such constraints are refused with a diagnostic.

## Plan-guided lazy enumeration

`planWitnessApply` fires instead when the bound value is a neural network's
structured output (`let s = nn sym in <predicates over s>`): since the NN's
distribution factorizes per `PartitionPlan` slot, the observation inverts
into worlds constraining individual plan leaves, measured as products of
logit-slice reads — no `of` clause or support materialization needed.

This engine is tried before forward-chaining point inversion, whose
inverses would otherwise crash on these shapes. See `testCases/planEnum*`
for worked examples across the milestone levels (inline predicates,
recursive user-function specialization, value-grouped DP for counting
folds, and continuous-leaf constraints).
