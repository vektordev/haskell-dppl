# Witness inversion engines for non-invertible observations

Two engines in `IRCompiler.hs` handle `let`-bindings whose observation can't
be point-inverted onto the bound variable via ordinary forward chaining.
The probabilistic `Apply` arm tries them in the order below, with
forward-chaining point inversion in between.

## Plan-guided lazy enumeration

`planWitnessApply` is tried *first*, ahead of point inversion, and fires when
the bound value is a neural network's structured output
(`let s = nn sym in <predicates over s>`): since the NN's distribution
factorizes per `PartitionPlan` slot, the observation inverts into worlds
constraining individual plan leaves, measured as products of logit-slice
reads — no `of` clause or support materialization needed.

Point inversion's inverses would otherwise crash on these shapes, which is
why the engine intercepts rather than backstops. Bodies its traversal
declines are untouched: they fall through to point inversion, and only then
to set-valued witnesses. See `testCases/planEnum*` for worked examples
across the milestone levels (inline predicates, recursive user-function
specialization, value-grouped DP for counting folds, and continuous-leaf
constraints).

## Set-valued witnesses

`setWitnessApply` is the last resort: it fires once `toInvExprMaybe` reports
that *no* occurrence of the bound variable is point-invertible, which is what
happens when every path to the binding crosses a comparison or `if`. The
observation then inverts into guarded constraint-set worlds (intervals from
comparisons, measured as CDF differences; case splits from conditionals;
intersections across multiple occurrences) — e.g.

```
let x = Normal in if x < 0.0 then 0.0 - x else x
```

yields the `|Normal|` density `2φ(y)` (`testCases/letProbAbsNormal`). Bodies
drawing fresh randomness alongside such constraints are refused with a
diagnostic.
