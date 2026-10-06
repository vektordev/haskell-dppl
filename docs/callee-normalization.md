# Callee normalization and function-valued mixtures

How a function value in callee position is made visible to inference.

## Callee Normalization

Probability mode compiles `Apply l v` by inverting the observation through
`l`'s body, which presupposes `l` names a lambda the compiler can see:
`ForwardChaining.findEquivalentExpression` has to resolve `l`'s chain name to a
`LambdaInfo`. That holds for a lambda literal and for a bare name (a top-level
function, or a `let`-bound one -- FC's equivalence classes walk through a
variable). It fails for every *other* way a program can produce a function
value, and the failures were not graceful: a lambda projected out of a tuple or
taken from a list hit an internal "should resolve to a lambda" `error`, and one
chosen by an `if` compiled a mixture that multiplied a branch weight by a
closure and died in the interpreter with a type error at run time.

`SPLL.CalleeNormalize` removes the selection rather than teaching each engine to
see through it. Two purely syntactic rewrites, run by `Prelude.compile` on the
freshly parsed program (before RInfer, so every node it builds is annotated by
the rest of the pipeline like any other, needing no re-chain-naming round of its
own):

- **An `if` in callee position is distributed into its arms**:
  `(if c then f else g) v` becomes `if c then f v else g v`. The arms are
  alternatives, so no draw in `v` is duplicated -- only one arm is ever realised
  -- and the result is the ordinary mixture the `IfThenElse` rules already
  compile, over the two applications' *probabilities* rather than over closures.
  This is what makes a probabilistic function value a real capability
  (`test/cases/higher-order/arrowApplyRandomFunction`) instead of a runtime crash.
- **A callee denoting a lambda literal is replaced by it**: `fst`/`snd` of a
  tuple literal, `head`/`tail` of a list literal, and `let`-bound names standing
  for either, reduced until a `Lambda` falls out. Only a reduction that bottoms
  out at a lambda is taken, so nothing else is ever moved.

Three more rewrites came with task `fuzz-admission-oracle-bugs`, all found by
the admission oracle:

- **A redex in callee position has the application pushed into its body**:
  `((\x -> b) a) v` becomes `(\x -> b v) a` (binder renamed on capture), and
  likewise a projection chain of a redex or of an `if`: `fst ((\x -> (f, ..))
  a) v` becomes `(\x -> fst (f, ..) v) a`. A `draw` stays where it is. Left
  alone, FC met a callee that is neither a lambda nor a name, and IRCompiler
  compiled the returned lambda's body outside the scope binding its free
  variables (`curriedLambdaUnusedRandomArg`, `arrowApplyRedexCallee*`).
- **An `if` arm projecting a lambda literal out of a literal constructor is
  that lambda**, so the pointwise-lifted arrow mixture sees lambda arms
  (`arrowApplyIfSelectedProjected`).
- **A bare name standing for a lambda only through a projection** (`draw f =
  snd (Normal, \x -> Uniform) in f c`) is substituted at the call: FC cannot
  see through `snd` of a tuple with a random sibling. The binding is then
  dead, and a dead function-valued binding is compiled as its body
  (`arrowApplyTupleProjectedRandomSibling`).

One more, from task `symbol-chosen-by-inline-coin-refused`:

- **A neural read of a selected input is distributed the same way**:
  `see (if c then a else b)` becomes `if c then see a else see b`, and a read
  of a redex is pushed into its body, so `see (draw s = .. in if s then a else
  b)` reaches the arms too. A read names no variable, so nothing is captured.
  Left alone, the read's input is not a point, and ModalityInfer's `ReadNN`
  rule must type a read of a non-point input sample-only, since a continuous
  input would make it a mixture with no closed form. In the arms, each read
  gets the point input it really receives, and the selection is the ordinary
  `IfThenElse` mixture. This covers both the inline coin and the `draw`-bound
  one, which had silently lost its probability variant when that rule was
  introduced (`test/cases/neural/symbolChosen*`). A read whose input is
  random in any other way (`see h` for a drawn `h`, a continuous input) is
  untouched and stays sample-only.

Whatever the pass does not reach is refused by IRCompiler's point-inversion
`Apply` arm ("does not resolve to a lambda the compiler can see"), an absent
variant rather than the `error` it used to be.

The one selection it deliberately leaves alone is a **bare name** in callee
position (other than the projected one above), precisely because that is the
one FC already resolves. An earlier
draft substituted those too and moved two working programs onto a different
path: `hoProbValueLambda` (`(\x -> x 1.0) (\y -> Uniform + y)`) became a dead
binding whose arrow-typed probabilistic argument arm generates rather than
infers, tripping the central generate-backed-body guard, and `twiceApplication`
stopped being refused by batched mode. It also would not terminate on a
recursive function. Descending under a binder drops every environment entry
whose value mentions that name, so a lambda is never moved into a scope where
one of its free variables means something else.

Corpus: `arrowApply*` (the probe table of investigation
`modality-function-space-test-coverage`, rows 1-8). Row 7,
`(\x -> x + x) Normal`, was a refusal -- the set-witness engine cannot
propagate an observation onto a variable occurring on both sides of its own
sum -- until affine Gaussian marginalisation (`witness-inversion-engines.md`) answered it without a
witness: `arrowApplySelfSum`, `N(0, 2)`.

A second, independent half of the same task: the `PNormal`/`PLogNormal`
catch-alls in `IRCompiler` now also decline a **local `Var`** and an
**`IfThenElse`**, neither of which `toIRNormalParams` has any `(mu, sigma)` to
read off, so the catch-all could only ever reach its fallthrough `error`.
A local `Var` is reached by a nested `let` (`let x = Normal in let y = x + 1.0
in y`: the body-factor fold retypes `x + 1.0` Deterministic but leaves `y`
labelled `PNormal`), and `hasOwnInferenceHandler` now asks the type environment
the same `Just (_, False)` question the `Var` equation itself dispatches on. An
`IfThenElse` is a mixture -- of two Gaussians it is not a Gaussian -- and its
own equation measures the arms and mixes them, which is right whether the
condition is deterministic (`ifSelectNormalDet`, which `TestModalityInfer`
already typed `PNormal` while the pipeline crashed on it) or probabilistic
(`ifSelectNormalMixture`, an even mixture of `N(1,1)` and `N(0,2)` that now
answers exactly). `isNormalExtractable`, the mirror predicate gating whether a
top-level function gets a `normalFun` at all, excludes `IfThenElse` for the same
reason. Corpus: `letChainNormalVar`, `letChainNormalVarTuple`,
`ifSelectNormalDet`, `ifSelectNormalMixture`.

## An arrow-typed `if`-mixture is lifted pointwise, not multiplied

`CalleeNormalize`'s `if`-distribution rule only reaches a selection *syntactically
in callee position*; a probabilistic function value reached any other way --
notably `let f = if Uniform < 0.5 then g else h in f v`, where `f` is a bare
name applied elsewhere -- still compiled a mixture that multiplied a branch
weight by a `VClosure` (`Mult can only multiply numbers ...: VClosure`), since
`toIRInference`'s `IfThenElse` equation treated each arm's `rProb` (itself a
closure, `detP (IRLambda ...)`, for an arrow-typed arm) as a scalar to
`prodP`/`mixP`.

Before that arithmetic is ever reached, `ForwardChaining.constructEquivalenceClauses`
builds a certificate for *every* `Apply` node unconditionally, and its `TArrow`
branch (the per-invocation tagging machinery for a function-valued binding)
assumed the bound value always resolves to exactly one lambda body via
`getEquivCN` -- an if-selected mixture has no such single body, so this crashed
first, one layer earlier than the arithmetic bug ("Found no equivalent chain
name to: ..."). `getEquivCNMaybe` makes that lookup recoverable; when it fails,
the branch degrades to just the Apply-is-equivalent-to-its-body clause (no
tagging) rather than erroring -- sound because nothing on the mixture's own
compilation path below ever consults that tagging for this shape.

`toIRInference`'s `IfThenElse` equation now dispatches on the arms' `rType`: for
`TArrow`, it builds a **new closure** over a fresh argument, whose body opens
each arm's own closure at that argument (`unpackResult (IRApply armClosure z)`,
let-bound once each to avoid `unpackResult`'s four-way destructuring
duplicating a possibly-expensive call) and runs the *ordinary* scalar
`weighByCond`/`mixP` combinators on the opened, scalar results --
`mix(p_c, t, g) == \z -> mix(p_c, unpack(t z), unpack(g z))`. `shareResult`'s
existing dead-arm guard carries over unchanged, so an arm whose condition
cannot hold is still never evaluated. topK pruning is not implemented on this
path (it always computes the exact, unpruned mixture -- a valid refinement of
what pruning would have approximated, never a regression from the pre-fix
crash) and the scalar path is untouched. Corpus:
`arrowApplyLetBoundRandomFunction`.

Two closely related shapes are deliberately **not** covered yet and are filed
separately, since they turned out to be blocked by different bugs, not by this
mechanism: a curried multi-argument selection in callee position (blocked by
`CalleeNormalize`'s own curried-spine gap) and a *named function's* call
resolving to an if-selected lambda, even with no randomness involved (a
different `ForwardChaining` crash, in the `l`-side resolution of the same
`constructEquivalenceClauses` function). See task
`arrow-lifted-mixture-for-function-values` and its `depends_on`.
