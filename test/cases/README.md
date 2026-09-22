# Test Cases

This folder contains the test cases for the automatic End-to-End testing framework.

Every test case consists of a program specified in a ".ppl" file and a set of assertions specified in a ".tst" file.

## Folder layout

Pairs are grouped into subfolders by language feature (`distributions/`,
`data-structures/`, `set-witness/`, `neural/`, ...) rather than flat, so
finding "the tests for X" doesn't mean grepping several hundred files. A
`.ppl`/`.tst` pair always lives together in the same folder; the test runner
(`End2EndTesting.getAllTestFiles`, `TestModalityInfer`'s corpus-wide sweep)
discovers them by recursing into every folder here, so a base name is unique
across the whole corpus and findable regardless of which folder it is in
(`TestCaseParser.corpusPplPath`/`corpusTstPath`). Which folder a new pair goes
into is a judgment call -- put it next to the pair it's most similar to.

`known-issues/` is a sibling of the topic folders, not one of them, and is
**excluded** from the recursive discovery above: every program there is
*expected* to fail to compile, pinning a specific, still-open compiler bug
rather than testing a working feature. See the next section.

## Pinning a known bug (`known-issues/`)

Filing a mechanical repro for a bug that must *keep failing* until it's fixed
doesn't need a hand-written Haskell test group -- drop a `.ppl`/`.tst` pair
into `known-issues/` whose `.tst` carries an `expect-failure:` header (in the
same style as `backends:`/`slow`) naming one of five shapes:

```
expect-failure: crash                              -- an uncaught exception, message unpinned
expect-failure: diagnostic "some substring"        -- an uncaught exception whose message contains this
expect-failure: no-code                            -- compiles, but generate/probability/integrate is silently absent
expect-failure: wrong-result                       -- compiles and runs; the p()/cdf() rows below pin the known-wrong value
expect-failure: broken                             -- mechanism unpinned; the p()/cdf() rows below state the idealized value instead
```

`crash`/`diagnostic` are checked against an *uncaught exception* thrown while
forcing `compile`'s result -- a graceful `Left` (an intended, working refusal)
does not count; that's what `TestRejection` is for. `wrong-result` needs no
special assertion machinery: the ordinary `p(...)`/`cdf(...)` rows below the
header already pin the value the bug produces, and the corpus's usual tuple
comparison already fails loudly the day a fix changes the computed number.

`broken` is the loose fallback for a repro nobody has characterized yet -- no
exact crash message, no wrong value pinned by hand. The rows below the header
state the *idealized* value instead (what a fixed compiler should produce), and
`TestKnownIssues.hs` asserts the compiled program does **not yet** match it: a
crash, a refused compile, a missing variant or a merely different number all
count as "still broken" and pass, while an exact match fails loudly ("may be
fixed now"). It trades the "which exact mechanism regressed" signal that
`diagnostic`/`wrong-result` give for robustness against unrelated churn
shifting a pinned message or number.

**Prefer `broken` over not filing at all.** If you have a program that
misbehaves but you have not worked out precisely how, `broken` is the header
for it -- writing down the idealized value is enough. A repro that exists is
worth far more than a precisely-characterized one that never got committed.

`TestKnownIssues.hs` discovers every pair here and checks it against its
header. This coexists with `TestRejection.hs` rather than replacing it: a
genuinely bespoke, multi-assertion regression (e.g. one that also checks a
*different*, unaffected code path) stays a hand-written HUnit group there.
This mechanism is for the common single-diagnostic shape only.

## What is tested
The automatic End-to-End testing framework tests that every program provided compiles correctly and produces a value in the generative direction. We test that for given sample values in the TST file, the value of the PDF matches the provided expected value. All of these steps are done with the built-in interpreter and a version of the program compiled into Python as well as Julia.

Further tests are employed for programs that declare neural networks. The Interpreter is capable of mimicking the functionality of neural networks. These Mock-Neural Networks have two modes: an NN outputting completely random results or a NN producing a probability spike at a given value.

For all programs declaring an NN, we generate a large number of outputs and test whether the resulting PDF is normalized. Furthermore, we can take custom tests for neural programs, which test whether the output of a program is what we would expect given a well-trained NN.

## Creating a test case
Create two files with the same name, except for the file extension. One with the ".ppl" file extension and one with ".tst". The ".ppl" contains a program that will be executed for every assertion specified in the ".tst" file.

### Syntax for the PPL file
Create a file with normal DPPL Syntax, containing a function called "main". The main may have additional parameters, which have to be specified in the TST file. This will be the function on which probabilistic inference is performed.

### Syntax of the TST file
The TST file consists of any number of assertions for the probabilistic inference of a PPL file. There are multiple types of assertions, but all of them must be in exactly one line.

Test cases, regardless of type, take Values as inputs. Make sure that the values you pass only use Value syntax and not expression syntax. E.g., Either types can be created using the uppercase "Left" or lowercase "left" syntax in expressions. The first is Value syntax, while the latter is expression syntax and invokes the "left" constructor. In this case, only the uppercase version may be used.

ADT values are written by juxtaposing a constructor with its fields, exactly as in the value grammar: `p(Leaf)`, `p(Node Leaf Leaf)`, `p(Node (Node Leaf Leaf) 0.5)`. A field that is itself a constructor application needs parentheses. The marginal wildcard `ANY` may stand in for any field, at any depth: `p(Node ANY Leaf)`, `p(Link ANY (Link ANY Nil))`.

Prefer querying an ADT-valued program at an ADT point over querying a `Float`/`Bool` projection of it. A projection only ever exercises the accessors of the constructor it reads, so it never reaches a sibling constructor's field accessors -- which is how a missing guard on those accessors survived the whole corpus once already.

`cdf(...)` is not available for an ADT-valued program: an ADT is an unordered sum, so there is no order for a cumulative distribution to integrate along. Such a query is refused with a diagnostic (pinned by the `Rejection.AdtCumulative` test group), not answered.

#### PDF/CDF assertions
These are the most basic types of assertions. They test that the PDF or CDF has an expected value at a given position. The following snippet shows one PDF and one CDF assertion:

```
p(1.5)=(0.5, 1.0)
cdf(1.5)=(0.75, 0.0)
```

The assertions test that the probability density of the main function is 0.5 at the position x=1.5 and has a dimensionality of 1 (density). The cumulative density at position x=1.5 has to be 0.75 with a dimensionality of 0 (mass).

If the main function has parameters, list them, comma-separated, after the sample point, like this:

```
p(1.5, False, [0.2])=(0.5, 1.0)
cdf(1.5, False, [0.2])=(0.75, 0.0)
```
False and [0.2] would be passed as parameters to the main function in both cases.

#### Argmax_p assertions
Especially when dealing with neural networks, testing for exact probability densities becomes infeasible. The argmax_p assertion allows to specify which output should be the most likely. This is done using a MockNN in the interpreter that behaves like a well-trained NN.

The argmax_p assertion works on programs that take a symbol as an input. For this type of testing, we pass a value as a symbol to the MockNN, and it behaves as if it recognized the value it was given. The test syntax looks like this:
```
argmax_p(3)=3
```
The key difference to PDF/CDF testing is that we don't specify a test point. All arguments of the argmax_p assertion are directly passed to the main function. Any neural network that takes a symbol as input behaves as if it recognized the value in its symbol input.

For example, an MNist addition program, that would normally take two images as symbol inputs, could be tested using: ```argmax_p(3, 7)=10``` to test that for an image showing a 3 and an image showing a 7, 10 would be the most likely outcome of the program.

Neural networks that output an ADT can be tested by creating a list with the head being the index of the constructor and each further element representing a field. This encoding predates the parser's ADT support and is still what the `argmax_p` path expects; PDF/CDF query points use the constructor syntax above.
