-- | The compiler's configuration: the knobs the frontend, the IR compiler and
-- the backends read. The IR optimizer sees only 'SPLL.IROptimizer.OptimizerConfig',
-- projected from this by "SPLL.OptimizerProjection" (task
-- ir-package-boundary-b6-optimizer-config); this module imports nothing from
-- the IR, so the interpreter's closure stays free of the optimizer.
module SPLL.CompilerConfig (
  CompilerConfig(..)
, SemiringFamily(..)
, defaultCompilerConfig
, defaultMaterializationCardinality
, defaultMarginalSlots
) where

data CompilerConfig = CompilerConfig {
  -- If set to Just x: All branches with likelihood less than x are discarded.
  --  Uses local probability of the branch,given that the execution arrives at that branching point
  topKThreshold :: Maybe Double,
  countBranches :: Bool,
  -- The per-function budget on ENUMERATED observation slots (design
  -- witnessed-per-query-capability; CLI --marginalSlots, default 4). A function
  -- with k enumerated slots has 2^k masks over them, so the budget is what keeps
  -- per-mask work bounded; over budget, the function gets no mask table and is
  -- reported as over budget rather than analysed. Sits next to
  -- materializationCardinality because it is the same kind of object: a
  -- decidable cost ceiling the user may raise, not a correctness gate.
  marginalSlots :: Int,
  verbose :: Int,
  optimizerLevel :: Int,
  pruneAnyChecks :: Bool,
  noIntegrate :: Bool,
  noProbability :: Bool,
  noGenerate :: Bool,
  -- When True, print every intermediate AST state during compilation (with full TypeInfo/tags)
  showIntermediates :: Bool,
  -- When True (default), the prob/integ function root is wrapped in a guard that
  -- checks the query value structurally conforms to the program's return type,
  -- failing with a clear diagnostic on a mismatch. Independent of optimizerLevel.
  -- Disable (CLI --noTypeCheck) to shave the entry check off hot compiled code.
  checkQueryType :: Bool,
  -- When True (CLI --batched), opt into batched inference mode (design
  -- pytorch-tensorizer). M1 wires only the backend-agnostic select pass, which
  -- retags data-dependent elementwise ifs to SelectIf; scalar lowering is
  -- unchanged, so today this is a behavioural no-op over the tensor fragment.
  batched :: Bool,
  -- When True (CLI --logSpace), compute probabilities in log space rather
  -- than linear space (task log-space-probability-computation, design
  -- materialized-marginals-semiring Decision beta): 'IRCompiler's PResult
  -- combinators (density/mass/prodP/mixP/enumSumP/guardP/scaleCoV/
  -- compareValueExpr) build and combine log-probabilities instead of linear
  -- ones (times becomes IROp OpPlus, mixture-sum becomes log-sum-exp, the
  -- multiplicative unit 1.0 becomes the additive unit 0.0, the zero
  -- probability becomes negative infinity), and the two builtin continuous
  -- distributions emit native log-pdf/log-cdf IR leaves ('IRDensity'/
  -- 'IRCumulative' with their 'LogSpace' field set to 'Log') rather than
  -- logging an already-computed linear value,
  -- so a deep tail never underflows to a hard float zero before its log is
  -- taken. Motivation: deep conjunctions and long enumerations of small
  -- probabilities underflow in linear space long before they are numerically
  -- meaningless. Scope (see the task's written invasiveness verdict): the
  -- core PResult combinators, the Uniform/Normal leaves, discrete
  -- value-equality masses ('compareValueExpr'), and enumerable-InjF sums
  -- ('enumSumP') are log-aware; 'ReadNN'/'AutoNeural' neural read-logits logit
  -- reads, the set-witness/plan-enum continuous measurement machinery, and
  -- batched mode are NOT -- they remain linear-only, so a program reaching
  -- those paths under 'logSpace' will not get the numerical-stability
  -- benefit there (and, for set-witness/plan-enum specifically, may combine
  -- a linear leaf with a log-space combinator and produce a wrong answer;
  -- no compile-time refusal guards this yet). Independent of 'batched'.
  logSpace :: Bool,
  -- When True (CLI --optStats), report optimizer telemetry on stderr: how many
  -- fixed-point iterations 'SPLL.IROptimizer.postProcess' needed per emitted
  -- function, and -- at @verbose >= 1@ -- which rewrite rule fired how many
  -- times in each of those iterations. Diagnostic only; it does not change what
  -- is compiled. Off by default so an ordinary compile stays quiet.
  optStats :: Bool,
  -- | Cardinality budget for marginal materialization (task
  -- materialization-cardinality-guard, design materialized-marginals-semiring
  -- Tier 0): the largest finite 'DiscreteValues' domain whose marginal the
  -- compiler is allowed to tabulate up front, and -- the SAME question, not a
  -- second one -- the largest operand grid it is allowed to unroll into
  -- let-bound cells, since a materialized table IS an unrolling of let-bound
  -- scalar cells rather than a runtime array (see 'SPLL.Analysis's
  -- 'materializationDomain' and IRCompiler's 'materializeOperandTable'). A
  -- domain above this falls back to today's point-query re-descent; set to 0
  -- to disable materialization entirely. Per-node, deliberately NOT a
  -- cumulative budget across nesting levels: budgeting the join is a
  -- non-compositional mechanism that is harder to reason about and to debug,
  -- and each level's unrolling is independently affordable or not. 10000 is a
  -- magic number chosen to sit far above every realistic enumerable domain
  -- (a 10-term MNIST-digit sum tops out at 91 cells and a 910-pair grid) and
  -- far below anything whose unrolling would be a compile-time disaster
  -- (set/bag-valued 2^k intermediates); it is a config field rather than a
  -- literal so the plumbing already exists if it ever needs to be
  -- user-servicable.
  materializationCardinality :: Int,
  -- | Additional per-function probability-mode variants to compile alongside
  -- the ordinary sum-product one (task semiring-parametric-marginals, design
  -- materialized-marginals-semiring Tier 1): each entry in this list adds one
  -- more 'IRFunGroup' per top-level function, named "<name>_<suffix>" (see
  -- 'SPLL.Semiring.semiringSuffix'), whose only populated slot is 'probFun',
  -- compiled with 'SPLL.Semiring.mkSemiring' fed this family instead of the
  -- default 'SRSumProduct' -- everything else ('prodP'/'mixP'/'enumSumP' and
  -- every leaf combinator built on 'SPLL.Semiring.Semiring') is unchanged, so
  -- the extra group rides the exact same compilation code the ordinary
  -- probability function does. Purely additive: '[]' (the default) changes
  -- nothing about any existing group, so every pre-existing compiled program
  -- is byte-for-byte unaffected. CLI: @--semiring=map@ (comma list of one
  -- token today; @map@ maps onto 'SRMaxProduct', the only family with a real
  -- 'SPLL.Semiring.Semiring' instance -- see 'SemiringFamily').
  --
  -- Scope: each extra family only gets a probability-mode entry point (no
  -- 'integFun'/'genFun'/'normalFun'/'writeLogitsFun') -- CDF and generation have no
  -- settled meaning under max-product (see the task's write-up), and
  -- 'topKThreshold' combined with an extra semiring is untested (topK is
  -- itself already an approximate max-plus mechanism; layering it under an
  -- *exact* 'SRMaxProduct' compile is redundant, not composed).
  --
  -- The requested family follows the program ACROSS top-level function calls:
  -- a body compiled under an extra family references the callee's group of the
  -- same family ("h_map_prob"), via 'SPLL.Semiring.semiringGroupInfix'. That is
  -- not cosmetic -- before it, an extra group was only semiring-correct for the
  -- code inlined into its own body, and any mixture behind a function boundary
  -- was silently summed rather than combined with the requested operator (task
  -- semiring-second-instance-and-kbest). Because extra groups have no
  -- 'integFun', a CDF query that reaches a top-level call under a non-default
  -- family is refused by name at compile time rather than routed to the
  -- callee's sum-product CDF.
  extraSemirings :: [SemiringFamily],
  -- | When True (CLI --memoRecursion; task
  -- recursive-prob-calls-not-shared-across-branches), the Python backends
  -- memoise the probability and integrate methods of every function on a
  -- recursive call cycle, keyed on their argument values, for the duration of
  -- one top-level query: an HMM's likelihood then costs the forward
  -- algorithm's O(n) calls instead of O(2^n). A codegen option only -- the IR
  -- is the same either way, and with the flag off the emitted code is
  -- byte-identical to a compile without it. Ignored under 'topKThreshold'
  -- (the accumulated probability differs per path) and by the Julia backend.
  memoRecursion :: Bool
} deriving (Show)

-- | The probability-mode semiring families 'extraSemirings' can request
-- besides the implicit default 'SRSumProduct' (task
-- semiring-parametric-marginals). Lives here, not in "SPLL.Semiring", purely
-- so 'CompilerConfig' -- itself defined in this module -- can name it in a
-- field without an import cycle; "SPLL.Semiring" re-exports it as part of the
-- same abstraction.
data SemiringFamily = SRSumProduct
                       -- ^ The default: exact probability/density. ⊗ = multiply
                       -- (linear) / add (log), ⊕ = add (linear) / log-sum-exp
                       -- (log). Never requested via 'extraSemirings' --
                       -- it is what every program already compiles with.
                     | SRMaxProduct
                       -- ^ MAP / Viterbi: the probability of the single most
                       -- likely derivation of a query value, rather than the
                       -- total over every derivation. ⊗ unchanged from
                       -- sum-product (independent factors still multiply/add);
                       -- ⊕ becomes max instead of sum/log-sum-exp. AnyExcept
                       -- (marginal-minus-one-branch) has no defined inverse
                       -- under max, so a program reaching that path under this
                       -- family is refused with a named error at compile time.
                     | SRCounting
                       -- ^ Model counting (#SAT) -- NOT implemented, and NOT
                       -- reachable via any accepted CLI/API surface ('Main.hs'
                       -- 's @--semiring=@ parser only accepts @map@;
                       -- 'SPLL.Semiring.mkSemiring' 'error's on this
                       -- constructor rather than emit a wrong answer). Kept as
                       -- a named, documented gap rather than deleted, so the
                       -- next attempt starts from the finding instead of
                       -- rediscovering it: the natural implementation --
                       -- leaves report unit weight instead of their real
                       -- probability, everything else unchanged -- is UNSOUND
                       -- under this codebase's Boolean-condition
                       -- representation. 'IfThenElse'/gt-lt/two-Normal
                       -- comparisons derive @p(cond=False)@ as
                       -- @'SPLL.Semiring.srComplement' p(cond=True)@ (@1 -
                       -- p(cond=True)@ linear) rather than compiling @cond@'s
                       -- False case separately, to avoid an O(2^depth) blowup
                       -- on nested conditions (see the comment at the
                       -- 'IfThenElse' case in IRCompiler.hs). That identity is
                       -- a probability-conservation law: it holds only because
                       -- real probabilities of an exhaustive two-way partition
                       -- sum to 1. A "count" leaf that reports unit weight
                       -- whenever its event is merely POSSIBLE breaks it --
                       -- @main = if Uniform < 0.5 then 1.0 else 2.0@ compiled
                       -- @p(cond=True)@ to the constant 1 (both branches are
                       -- possible, so both get unit weight under the natural
                       -- reading), and @srComplement 1 = 1 - 1 = 0@ then
                       -- reported the False branch -- and hence @count(2.0)@
                       -- -- as impossible: measured @0.0@ against the true
                       -- @1.0@. No 'Semiring'-level fix exists: 'srComplement'
                       -- is a plain @IRExpr -> IRExpr@ function, and the
                       -- correct False-branch weight (0 if @cond@ is
                       -- deterministically true, 1 otherwise) is not a
                       -- function of the collapsed True-branch weight alone --
                       -- it needs the *pre-collapse* probability the collapse
                       -- already discarded.
                       --
                       -- Follow-up task semiring-second-instance-and-kbest
                       -- then MEASURED the two candidate repairs and declined
                       -- both. (a) The proposed shortcut @srComplement = const
                       -- 1@ ("the complement of a count is always
                       -- satisfiable") does fix the program above, but is
                       -- wrong wherever one branch has zero models: on
                       -- @Uniform < 2.0@, @Uniform < 0.0@ and a
                       -- constant-folded condition it reported count 1 for a
                       -- branch with no models at all. (b) Paying the
                       -- O(2^depth) cost -- compiling @cond@'s False case as a
                       -- genuine second recursive call -- repairs ONLY the
                       -- 'IfThenElse' site. The other three 'srComplement'
                       -- sites (gt/lt against a deterministic bound,
                       -- two-Normal comparisons, and the decreasing-transform
                       -- CDF flip in 'SPLL.Semiring.scaleCoV') complement a
                       -- CUMULATIVE value, where there is no "other branch" to
                       -- recompile: the false-side weight is
                       -- @[1 - realCdf > 0]@, and the IR has only a lower-tail
                       -- 'IRCumulative'. Both repairs therefore end at the
                       -- same place -- the counting value must be carried
                       -- ALONGSIDE the real probability rather than in place
                       -- of it -- which is a widening of the 'Semiring'
                       -- interface, declined on cost/benefit. Counting also
                       -- fails independently on multiplicity (two summed coins
                       -- measured 0.25/0.5/0.25 rather than 1/2/1).
                       --
                       -- Satisfiability -- the boolean half this family was
                       -- partly wanted for -- needs none of that, and is
                       -- already answered soundly by the impossibility flag
                       -- ('resultImpossible'), pinned by TestInternals'
                       -- "Satisfiability via the impossibility flag" group on
                       -- the very shapes (b) gets wrong. That works precisely
                       -- because possibility IS a function of the real
                       -- probability, so it rides the sum-product computation;
                       -- multiplicity is not, which is the whole reason
                       -- counting cannot.
                     deriving (Show, Eq, Ord)

-- | The default cardinality budget for marginal materialization. See
-- 'materializationCardinality' for what the number means and why it is 10000.
defaultMaterializationCardinality :: Int
defaultMaterializationCardinality = 10000

-- | Default 'marginalSlots' budget: 16 masks per function, the largest the
-- corpus needs and cheap to compile.
defaultMarginalSlots :: Int
defaultMarginalSlots = 4

defaultCompilerConfig :: CompilerConfig
defaultCompilerConfig = CompilerConfig {countBranches = False, topKThreshold = Nothing, optimizerLevel = 2, verbose = 0, pruneAnyChecks = False, noIntegrate=False, noProbability=False, noGenerate=False, showIntermediates=False, checkQueryType=True, batched=False, logSpace=False, optStats=False, materializationCardinality=defaultMaterializationCardinality, marginalSlots=defaultMarginalSlots, extraSemirings=[], memoRecursion=False}
