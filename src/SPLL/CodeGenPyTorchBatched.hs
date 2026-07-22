-- | Batched (tensor) PyTorch code generation (design pytorch-tensorizer, M2).
--
-- The scalar backend ('SPLL.CodeGenPyTorch') emits Python that works one query
-- point at a time: @math.exp@, Python floats, @if@ statements. The batched
-- backend emits /branch-free, elementwise/ Python that feeds a whole batch of
-- query points through at once, using @torch.where@ in place of data-dependent
-- @if@ and @torch.*@ in place of @math.*@. Plain broadcasting then batches it
-- for free (the classic probabilistic-circuits compilation style).
--
-- Two facts make this a small backend rather than a rewrite. First, the select
-- pass ('SPLL.IRSelectPass') has already turned every data-dependent, elementwise
-- 'IRIf' in the prob/integ bodies into an 'IRSelect'; here we simply lower those
-- to @torch.where@ instead of desugaring them back to @if@. Second, once every
-- conditional is a select, a prob body is one big /expression/ — there is no
-- statement-level @if:/elif:@ machinery to emit at all (contrast
-- 'SPLL.CodeGenPyTorch.generateStatementBlock'): the body is a let-spine of
-- assignments ending in a @return@.
--
-- Only the /tensor fragment/ is supported (design "Scope"): float/int/bool
-- leaves in fixed-shape tuples, no lists / ADTs / Either dispatch / recursion /
-- @VAny@ marginals. A program outside it is refused at compile time with a
-- diagnostic naming the offending construct ('batchedGuard'), in the style of
-- the set-valued-witness refusals.
module SPLL.CodeGenPyTorchBatched
  ( generateFunctionsBatched
  , batchedGuard
  , prepBatchedBody
  ) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types (CompilerError, GenericValue(..), MultiValue(..))
import SPLL.Lang.Lang (multiValueToValueList)
import SPLL.CodeGenPyTorch (pyVal, envToLUT, replaceCalls)
import Data.Char (toUpper)
import Data.List (intercalate, isSuffixOf)
import Data.Maybe (fromMaybe)
import Control.Monad (foldM)

-- | Entry point mirroring 'SPLL.CodeGenPyTorch.generateFunctions', but for the
-- batched backend and fallible: it runs the fragment guard over every emitted
-- prob/integ/generate body and returns a refusal diagnostic ('Left') if any is
-- outside the tensor fragment. The 'Bool' is the same generate-boilerplate
-- flag.
--
-- Generate ineligibility (recursive, or a still-unsupported shape) is a hard
-- 'Left' here, exactly like forward/integrate (task neural-generate-parity).
-- M4 originally made a single class's generate ineligibility degrade to a
-- runtime-raising stub rather than aborting the whole compile, because every
-- neural decoder group unconditionally had a 'genFun' and batched generate did
-- not yet support any of them -- a hard failure would have broken batched
-- compilation of every neural corpus program the moment generate was
-- attempted at all. Now that neural decoder generate (categorical/Gaussian
-- sampling) is supported for the non-ADT/non-Either shapes, that blanket
-- exclusion is gone and the remaining ineligible shapes (recursion; Either/ADT
-- decoder output, which already fails to batch-compile via forward/integrate
-- for the same structural reason) are rare enough that a hard refusal is the
-- more honest contract, matching forward/integrate.
generateFunctionsBatched :: Bool -> IREnv -> Either CompilerError [String]
generateFunctionsBatched genBoil env@(IREnv funcs adts consts)
  | not (null adts) =
      Left "batched mode: ADT declarations are not in the tensor fragment (no tensor representation for constructor-tagged values)."
  | otherwise = do
      let lut = envToLUT env
          -- Every group's generate method, raw (pre-rename) name and body: the
          -- self-contained recursion check ('hasGenCycle') walks these
          -- directly, mirroring 'checkCallGraph's raw-name convention.
          genRaw = [ (n ++ "_gen", e) | IRFunGroup{groupName=n, genFun=Just (e, _)} <- funcs ]
          -- Every group's generate arity, keyed by its *post-LUT* name, used to
          -- thread the batch-size parameter through cross-function generate
          -- calls ('attachBatchCalls'), which runs after the same renaming.
          genArities = [ (fromMaybe raw (lookup raw lut), length (fst (unwrapLambdas e))) | (raw, e) <- genRaw ]
      () <- checkCallGraph funcs
      classes <- mapM (generateClass lut genArities genRaw) funcs
      let body = map (\(n, v) -> n ++ " = " ++ pyVal v) consts
             ++ (if null consts then [] else [""])
             ++ concat classes
             ++ ["", "# Example Initialization"]
             ++ map (\IRFunGroup{groupName=n} -> n ++ " = " ++ onHead toUpper n ++ "()") funcs
      return $ if genBoil
        then [ "from pythonLibBatched import *"
             , "import torch"
             , "import math"
             , "from torch.nn import Module", "" ] ++ body
        else body

-- | Emit one function group's class: the prob ('forward'), integ
-- ('integrate'), and generate methods -- all three a hard fragment refusal
-- (task neural-generate-parity: generate's ineligibility used to degrade to a
-- runtime-raising stub per class, M4; it is now a compile-time refusal like
-- forward/integrate, see 'renderGen').
generateClass :: [(String, String)] -> [(String, Int)] -> [(String, IRExpr)] -> IRFunGroup -> Either CompilerError [String]
generateClass lut genArities genMethods (IRFunGroup name gen prob integ _ _ doc) = do
  p <- maybe (Right []) (generateMethod lut "forward" name) prob
  i <- maybe (Right []) (generateMethod lut "integrate" name) integ
  g <- maybe (Right []) (renderGen lut genArities genMethods name) gen
  let commentLines = map ("# " ++) (lines doc)
      initLine = "class " ++ onHead toUpper name ++ "(Module):"
      -- A group with none of forward/integrate/generate (e.g. a tuple
      -- 'component' group carrying only a normal function, which batched mode
      -- does not emit) would otherwise produce a syntactically empty class
      -- body. It is never called (checkCallGraph admits only forward/integrate
      -- callees), so a `pass` body keeps the instantiation valid.
      sections = filter (not . null) [i, p, g]
      methodBody = if null sections then ["pass"] else intercalate [""] sections
  return $ commentLines ++ [initLine] ++ indentOnce methodBody

-- | Emit one method: rewrite cross-function call names to Python @class.method@
-- form (the same @_prob@ → @.forward@ LUT the scalar backend uses), peel the
-- query-type guard and any @isAny@ marginal branches (batched v1 excludes
-- @VAny@), check the residue lies in the tensor fragment, then render it as a
-- let-spine ending in a @return@.
generateMethod :: [(String, String)] -> String -> String -> IRFunDecl -> Either CompilerError [String]
generateMethod lut methodName groupName (expr0, doc) = do
  let expr = irMap (replaceCalls lut) expr0
      (args, body) = unwrapLambdas (prepBatchedBody expr)
  () <- batchedGuard groupName methodName body
  let l1 = "def " ++ methodName ++ "(self" ++ concatMap (", " ++) args ++ "):"
      docLines = map ("# " ++) (lines doc)
  return $ docLines ++ [l1] ++ indentOnce (batchedBlock body)

unwrapLambdas :: IRExpr -> ([String], IRExpr)
unwrapLambdas (IRLambda name rest) = (name : otherNames, plainTree)
  where (otherNames, plainTree) = unwrapLambdas rest
unwrapLambdas anyNode = ([], anyNode)

indentOnce :: [String] -> [String]
indentOnce = map ("    " ++)

onHead :: (a -> a) -> [a] -> [a]
onHead f (x:xs) = f x : xs
onHead _ []     = []

-- ---------------------------------------------------------------------------
-- Generate (milestone M4, extended by task neural-generate-parity):
-- rand()/randn() take a batch shape, and a random `if` becomes a select over
-- per-element draws -- both arms of a select are drawn independently for the
-- whole batch and combined by the same mask machinery prob/integ already use,
-- which is exactly as correct here: each element ends up with one arm's
-- *fresh, independent* draw, so the result is the same mixture distribution
-- as the scalar generate, just with (harmless) extra randomness drawn for the
-- untaken arm.
--
-- A neural decoder's own generate body ('SPLL.AutoNeural.makeGenRec') draws
-- from the decoder's output distribution: a sequential weighted lottery for a
-- discrete/categorical leaf (nested 'IRIf'/'IRSample' 'IRUniform' comparisons
-- against running normalised weight -- mathematically a categorical draw, the
-- same shape 'lottery' already builds for the *scalar* backend, not a fresh
-- policy invented here) and a Gaussian reparameterisation
-- (@mu + sample*sigma@, 'IRSample' 'IRNormal') for a continuous leaf, composed
-- over 'IRTCons' for tuples. None of that needed new IR nodes or new
-- 'pythonLibBatched.py' primitives: every node 'makeGenRec' emits was already
-- in the tensor fragment ('emittable' below), so removing the blanket
-- @isNeuralDecoderGroup@ exclusion this milestone had is sufficient. What
-- remains excluded -- 'EitherPlan' (@IRLeft@/@IRRight@ construction has no
-- tensor representation) and 'ADTPlan' (ADTs are refused for the whole batched
-- compile already, see 'generateFunctionsBatched') -- is refused by the same
-- 'batchedGuard' forward/integrate already goes through, which is no loss:
-- a decoder with an Either/ADT-shaped output already fails to batch-compile at
-- all, since its *probability* reader ('SPLL.AutoNeural.makeProb') hits the
-- same excluded constructs.
-- ---------------------------------------------------------------------------

-- | The batch-size parameter threaded through every generate method and every
-- cross-function generate call. Reserved-looking (matches the compiler's own
-- "_r0"/"_t0"/"cse_0" internal-name convention) so it can never collide with a
-- user-chosen SPLL parameter name (e.g. a helper function genuinely
-- parameterised as @dist n = ...@).
batchNVar :: String
batchNVar = "_batchN"

-- | Render one group's generate method as a real batched @def generate@, or
-- refuse the whole compile ('Left') if it is not eligible.
--
-- Two shapes are excluded, each with its own diagnostic:
--
--   1. Recursive generate (a cycle in the generate-only call graph,
--      'hasGenCycle'): both-arm-eager select semantics would recurse forever
--      at *runtime* (unlike prob/integ, this is not merely a compile-time
--      concern -- Python would stack-overflow actually calling it).
--   2. Any other construct outside the tensor fragment ('batchedGuard', same
--      as forward/integrate): lists, ADTs, Either dispatch (including a
--      neural decoder's own 'EitherPlan'/'ADTPlan' output shape -- see the
--      header comment above), etc.
renderGen :: [(String, String)] -> [(String, Int)] -> [(String, IRExpr)] -> String -> IRFunDecl -> Either CompilerError [String]
renderGen lut genArities genRaw groupName (expr0, doc)
  | hasGenCycle genRaw (groupName ++ "_gen") =
      Left $ "batched mode: " ++ groupName ++ "'s generate function recurses (directly "
        ++ "or through a call chain); data-dependent recursion is outside the tensor fragment "
        ++ "(design pytorch-tensorizer) and both-arm-eager select semantics would not terminate."
  | otherwise =
      let expr = irMap (attachBatchCall genArities . replaceCalls lut) expr0
          (args, body) = unwrapLambdas (prepBatchedBody expr)
      in do
           () <- batchedGuard groupName "generate" body
           let l1 = "def generate(self" ++ concatMap (", " ++) (args ++ [batchNVar]) ++ "):"
               docLines = map ("# " ++) (lines doc)
           Right (docLines ++ [l1] ++ indentOnce (batchedBlock body))

-- | Is there a cycle reachable from @root@ in the call graph restricted to
-- generate methods (@_gen@-suffixed names only, mirroring 'checkCallGraph's
-- restriction to its own method universe)? Same grey/black DFS shape as
-- 'checkCallGraph's 'walk' (a black memo of nodes already proven acyclic, so a
-- diamond-shaped call graph -- shared helpers called from several branches --
-- is not re-explored once per incoming path), specialised to a single root and
-- a plain 'Bool' rather than threading an 'Either' diagnostic.
hasGenCycle :: [(String, IRExpr)] -> String -> Bool
hasGenCycle genMethods root = fst (walk [] [] root)
  where
    callees = graphCallees genMethods
    walk grey black n
      | n `elem` grey  = (True, black)
      | n `elem` black = (False, black)
      | otherwise      = let (cyclic, black') = walkAny (n : grey) black (callees n)
                          in (cyclic, n : black')
    walkAny _    black []     = (False, black)
    walkAny grey black (c:cs) =
      let (cyclic, black') = walk grey black c
      in if cyclic then (True, black') else walkAny grey black' cs

-- | Call-graph edges for a DFS restricted to a given method universe: every
-- 'IRVar' name referenced by @n@'s body that is itself a member of the
-- universe. Shared by 'checkCallGraph' (prob/integ) and 'hasGenCycle'
-- (generate) -- the two graphs differ only in which methods populate
-- @methods@, not in how an edge is read off a body.
graphCallees :: [(String, IRExpr)] -> String -> [String]
graphCallees methods name =
  maybe [] (filter (`elem` map fst methods) . allVarNames) (lookup name methods)

-- | Thread the batch-size parameter through one cross-function generate call:
-- a bare nullary reference (@IRVar name@, the compiler's convention for
-- calling a zero-argument function) becomes @name(_batchN)@, and a *complete*
-- application (all of the callee's declared arguments already supplied, per
-- @arities@) gets one more argument appended, e.g. @dist(0.3)@ becomes
-- @dist(0.3, _batchN)@. Both shapes reduce to the same check via
-- 'collectApplyChain' (a bare 'IRVar' collects zero args), matched by exact
-- arity. Applied bottom-up (fused into the same 'irMap' pass as
-- 'replaceCalls', so cross-function names are already renamed at each node),
-- so an inner complete call is rewritten before an outer node (which might
-- itself be a different complete call) is examined.
attachBatchCall :: [(String, Int)] -> IRExpr -> IRExpr
attachBatchCall arities e
  | (IRVar name, callArgs) <- collectApplyChain e
  , Just ar <- lookup name arities
  , length callArgs == ar
  = IRApply e (IRVar batchNVar)
attachBatchCall _ e = e

-- ---------------------------------------------------------------------------
-- Body preparation: strip the constructs batched v1 does not represent.
-- ---------------------------------------------------------------------------

-- | Normalise a prob/integ body for batched emission, under the outer parameter
-- lambdas:
--
--   1. strip the root query-type guard (@IRConformsTo@ 'IRIf') — its @isinstance@
--      check is meaningless on a tensor, and the fragment guard supplants it at
--      compile time;
--   2. prune @isAny@ marginal checks to 'False' (batched v1 excludes @VAny@) and
--      fold the now-constant selects away;
--   3. push selects through tuple construction so every 'IRSelect' arm is a
--      scalar tensor (a @torch.where@ cannot select whole Python @T@ objects).
prepBatchedBody :: IRExpr -> IRExpr
prepBatchedBody (IRLambda n b) = IRLambda n (prepBatchedBody b)
prepBatchedBody e = distributeSelects (foldConst (pruneAny (stripRootGuard e)))

-- | Strip a root query-type guard @if (sample conforms) then body else error@,
-- taking the conforming arm. Leaves a guard-less body untouched.
stripRootGuard :: IRExpr -> IRExpr
stripRootGuard (IRIf (IRConformsTo _ _) body _) = body
stripRootGuard e = e

-- | Replace every @isAny@ check by 'False': batched v1 has no @VAny@ sample, so
-- a marginal branch is statically not taken.
pruneAny :: IRExpr -> IRExpr
pruneAny = irMap p
  where p (IRUnaryOp OpIsAny _) = IRConst (VBool False)
        p e                     = e

-- | Constant-fold the selects/ifs that pruning made trivial: a literal-mask
-- select picks an arm; equal arms collapse. Bottom-up so inner folds expose
-- outer ones.
foldConst :: IRExpr -> IRExpr
foldConst = irMap f
  where
    f (IRSelect (IRConst (VBool True))  t _) = t
    f (IRSelect (IRConst (VBool False)) _ e) = e
    f (IRIf     (IRConst (VBool True))  t _) = t
    f (IRIf     (IRConst (VBool False)) _ e) = e
    f e = e

-- | Push a /tuple-valued/ select into per-component selects, so @torch.where@
-- only ever selects scalar tensors:
-- @select c (T a b) (T x y)  ->  T (select c a x) (select c b y)@.
--
-- An arm is tuple-valued when, after peeling its @let@-spine, it is an
-- 'IRTCons' (the whole-result guard @select c (let … in T p (T d i)) (T 0 …)@
-- is exactly this shape). Projection is pushed through the let-spine
-- ('projTuple'), so each component select carries the bindings it needs; the
-- optimizer's own field-splitting already duplicates such spines, so this only
-- mirrors that.
distributeSelects :: IRExpr -> IRExpr
distributeSelects = irMap d
  where
    d (IRSelect c t f) | tupleValued t || tupleValued f =
      IRTCons (distributeSelects (IRSelect c (projTuple True t)  (projTuple True f)))
              (distributeSelects (IRSelect c (projTuple False t) (projTuple False f)))
    d (IRIf c t f) | tupleValued t || tupleValued f =
      IRTCons (distributeSelects (IRIf c (projTuple True t)  (projTuple True f)))
              (distributeSelects (IRIf c (projTuple False t) (projTuple False f)))
    d e = e

-- | Does this expression evaluate to a tuple (an 'IRTCons' under its let-spine)?
tupleValued :: IRExpr -> Bool
tupleValued (IRLetIn _ _ b) = tupleValued b
tupleValued (IRTCons _ _)   = True
tupleValued _               = False

-- | Project the first (@fst=True@) or second component out of a tuple-valued
-- expression, pushing the projection through the let-spine so bindings stay in
-- scope. Falls back to 'IRTFst'/'IRTSnd' for a non-literal tuple.
projTuple :: Bool -> IRExpr -> IRExpr
projTuple fstp (IRLetIn n v b) = IRLetIn n v (projTuple fstp b)
projTuple True  (IRTCons a _)  = a
projTuple False (IRTCons _ b)  = b
projTuple True  e              = IRTFst e
projTuple False e              = IRTSnd e

-- ---------------------------------------------------------------------------
-- Call-graph guard: recursion and non-emitted-method calls
-- ---------------------------------------------------------------------------

-- | Batched mode admits cross-function calls (the neural decoder pattern:
-- @main_prob@ → @decoder_prob@ → a network invocation), but only to functions
-- it actually emits from a prob/integ path -- the @forward@ (@_prob@) and
-- @integrate@ (@_integ@) methods -- and only when the call graph is acyclic.
-- Two constructs it must keep refusing (both were caught for free by the old
-- blanket @IRApply@ refusal): a prob/integ call reaching a @generate@/@normal@
-- method (a different compiled artifact entirely -- e.g. scalar
-- @factorial@/@flip@'s prob path), and recursion (unbounded, data-dependent
-- depth is outside the tensor fragment and both-arm-eager evaluation would not
-- terminate; e.g. scalar @dice@).
--
-- This check is unchanged by generate's own admission (M4, 'renderGen'):
-- generate is now sometimes emitted, but it is checked and rendered
-- independently (per class, best-effort) rather than through this hard,
-- whole-program graph -- see 'hasGenCycle' for its own, separate cycle check.
checkCallGraph :: [IRFunGroup] -> Either CompilerError ()
checkCallGraph funcs = () <$ foldM (walk []) [] roots
  where
    methods  = concatMap groupMethods funcs
    roots    = [n | (n, _) <- methods, isEmittedMethod n]
    callees  = graphCallees methods
    -- DFS with a grey path (cycle detection) and a black memo (already proven
    -- clean, so a shared sub-DAG is not re-walked).
    walk grey black name
      | name `elem` grey =
          Left $ "batched mode: " ++ head grey ++ " reaches " ++ name
              ++ " recursively; data-dependent recursion is outside the tensor "
              ++ "fragment (design pytorch-tensorizer)."
      | name `elem` black = Right black
      | not (isEmittedMethod name) =
          Left $ "batched mode: a prob/integ path calls " ++ name
              ++ ", which is not a forward/integrate method (a prob/integ path may only "
              ++ "call other forward/integrate methods; generate and normal_params are "
              ++ "compiled separately -- see design pytorch-tensorizer)."
      | otherwise = do
          black' <- foldM (walk (name : grey)) black (callees name)
          Right (name : black')

groupMethods :: IRFunGroup -> [(String, IRExpr)]
groupMethods (IRFunGroup n gen prob integ enc normal _) =
     [(n ++ "_gen",    b) | Just (b, _) <- [gen]]
  ++ [(n ++ "_prob",   b) | Just (b, _) <- [prob]]
  ++ [(n ++ "_integ",  b) | Just (b, _) <- [integ]]
  ++ [(n ++ "_encode", b) | Just (b, _) <- [enc]]
  ++ [(n ++ "_normal", b) | Just (b, _) <- [normal]]

-- | The only call targets a prob/integ path may reach ('checkCallGraph').
-- Generate has its own, separate admission rule ('renderGen'/'hasGenCycle').
isEmittedMethod :: String -> Bool
isEmittedMethod n = ("_prob" `isSuffixOf` n) || ("_integ" `isSuffixOf` n)

-- | Every 'IRVar' name occurring anywhere in an expression (call-graph edges
-- are these names filtered to the function universe).
allVarNames :: IRExpr -> [String]
allVarNames e = [n | IRVar n <- [e]] ++ concatMap allVarNames (getIRSubExprs e)

-- ---------------------------------------------------------------------------
-- Fragment guard
-- ---------------------------------------------------------------------------

-- | Refuse a body that uses a construct outside the batched tensor fragment,
-- with a diagnostic naming the first offender. Runs on the already-prepared
-- body (guard/isAny stripped), so the only nodes it should see are the ones
-- 'batchedExpr' knows how to emit.
batchedGuard :: String -> String -> IRExpr -> Either CompilerError ()
batchedGuard groupName methodName body =
  case offenders body of
    []      -> Right ()
    (why:_) -> Left $
      "batched mode: " ++ groupName ++ "'s " ++ methodName
      ++ " uses a construct outside the tensor fragment: " ++ why
      ++ ". The tensor fragment (design pytorch-tensorizer) admits only "
      ++ "float/int/bool leaves in fixed-shape tuples -- no lists, ADTs, "
      ++ "Either dispatch, recursion, or marginal (ANY) queries."
  where
    offenders e = [reason e | not (emittable e)] ++ concatMap offenders (getIRSubExprs e)

-- | Is this node one the batched expression emitter handles?
emittable :: IRExpr -> Bool
emittable e = case e of
  IRIf{}         -> True   -- defensive: a residual if lowers like a select
  IRSelect{}     -> True
  IROp{}         -> True
  IRUnaryOp op _ -> op /= OpIsAny   -- isAny must have been pruned
  IRConst VAny       -> False       -- marginal sentinel: no tensor representation
  IRConst (VAnyExcept _) -> False
  IRConst{}      -> True
  IRVar{}        -> True
  IRLetIn{}      -> True
  IRTCons{}      -> True
  IRTFst{}       -> True
  IRTSnd{}       -> True
  IRTheta{}      -> True
  IRSubtree{}    -> True
  IRDensity{}    -> True
  IRCumulative{} -> True
  IRApply{}      -> True   -- network call / cross-function decoder call (M2b)
  IRIndex{}      -> True   -- logit-vector slice or per-element gather (M2b)
  IREnumSum{}    -> True   -- enumeration sum, unrolled over the enum axis (M2b)
  IRIsPossible mv _ -> scalarDiscreteMulti mv  -- membership over a scalar enum (M2b)
  IRError{}      -> True   -- refusal arm, emitted as a selected-away NaN poison (M3)
  IRSample{}     -> True   -- a fresh random draw, batched via rand(n)/randn(n) (M4);
                           -- only ever produced by a generate body, never prob/integ
  _              -> False

-- | A 'MultiValue' whose membership test is a flat scalar enumeration — the only
-- 'IRIsPossible' shape the batched backend renders (an elementwise @x in {..}@
-- mask). Composite membership (tuple/either/ADT structure) is outside the
-- tensor fragment.
scalarDiscreteMulti :: MultiValue -> Bool
scalarDiscreteMulti (MultiDiscretes vs) = not (null vs) && all isScalarV vs
  where isScalarV (VInt _)   = True
        isScalarV (VBool _)  = True
        isScalarV (VFloat _) = True
        isScalarV _          = False
scalarDiscreteMulti _ = False

-- | A human-readable name for an unsupported node, for the refusal diagnostic.
reason :: IRExpr -> String
reason e = case e of
  IRCons{}        -> "list construction (IRCons)"
  IRHead{}        -> "list head (IRHead)"
  IRTail{}        -> "list tail (IRTail)"
  IRMap{}         -> "list map (IRMap)"
  IRIndex{}       -> "list index (IRIndex)"
  IRElementOf{}   -> "list membership (IRElementOf)"
  IRLeft{}        -> "Either constructor (IRLeft)"
  IRRight{}       -> "Either constructor (IRRight)"
  IRFromLeft{}    -> "Either destructor (IRFromLeft)"
  IRFromRight{}   -> "Either destructor (IRFromRight)"
  IRIsLeft{}      -> "Either predicate (IRIsLeft)"
  IRIsRight{}     -> "Either predicate (IRIsRight)"
  IRApply{}       -> "function application (IRApply); a call did not inline"
  IRLambda{}      -> "inner lambda (IRLambda)"
  IRIsPossible{}  -> "membership check (IRIsPossible)"
  IRConformsTo{}  -> "type-conformance check (IRConformsTo)"
  IRConst VAny        -> "marginal ANY sentinel (IRConst VAny); marginal queries are outside the tensor fragment"
  IRConst (VAnyExcept _) -> "marginal ANY-except sentinel (IRConst VAnyExcept); marginal queries are outside the tensor fragment"
  IRUnaryOp OpIsAny _ -> "marginal (ANY) check (IRUnaryOp OpIsAny)"
  _               -> irPrintFlat e

-- ---------------------------------------------------------------------------
-- Emission
-- ---------------------------------------------------------------------------

-- | Render a prepared body as a Python statement block: a spine of @let@
-- bindings emitted as assignments, ending in a single @return@. No @if:@ blocks
-- are ever emitted -- every conditional is a @torch.where@ expression. The
-- result tuple's components are lifted to assignments (like the scalar backend's
-- 'SPLL.CodeGenPyTorch.generateStatementBlock') so a deep world-sum spine stays
-- a sequence of statements rather than one pathologically long expression.
batchedBlock :: IRExpr -> [String]
batchedBlock (IRLetIn name val body) =
  batchedAssign name val ++ batchedBlock body
batchedBlock (IRTCons f s) =
  batchedAssign "_r0" f ++ batchedAssign "_r1" s ++ ["return T(_r0, _r1)"]
batchedBlock e = ["return " ++ batchedExpr e]

-- | Emit a let binding as one or more assignment statements, splitting a
-- let-spine and a tuple construction into separate statements so sharing and
-- statement form are preserved down the tree.
batchedAssign :: String -> IRExpr -> [String]
batchedAssign name (IRLetIn innerName innerVal body) =
  batchedAssign innerName innerVal ++ batchedAssign name body
batchedAssign name (IRTCons f s) =
  batchedAssign (name ++ "_0") f
  ++ batchedAssign (name ++ "_1") s
  ++ [name ++ " = T(" ++ name ++ "_0, " ++ name ++ "_1)"]
batchedAssign name e = [name ++ " = " ++ batchedExpr e]

-- | Emit an expression as branch-free, elementwise Python. Every conditional is
-- a @torch.where@; math functions and boolean operators are their tensor twins.
batchedExpr :: IRExpr -> String
batchedExpr (IRConst v)   = pyVal v
batchedExpr (IRVar name)  = name
batchedExpr (IROp OpApprox l r) = "isclose(" ++ batchedExpr l ++ ", " ++ batchedExpr r ++ ")"
batchedExpr (IROp OpAnd l r)    = "(" ++ batchedExpr l ++ " & " ++ batchedExpr r ++ ")"
batchedExpr (IROp OpOr l r)     = "(" ++ batchedExpr l ++ " | " ++ batchedExpr r ++ ")"
-- OpDiv is gradient-unsafe (division by zero in a masked-away arm yields NaN
-- gradients); route it through the double-where 'safe_div' (design M3).
batchedExpr (IROp OpDiv l r)    = "safe_div(" ++ batchedExpr l ++ ", " ++ batchedExpr r ++ ")"
batchedExpr (IROp op l r)       = "(" ++ batchedExpr l ++ " " ++ batchedOp op ++ " " ++ batchedExpr r ++ ")"
batchedExpr (IRUnaryOp OpNot e) = "torch.logical_not(asmask(" ++ batchedExpr e ++ "))"
batchedExpr (IRUnaryOp OpNeg e) = "(-(" ++ batchedExpr e ++ "))"
batchedExpr (IRUnaryOp OpExp e) = "torch.exp(" ++ batchedExpr e ++ ")"
-- OpLog is gradient-unsafe (log of a non-positive value in a masked-away arm
-- yields NaN gradients); route it through the double-where 'safe_log' (M3).
batchedExpr (IRUnaryOp OpLog e) = "safe_log(" ++ batchedExpr e ++ ")"
batchedExpr (IRUnaryOp OpAbs e) = "torch.abs(" ++ batchedExpr e ++ ")"
batchedExpr (IRUnaryOp OpSign e) = "sign(" ++ batchedExpr e ++ ")"
batchedExpr (IRSelect c t f) = torchWhere c t f
batchedExpr (IRIf c t f)     = torchWhere c t f
-- A fresh random draw (M4): the whole batch's worth at once, shape [_batchN].
-- Both arms of an enclosing select draw independently (see the M4 header
-- comment above 'batchNVar'), so this is correct even under eager both-arm
-- evaluation.
batchedExpr (IRSample IRNormal)  = "randn(" ++ batchNVar ++ ")"
batchedExpr (IRSample IRUniform) = "rand(" ++ batchNVar ++ ")"
batchedExpr (IRTCons a b)    = "T(" ++ batchedExpr a ++ ", " ++ batchedExpr b ++ ")"
batchedExpr (IRTFst e)       = "(" ++ batchedExpr e ++ ")[0]"
batchedExpr (IRTSnd e)       = "(" ++ batchedExpr e ++ ")[1]"
batchedExpr (IRTheta e i)    = "(" ++ batchedExpr e ++ ")[0][" ++ show i ++ "]"
batchedExpr (IRSubtree e i)  = "(" ++ batchedExpr e ++ ")[1][" ++ show i ++ "]"
batchedExpr (IRDensity d e)    = "density_" ++ batchedDist d ++ "(" ++ batchedExpr e ++ ")"
batchedExpr (IRCumulative d e) = "cumulative_" ++ batchedDist d ++ "(" ++ batchedExpr e ++ ")"
-- A call chain: the raw network invocation @net(sym)@ (returning a @[B, n]@
-- logit tensor) or a cross-function decoder call @decoder.forward(logits, sample)@
-- (the function name already rewritten to @class.method@ form by the LUT).
batchedExpr e@(IRApply _ _) =
  let (fn, args) = collectApplyChain e
  in batchedExpr fn ++ "(" ++ intercalate ", " (map batchedExpr args) ++ ")"
-- Indexing a @[B, n]@ logit tensor. A constant logit slot is the last-axis
-- select @out[..., i]@ (dim 0 stays the batch); a per-element index (a @[B]@
-- @sample@ tensor) is a batched gather @nn_gather(out, idx)@.
batchedExpr (IRIndex l (IRConst (VInt i))) =
  "(" ++ batchedExpr l ++ ")[..., " ++ show i ++ "]"
batchedExpr (IRIndex l idx) =
  "nn_gather(" ++ batchedExpr l ++ ", " ++ batchedExpr idx ++ ")"
-- An enumeration sum: sum the body over its enumerable values. The enum axis is
-- known at compile time (a resolved 'MultiValue'), so we unroll it inline —
-- binding @name@ to each value and summing the resulting @[B]@ tensors — rather
-- than going through the scalar backend's runtime @multiValueToValueList@
-- storage (the batched backend keeps no global-storage state). This is the
-- @[E, B]@ enum-axis stack of the design's "Central insight": each arm is
-- evaluated against the whole batch, then reduced over the enum axis.
batchedExpr (IREnumSum name multiVal expr) =
  "sum(map((lambda " ++ name ++ ": " ++ batchedExpr expr ++ "), ["
    ++ intercalate ", " (map (pyVal . valueToIR) (multiValueToValueList multiVal)) ++ "]))"
-- A membership test @x in {v0, ..}@ over a scalar enumeration (e.g. \"is the
-- residual @c - a@ a valid digit?\" in MNIST addition). Rendered as an
-- elementwise @[B]@ bool mask via 'is_member', which evaluates @x@ once.
batchedExpr (IRIsPossible multiVal expr) =
  "is_member(" ++ batchedExpr expr ++ ", ["
    ++ intercalate ", " (map (pyVal . valueToIR) (multiValueToValueList multiVal)) ++ "])"
batchedExpr (IRLetIn name val body) =
  "((" ++ name ++ " := " ++ batchedExpr val ++ "), " ++ batchedExpr body ++ ")[1]"
-- A refusal/error arm has no batched value; emit a NaN poison constant that the
-- enclosing torch.where selects away (design M3). A poison that survives into
-- the output shows up as NaN, caught by the value differential.
batchedExpr (IRError _) = "poison()"
batchedExpr e = error ("batched PyTorch codegen: unexpected node " ++ irPrintFlat e)

-- | @torch.where@: the condition is coerced to a bool tensor ('asmask') so a
-- batch-independent (Python-bool) mask -- e.g. a comparison of two folded
-- constants -- still broadcasts against the tensor arms.
torchWhere :: IRExpr -> IRExpr -> IRExpr -> String
torchWhere c t f =
  "torch.where(asmask(" ++ batchedExpr c ++ "), "
  ++ batchedExpr t ++ ", " ++ batchedExpr f ++ ")"

batchedOp :: Operand -> String
batchedOp OpPlus        = "+"
batchedOp OpMult        = "*"
batchedOp OpGreaterThan = ">"
batchedOp OpLessThan    = "<"
batchedOp OpDiv         = "/"
batchedOp OpSub         = "-"
batchedOp OpEq          = "=="
batchedOp op            = error ("batched PyTorch codegen: no infix form for " ++ show op)

batchedDist :: Distribution -> String
batchedDist IRNormal  = "normal"
batchedDist IRUniform = "uniform"

-- | Flatten a left-nested application spine into the callee and its arguments,
-- in source order (mirrors the scalar backend's 'collectApplyChain').
collectApplyChain :: IRExpr -> (IRExpr, [IRExpr])
collectApplyChain (IRApply f arg) = let (fn, args) = collectApplyChain f in (fn, args ++ [arg])
collectApplyChain e = (e, [])
