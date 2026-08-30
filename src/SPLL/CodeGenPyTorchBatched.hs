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
-- leaves in fixed-shape tuples, no @VAny@ marginals. A
-- program outside it is refused at compile time with a diagnostic naming the
-- offending construct ('batchedGuard'), in the style of the set-valued-witness
-- refusals.
--
-- Lists, @Either@ arms, ADT constructors and structure-directed recursion /are/
-- in the fragment, via design heterogeneous-batch-inference (M1 lists, M2
-- constructor tags): the host bucketing wrapper
-- (@pythonLibBatched.bucketed@) partitions a batch by structural signature
-- before calling the kernel, so within one call the shape is uniform. That
-- turns every shape-directed test into a plain Python bool, which this backend
-- keeps as a real @if@ statement ('structural', 'hoistStructural') over
-- structure-of-arrays data, and makes list recursion terminate at a
-- bucket-uniform depth. What stays refused is the other half of the dichotomy:
-- a *value*-dependent branch that chooses between structures, and
-- value-dependent recursion ('recOffenders').
module SPLL.CodeGenPyTorchBatched
  ( generateFunctionsBatched
  , batchedGuard
  , prepBatchedBody
  , structural
  , hoistStructural
  , SEnv(..)
  , adtEnv
  ) where

import SPLL.IntermediateRepresentation
import SPLL.Typing.RType (shapeRank)
import SPLL.Lang.Types (CompilerError, GenericValue(..), GenericList(..), MultiValue(..), ADTDecl(..), Value)
import SPLL.Lang.Lang (multiValueToValueList)
-- 'pyDouble' is shared with the scalar backend for the same reason
-- 'pyMangle' is: it renders a *Python language* literal, not a call into
-- pythonLib.py. The ban below is on 'pyVal', whose hazard is naming runtime
-- constructors that pythonLibBatched.py does not define.
import SPLL.CodeGenPyTorch (envToLUT, replaceCalls, pyMangle, pyDouble)
import Data.Char (toUpper)
import Data.List (intercalate, isSuffixOf, nub)
import Data.Maybe (fromMaybe, isJust)
import Control.Monad (foldM)
import Control.Monad.State (State, evalState, get, put)

-- | Entry point mirroring 'SPLL.CodeGenPyTorch.generateFunctions', but for the
-- batched backend and fallible: it runs the fragment guard over every emitted
-- prob/integ/generate body and returns a refusal diagnostic ('Left') if any is
-- outside the tensor fragment. The 'Bool' is the same generate-boilerplate
-- flag.
--
-- Generate ineligibility (recursive, or a still-unsupported shape) is a hard
-- 'Left' here, exactly like forward/integrate (task neural-generate-parity,
-- an explicit choice over keeping M4's per-class stub now that neural decoder
-- generate is usually eligible). M4 originally made a single class's generate
-- ineligibility degrade to a runtime-raising stub rather than aborting the
-- whole compile, because every neural decoder group unconditionally had a
-- 'genFun' and batched generate did not yet support any of them -- a hard
-- failure would have broken batched compilation of every neural corpus
-- program the moment generate was attempted at all.
--
-- This has one known, accepted cost in the current corpus: @twiceApplication@
-- (@main = (\f -> f (f Uniform)) (\x -> x * 2.0)@, a nullary higher-order
-- application) has forward/integrate bodies the optimizer beta-reduces down
-- to plain arithmetic, but a *generate* body that still contains a literal,
-- un-reduced 'IRLambda'/'IRApply' -- unrelated to neural decoders, and not
-- something this task's fragment additions cover. Under M4's stub it still
-- contributed forward/integrate coverage to the batched differential; under
-- this hard rule the whole program is refused, dropping it out of batched
-- mode entirely (measured: 92→91 eligible corpus programs, 461→457 points).
-- Accepted per Viktor (2026-07-22) as the honest cost of a hard, uniform
-- contract, rather than special-casing the stub back in for this one shape.
generateFunctionsBatched :: Bool -> IREnv -> Either CompilerError [String]
generateFunctionsBatched genBoil env0 = do
      -- Same identifier hygiene as the scalar backend: ADT names that are
      -- Python keywords are mangled in the emitted code, and every IR
      -- reference to them is renamed to match. The declarations keep the
      -- user's names, so 'ctorNames' below -- which is analysis, matched
      -- against IR variable names rather than printed -- is mangled explicitly.
      let env@(IREnv funcs adts consts) = renameADTIdentifiers pyMangle env0
      let lut = envToLUT env
          -- Every group's generate method, raw (pre-rename) name and body: the
          -- self-contained recursion check ('hasGenCycle') walks these
          -- directly, mirroring 'checkCallGraph's raw-name convention.
          genRaw = [ (n ++ "_gen", e) | IRFunGroup{groupName=n, genFun=Just (e, _)} <- funcs ]
          -- Every group's generate arity, keyed by its *post-LUT* name, used to
          -- thread the batch-size parameter through cross-function generate
          -- calls ('attachBatchCalls'), which runs after the same renaming.
          genArities = [ (fromMaybe raw (lookup raw lut), length (fst (unwrapLambdas e))) | (raw, e) <- genRaw ]
      -- The ADT-derived name sets every pass below shares: constructor names
      -- (the dichotomy guard's notion of *structure*, M2), the nullary ones
      -- (emitted as instantiations, the same rule and reason as
      -- 'SPLL.CodeGenPyTorch.generateFunctions'' callableNames) and the
      -- @is\<Ctor\>@ predicates ('structural' shape-directed conditions).
      let env' = adtEnv adts
      () <- checkCallGraph env' funcs
      classes <- mapM (generateClass env' lut genArities genRaw) funcs
      constLines <- mapM renderConst consts
      let body = generateADTClassesBatched adts ++ constLines
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

-- | The batched twin of 'SPLL.CodeGenPyTorch.generateADTClasses': one Python
-- class per constructor, plus its @is\<Ctor\>@ predicate and field accessors.
-- The constructor tag is structure (part of the bucket signature, uniform
-- within a kernel call), so the predicate answers a plain Python bool; the
-- fields are @[B]@ tensors, so @__eq__@ is elementwise like @T.__eq__@ -- except
-- on a tag mismatch, which is structural and answers a Python @False@.
generateADTClassesBatched :: [ADTDecl] -> [String]
generateADTClassesBatched decls = concatMap one (concatMap constructors decls)
  where
    one (rawName, fieldDecls) =
      let name   = pyMangle rawName
          fields = map (pyMangle . fst) fieldDecls in
      ["class " ++ name ++ ":"]
      ++ indentOnce (("def __init__(self" ++ concatMap (", " ++) fields ++ "):")
           : indentOnce (map (\f -> "self." ++ f ++ " = " ++ f) fields
                         -- Always set _fields, even when empty: the bucketing
                         -- wrapper uses its presence to recognise a
                         -- constructor-tagged value, and a nullary constructor
                         -- is pure tag with nothing to pack.
                         ++ ["self._fields = [" ++ intercalate ", " fields ++ "]"]))
      ++ [""]
      ++ indentOnce ("def __eq__(self, other):"
           : indentOnce (("if not isinstance(other, " ++ name ++ "): return False")
               : [if null fields then "return True"
                  else "return " ++ intercalate " & "
                         [ "(self." ++ f ++ " == other." ++ f ++ ")" | f <- fields ]]))
      ++ [""]
      ++ ["def is" ++ name ++ "(x):"] ++ indentOnce ["return isinstance(x, " ++ name ++ ")"]
      ++ concatMap (\f -> ("def " ++ f ++ "(x):") : indentOnce ["return x." ++ f]) fields
      ++ [""]

-- | Render a top-level constant binding, refusing one whose shape has no
-- batched representation ('batchedVal').
renderConst :: (String, IRValue) -> Either CompilerError String
renderConst (n, v) = case batchedVal v of
  Just s  -> Right (n ++ " = " ++ s)
  Nothing -> Left ("batched mode: top-level constant " ++ n
                   ++ " has a shape with no batched representation: " ++ show v
                   ++ ". The tensor fragment admits only float/int/bool leaves "
                   ++ "in fixed-shape tuples.")

-- | Emit one function group's class: the prob ('forward'), integ
-- ('integrate'), and generate methods -- all three a hard fragment refusal
-- (task neural-generate-parity: generate's ineligibility used to degrade to a
-- runtime-raising stub per class, M4; it is now a compile-time refusal like
-- forward/integrate, see 'renderGen').
generateClass :: SEnv -> [(String, String)] -> [(String, Int)] -> [(String, IRExpr)] -> IRFunGroup -> Either CompilerError [String]
generateClass env lut genArities genMethods (IRFunGroup name gen prob integ _ _ doc dom) = do
  p <- maybe (Right []) (generateMethod env lut "forward" name) prob
  i <- maybe (Right []) (generateMethod env lut "integrate" name) integ
  g <- maybe (Right []) (renderGen env lut genArities genMethods name) gen
  let commentLines = map ("# " ++) (lines doc)
      initLine = "class " ++ onHead toUpper name ++ "(Module):"
      -- Dense enumeration (M3): rendered domain, and the two extra methods per
      -- inference method whose signature it fits. Purely additive -- `forward`,
      -- `integrate` and `generate` above are byte-identical either way.
      domLines = denseDomainLines dom
      pDense = if null domLines then [] else denseMethods env lut "forward" prob
      iDense = if null domLines then [] else denseMethods env lut "integrate" integ
      -- Emit the domain constant only if something reads it: a finite domain on
      -- a group whose methods all take extra per-point arguments is real, but
      -- has no dense entry point to justify the constant.
      domSection = if null pDense && null iDense then [] else domLines
      -- A group with none of forward/integrate/generate (e.g. a tuple
      -- 'component' group carrying only a normal function, which batched mode
      -- does not emit) would otherwise produce a syntactically empty class
      -- body. It is never called (checkCallGraph admits only forward/integrate
      -- callees), so a `pass` body keeps the instantiation valid.
      sections = filter (not . null) [domSection, i, iDense, p, pDense, g]
      methodBody = if null sections then ["pass"] else intercalate [""] sections
  return $ commentLines ++ [initLine] ++ indentOnce methodBody

-- ---------------------------------------------------------------------------
-- Dense enumeration mode (design heterogeneous-batch-inference, Component 2 /
-- M3). When the *query* domain is finite, evaluating the kernel once with the
-- whole domain as the batch gives the @[V]@ probability vector, and any query is
-- a gather into it (@pythonLibBatched.dense_query@). The @[V]@ axis is the
-- ordinary batch axis: nothing inside the kernel changes, and the enumeration a
-- program does *internally* ('IREnumSum') is a separate axis dense mode sits
-- above rather than replaces.
--
-- Everything here is additive. A domain that cannot be rendered, or a method
-- whose signature does not fit, yields no dense methods -- never a refusal,
-- since that would cost the program its ordinary batched eligibility for the
-- sake of an optional extra entry point.

-- | The class-level @DOMAIN@ constant, or @[]@ when there is no renderable
-- finite domain.
denseDomainLines :: Maybe MultiValue -> [String]
-- Deduplicated: a DiscreteValues tag may enumerate the same value by several
-- routes (tupleDiscreteDistrib's tag lists each tuple 3x), and a repeated slot
-- would cost kernel work for a column nothing distinct reads -- and inflate V,
-- which is what dense_query's dispatch compares the batch against.
denseDomainLines dom = case nub <$> (dom >>= (mapM domainVal . multiValueToValueList)) of
  Just vals@(_:_) ->
    [ "# Dense enumeration domain (design heterogeneous-batch-inference, M3): the"
    , "# " ++ show (length vals) ++ " value(s) a query against this function can take."
    , "DOMAIN = [" ++ intercalate ", " vals ++ "]" ]
  _ -> []

-- | Render one domain value as the per-point Python literal @bucketed@ consumes
-- (it packs the leaves into @[B]@ tensors itself). Deliberately separate from
-- 'batchedVal', which answers a different question -- what may appear as a
-- constant *inside* a kernel body -- and must not silently gain cases here.
domainVal :: Value -> Maybe String
domainVal (VFloat f) = Just (pyDouble f)
domainVal (VInt i)   = Just (show i)
domainVal (VBool b)  = Just (if b then "True" else "False")
domainVal (VTuple a b) = (\x y -> "T(" ++ x ++ ", " ++ y ++ ")") <$> domainVal a <*> domainVal b
domainVal (VEither (Left v))  = (\x -> "Left("  ++ x ++ ")") <$> domainVal v
domainVal (VEither (Right v)) = (\x -> "Right(" ++ x ++ ")") <$> domainVal v
domainVal (VADT cn fs) = (\xs -> pyMangle cn ++ "(" ++ intercalate ", " xs ++ ")") <$> mapM domainVal fs
domainVal _ = Nothing

-- | @\<method\>_dense@ / @\<method\>_at@ for one inference method, when its
-- signature admits the domain as a batch: the parameters must be exactly the
-- query value, optionally followed by topK's accumulated probability (which is
-- shared across the batch and broadcasts). A method taking a further per-point
-- argument -- a neural symbol -- is excluded: its dense result would be
-- @[B, V]@, which amortises over nothing.
denseMethods :: SEnv -> [(String, String)] -> String -> Maybe IRFunDecl -> [String]
denseMethods _ _ _ Nothing = []
denseMethods env lut methodName (Just fd)
  | denseArgs (methodArgs env lut fd) =
      [ "def " ++ methodName ++ "_dense(self, *args):"
      ] ++ indentOnce
      [ "# The whole [V] vector: the kernel above, evaluated once with the domain"
      , "# as the batch. Deliberately not cached -- it depends on thetas/weights"
      , "# that nothing here observes changing (see pythonLibBatched)."
      , "return bucketed(self." ++ methodName ++ ", type(self).DOMAIN, *args)" ]
      ++ [ "", "def " ++ methodName ++ "_at(self, samples, *args, dense=None):" ]
      ++ indentOnce
      [ "# Query points answered by gathering into the dense vector when that is"
      , "# the cheaper axis (batch larger than the domain), else by the ordinary"
      , "# kernel. dense=True/False forces the choice."
      , "return dense_query(self." ++ methodName ++ "_dense, self." ++ methodName
        ++ ", type(self).DOMAIN, samples, args, dense)" ]
  | otherwise = []
  where
    denseArgs ["sample"] = True
    denseArgs ["sample", "acc_prob"] = True
    denseArgs _ = False

-- | The parameter names 'generateMethod' will emit for a method, without
-- rendering it (or committing to its fragment check succeeding).
methodArgs :: SEnv -> [(String, String)] -> IRFunDecl -> [String]
methodArgs env lut (expr0, _) = fst (unwrapLambdas (prepBatchedBody env (irMap (replaceCalls lut) expr0)))

-- | Emit one method: rewrite cross-function call names to Python @class.method@
-- form (the same @_prob@ → @.forward@ LUT the scalar backend uses), peel the
-- query-type guard and any @isAny@ marginal branches (batched v1 excludes
-- @VAny@), check the residue lies in the tensor fragment, then render it as a
-- let-spine ending in a @return@.
generateMethod :: SEnv -> [(String, String)] -> String -> String -> IRFunDecl -> Either CompilerError [String]
generateMethod env lut methodName groupNameStr (expr0, doc) = do
  let expr = irMap (replaceCalls lut) expr0
      (args, body) = unwrapLambdas (prepBatchedBody env expr)
  () <- batchedGuard env groupNameStr methodName body
  let l1 = "def " ++ methodName ++ "(self" ++ concatMap (", " ++) args ++ "):"
      docLines = map ("# " ++) (lines doc)
  return $ docLines ++ [l1] ++ indentOnce (batchedBlock env body)

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
renderGen :: SEnv -> [(String, String)] -> [(String, Int)] -> [(String, IRExpr)] -> String -> IRFunDecl -> Either CompilerError [String]
renderGen env lut genArities genRaw groupNameStr (expr0, doc)
  | hasGenCycle genRaw (groupNameStr ++ "_gen") =
      if producesList (lookup (groupNameStr ++ "_gen") genRaw)
        then Right (heterogeneousGenStub groupNameStr)
        else Left $ "batched mode: " ++ groupNameStr ++ "'s generate function recurses (directly "
          ++ "or through a call chain); data-dependent recursion is outside the tensor fragment "
          ++ "(design pytorch-tensorizer) and both-arm-eager select semantics would not terminate."
  | otherwise =
      let expr = irMap (attachBatchCall genArities . replaceCalls lut) expr0
          (args, body) = unwrapLambdas (prepBatchedBody env expr)
      in case batchedGuard env groupNameStr "generate" body of
           -- Drawing a *structurally heterogeneous* sample -- a value-dependent
           -- branch between two shapes -- is the same Component 4 situation as
           -- the recursive list case above: the shapes are the output, so there
           -- is nothing to bucket on. Stub it rather than refusing the whole
           -- program, whose inference over such samples buckets fine.
           Left why | structureBranch env body -> Right (heterogeneousGenStub groupNameStr)
                    | otherwise                 -> Left why
           Right () ->
             let l1 = "def generate(self" ++ concatMap (", " ++) (args ++ [batchNVar]) ++ "):"
                 docLines = map ("# " ++) (lines doc)
             in Right (docLines ++ [l1] ++ indentOnce (batchedBlock env body))

-- | A generate that draws a /structurally heterogeneous/ sample -- a recursion
-- that builds a list, or a value-dependent branch between two shapes -- is the
-- one case where the batch's shapes are the *output* rather than an input to
-- partition on, so there is no bucket to run it in. That is design
-- heterogeneous-batch-inference's Component 4 (per-element dynamic iteration),
-- explicitly deferred there pending a driving program.
--
-- This is the single, narrow exception to the hard-refusal rule task
-- neural-generate-parity established (see 'generateFunctionsBatched'): without
-- it, admitting list-valued *inference* (M1) would buy nothing, because every
-- list-valued corpus program also has a generate function, and a whole-program
-- refusal on it would keep the program out of batched mode entirely. It is
-- scoped by construction to a recursion that constructs a list, so
-- @twiceApplication@ (the accepted cost of the hard rule) is unaffected.
heterogeneousGenStub :: String -> [String]
heterogeneousGenStub groupNameStr =
  [ "# Batched generate for " ++ groupNameStr ++ " is not available: it draws a"
  , "# structurally heterogeneous sample (its shape is decided per element), which"
  , "# is design heterogeneous-batch-inference Component 4. Inference *over* such"
  , "# samples batches fine -- the bucketing wrapper partitions by shape -- but"
  , "# drawing them cannot, because the shapes are the output."
  , "def generate(self, *args, **kwargs):"
  , "    raise NotImplementedError(\"batched generate: " ++ groupNameStr
      ++ " draws a structurally heterogeneous sample \""
  , "                              \"(list length / constructor tag decided per element); that is design "
      ++ "heterogeneous-batch-inference Component 4 (per-element dynamic iteration).\")"
  ]

-- | Does this body contain a /value-dependent/ branch whose arms have different
-- structure -- the shape the dichotomy guard refuses? In a generate body that
-- means the drawn sample's structure is itself random.
structureBranch :: SEnv -> IRExpr -> Bool
structureBranch env e = here e || any (structureBranch env) (getIRSubExprs e)
  where here (IRSelect _ t f) = listValued env t || listValued env f
        here (IRIf c t f)     = not (structural env c)
                             && (listValued env t || listValued env f)
        here _                = False

-- | Does this generate body construct a list?
producesList :: Maybe IRExpr -> Bool
producesList Nothing  = False
producesList (Just e) = go e
  where go x = case x of
          IRCons{}          -> True
          IRConst (VList _) -> True
          _                 -> any go (getIRSubExprs x)

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
--   4. hoist structural (shape-directed) 'IRIf's out of expression positions,
--      so each becomes a real Python @if@ statement (design
--      heterogeneous-batch-inference, Component 1).
prepBatchedBody :: SEnv -> IRExpr -> IRExpr
prepBatchedBody env (IRLambda n b) = IRLambda n (prepBatchedBody env b)
prepBatchedBody env e = hoistStructural env (distributeSelects (foldConst (pruneAny (stripRootGuard e))))

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
-- Structural (shape-directed) control flow -- design
-- heterogeneous-batch-inference, Component 1.
--
-- The tensorizer's dichotomy: *value*-dependent branching is per element and
-- becomes a @torch.where@ (the select pass has already retagged those);
-- *structure*-dependent branching -- "is this list empty?", "which constructor
-- is this?" -- has no tensor representation at all. It does not need one:
-- the host bucketing wrapper ('bucketed' in pythonLibBatched.py) partitions the
-- batch by structural signature before calling the kernel, so within one call
-- every sample has the same shape, every structural test has the same answer
-- for the whole bucket, and it can stay ordinary Python control flow over
-- structure-of-arrays data.
--
-- So the batched backend needs to *recognise* structural conditions, keep them
-- as real @if@ statements, and refuse the shapes where the dichotomy does not
-- hold (a value-dependent branch that chooses between different structures).
-- ---------------------------------------------------------------------------

-- | What every pass over a batched body needs to know about names. One value is
-- built per program by 'adtEnv' and threaded through analysis and emission
-- alike, so the two can never disagree about whether a given node is structure.
--
-- Only 'sBound' varies as a body is walked ('bindS'); the three ADT-derived
-- sets are fixed for the whole program.
data SEnv = SEnv
  { -- | Names @let@-bound to a structurally-determined (batch-independent,
    -- Python-bool) value.
    sBound        :: [String]
    -- | Every constructor name: a value tagged with one is /structure/, which
    -- is what the dichotomy guard refuses to select between.
  , sCtors        :: [String]
    -- | The nullary constructors, which 'batchedExpr' emits as instantiations
    -- rather than as bare class references.
  , sNullaryCtors :: [String]
    -- | The @is\<Ctor\>@ predicate names, which 'structural' recognises as
    -- shape-directed conditions.
  , sCtorPreds    :: [String]
  }

-- | The environment for one program: nothing bound yet, and the three name sets
-- its ADT declarations contribute.
--
-- The predicate spelling is @\"is\" ++ mangled@, matching both
-- 'generateADTClassesBatched' (which prints it) and
-- 'SPLL.IntermediateRepresentation.adtIdentifierRenaming' (which renames IR
-- references to it) -- the constructor is mangled first, then prefixed.
adtEnv :: [ADTDecl] -> SEnv
adtEnv decls = SEnv
  { sBound        = []
  , sCtors        = [ pyMangle cn        | d <- decls, (cn, _)  <- constructors d ]
  , sNullaryCtors = [ pyMangle cn        | d <- decls, (cn, []) <- constructors d ]
  , sCtorPreds    = [ "is" ++ pyMangle cn | d <- decls, (cn, _)  <- constructors d ]
  }

-- | Is this expression's value fixed by the sample's /shape/ alone, hence a
-- plain Python value that is constant across a bucket?
--
-- The only primitive shape probe the compiler emits is a comparison against the
-- empty-list constant (@sample == []@, @tail (tail sample) == []@) -- which the
-- batched 'InferenceList.__eq__' answers with a Python bool precisely when the
-- lengths differ or both are empty. Boolean combinations of those, constants,
-- and previously-bound structural names are structural too. Everything else --
-- notably any comparison against a *non-empty* list, which compares leaves
-- elementwise -- is treated as per-element.
structural :: SEnv -> IRExpr -> Bool
structural env e = case e of
  IRConst _         -> True
  IRVar n           -> n `elem` sBound env
  -- An Either tag test is pure structure: which arm a value is in is part of
  -- its signature, so it is uniform across a bucket (M2).
  IRIsLeft _        -> True
  IRIsRight _       -> True
  IROp OpEq a b     -> isEmptyListConst a || isEmptyListConst b
  IROp OpAnd a b    -> structural env a && structural env b
  IROp OpOr  a b    -> structural env a && structural env b
  IRUnaryOp OpNot a -> structural env a
  IRLetIn n v b     -> structural (bindS env n v) b
  -- An ADT constructor test is the same fact as the Either tag test above:
  -- which constructor a value carries is part of its bucket signature, so the
  -- emitted @is\<Ctor\>@ answers a plain Python bool ('generateADTClassesBatched')
  -- that is uniform across the call. Recognising it is what keeps a sibling
  -- constructor's field accessor out of a masked-away @torch.where@ arm, which
  -- would evaluate it eagerly and raise (task
  -- batched-ctor-test-not-structural-eager-accessor).
  _ | (IRVar n, [_]) <- collectApplyChain e
    , n `elem` sCtorPreds env -> True
  _                 -> False

-- | Extend the structural environment with a @let@ binding (shadowing a
-- previously-structural name that is rebound to a per-element value).
bindS :: SEnv -> String -> IRExpr -> SEnv
bindS env n v | structural env v = env { sBound = nub (n : sBound env) }
              | otherwise        = env { sBound = filter (/= n) (sBound env) }

isEmptyListConst :: IRExpr -> Bool
isEmptyListConst (IRConst (VList EmptyList)) = True
isEmptyListConst _                           = False

-- | Does this expression evaluate to a /structure/ (a list or an @Either@ arm)?
-- Used by the dichotomy guard: a
-- per-element branch (a select, or a residual value-dependent 'IRIf') may not
-- choose between two structures, because @torch.where@ has nothing to select
-- with -- that is precisely the "structure-dependent branching" the bucketing
-- wrapper exists to eliminate, and a program that still contains one after
-- bucketing is outside the fragment.
listValued :: SEnv -> IRExpr -> Bool
listValued env e = case e of
  IRCons{}            -> True
  IRTail{}            -> True
  IRConst (VList _)   -> True
  IRLeft{}            -> True
  IRRight{}           -> True
  IRConst (VEither _) -> True
  IRLetIn _ _ b       -> listValued env b
  IRIf _ t f          -> listValued env t || listValued env f
  IRSelect _ t f      -> listValued env t || listValued env f
  IRConst (VADT _ _)  -> True
  -- An ADT constructor: a bare nullary one (`Heads`) is a reference to the
  -- emitted class, an applied one is a call to it. Either way it builds a
  -- constructor-tagged value, which is structure.
  _ | (IRVar n, _) <- collectApplyChain e -> n `elem` sCtors env
  _                   -> False

-- | Lift every structural 'IRIf' out of expression position into a @let@-bound
-- temporary at the nearest enclosing statement position, so the emitter can
-- render it as a Python @if@ statement block. Arms of a structural @if@ are
-- themselves statement positions, so nothing is ever hoisted /out/ of an arm --
-- which matters: the arm's guard is often what makes evaluating it legal at all
-- (@head sample@ under @if sample != []@).
--
-- Expressions containing no structural @if@ are returned untouched, so this is a
-- no-op for every program in the original (non-heterogeneous) tensor fragment.
hoistStructural :: SEnv -> IRExpr -> IRExpr
hoistStructural env0 top = evalState (stmt env0 top) 0
  where
    -- Statement position: the binding forms keep their shape, everything else
    -- collects hoisted bindings and wraps them around itself.
    stmt :: SEnv -> IRExpr -> State Int IRExpr
    stmt env (IRLambda n b)   = IRLambda n <$> stmt env b
    stmt env (IRLetIn n v b)  = IRLetIn n <$> stmt env v <*> stmt (bindS env n v) b
    stmt env (IRTCons a b)    = IRTCons <$> stmt env a <*> stmt env b
    stmt env (IRIf c t f)
      | structural env c      = IRIf c <$> stmt env t <*> stmt env f
    stmt env e = do
      (e', binds) <- expr env e
      return (foldr (\(n, v) acc -> IRLetIn n v acc) e' binds)

    -- Expression position: replace each structural if by a fresh name.
    expr :: SEnv -> IRExpr -> State Int (IRExpr, [(String, IRExpr)])
    expr env e
      | not (hasStructuralIf env e) = return (e, [])
      | hoistable = do
          e' <- stmt env e
          i  <- get
          put (i + 1)
          let n = "_hs" ++ show i
          return (IRVar n, [(n, e')])
      | otherwise = do
          results <- mapM (expr env) (getIRSubExprs e)
          return (rebuild e (map fst results), concatMap snd results)
      where
        -- A structural if is lifted whole; so is a let-binding spine containing
        -- one, because lifting out of it would move the hoisted binding out of
        -- the scope of the let's own name.
        hoistable = case e of
          IRIf c _ _ -> structural env c
          IRLetIn{}  -> True
          _          -> False

    -- Put rewritten children back, in the order 'getIRSubExprs' produced them.
    rebuild e subs = evalState (irDescendM (const pop) e) subs
      where pop = do { xs <- get; case xs of { (y:ys) -> put ys >> return y; [] -> return (IRConst (VBool False)) } }

-- | Does a structural 'IRIf' occur anywhere in this expression (with @let@
-- scopes threaded, so a name bound to a shape probe counts)?
hasStructuralIf :: SEnv -> IRExpr -> Bool
hasStructuralIf env e = case e of
  IRIf c t f | structural env c -> True
             | otherwise        -> any (hasStructuralIf env) [c, t, f]
  IRLetIn n v b -> hasStructuralIf env v || hasStructuralIf (bindS env n v) b
  _             -> any (hasStructuralIf env) (getIRSubExprs e)

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
checkCallGraph :: SEnv -> [IRFunGroup] -> Either CompilerError ()
checkCallGraph env funcs = do
    () <$ foldM (walk []) [] roots
    mapM_ checkRecursion [(n, prepBatchedBody env b) | (n, b) <- methods, isEmittedMethod n]
  where
    methods  = concatMap groupMethods funcs
    roots    = [n | (n, _) <- methods, isEmittedMethod n]
    callees  = graphCallees methods
    -- Every method that can reach itself: the calls this body makes to any of
    -- them are the ones that need a structural guard.
    cyclic   = [n | (n, _) <- methods, isEmittedMethod n, n `elem` reachable n]
    reachable = go [] . callees
      where go seen []     = seen
            go seen (n:ns)
              | n `elem` seen = go seen ns
              | otherwise     = go (n : seen) (callees n ++ ns)
    checkRecursion (n, body) = case recOffenders cyclic env False body of
      []      -> Right ()
      (why:_) -> Left $ "batched mode: " ++ n ++ " " ++ why
                     ++ ". Structure-directed recursion is admitted (design "
                     ++ "heterogeneous-batch-inference, Component 1: within a "
                     ++ "shape bucket its depth is uniform, so it runs unchanged "
                     ++ "over [B] leaves), but value-dependent recursion is not."
    -- DFS with a grey path (cycle detection) and a black memo (already proven
    -- clean, so a shared sub-DAG is not re-walked).
    walk grey black name
      | name `elem` grey  = Right black   -- a cycle: admissibility is 'checkRecursion's call
      | name `elem` black = Right black
      | not (isEmittedMethod name) =
          Left $ "batched mode: a prob/integ path calls " ++ name
              ++ ", which is not a forward/integrate method (a prob/integ path may only "
              ++ "call other forward/integrate methods; generate and normal_params are "
              ++ "compiled separately -- see design pytorch-tensorizer)."
      | otherwise = do
          black' <- foldM (walk (name : grey)) black (callees name)
          Right (name : black')

-- | Why a recursive call site is /not/ admissible, if it is not. Recursion is
-- in the fragment exactly when it is structure-directed, which needs two things
-- at every call to a cycle member:
--
--   1. it is reached only through a structural (shape-directed) @if@ — so the
--      call is skipped, at Python level, for the bucket that bottoms out.
--      Under eager select semantics a call sitting under a @torch.where@ is
--      /always/ evaluated, so a value-guarded recursion would not terminate;
--   2. it descends: some argument is the tail of a list, so the shrinking
--      structure is what bounds the depth. Together these are the termination
--      argument — the same one the sample's own finite length gives the scalar
--      backend.
--
-- @guarded@ tracks (1) down the traversal; @env@ tracks which names hold
-- structural values ('structural').
recOffenders :: [String] -> SEnv -> Bool -> IRExpr -> [String]
recOffenders cyc env guarded e = case e of
  IRLetIn n v b -> recOffenders cyc env guarded v
                ++ recOffenders cyc (bindS env n v) guarded b
  IRIf c t f | structural env c ->
       recOffenders cyc env guarded c
    ++ recOffenders cyc env True t
    ++ recOffenders cyc env True f
  _ | (IRVar n, args) <- collectApplyChain e, n `elem` cyc ->
       [ "calls " ++ n ++ " recursively from a position that is not guarded by a "
         ++ "structural (shape-directed) test, so both-arm-eager select semantics "
         ++ "would not terminate" | not guarded ]
    ++ [ "calls " ++ n ++ " recursively without descending into the tail of a list "
         ++ "argument, so the recursion is not bounded by the sample's structure"
       | not (any hasTailDescent args) ]
    ++ concatMap (recOffenders cyc env guarded) args
  _ -> concatMap (recOffenders cyc env guarded) (getIRSubExprs e)

-- | Does this argument expression take the tail of a list anywhere?
hasTailDescent :: IRExpr -> Bool
hasTailDescent IRTail{} = True
hasTailDescent e        = any hasTailDescent (getIRSubExprs e)

groupMethods :: IRFunGroup -> [(String, IRExpr)]
groupMethods (IRFunGroup n gen prob integ enc normal _ _) =
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
batchedGuard :: SEnv -> String -> String -> IRExpr -> Either CompilerError ()
batchedGuard env0 groupNameStr methodName body =
  case offenders env0 body of
    []      -> Right ()
    (why:_) -> Left $
      "batched mode: " ++ groupNameStr ++ "'s " ++ methodName
      ++ " uses a construct outside the tensor fragment: " ++ why
      ++ ". The tensor fragment (design pytorch-tensorizer) admits only "
      ++ "float/int/bool leaves in fixed-shape tuples -- no lists, ADTs, "
      ++ "Either dispatch, recursion, or marginal (ANY) queries."
  where
    offenders env e = [reason e | not (emittable e)]
                   ++ [ structureSelectReason | structureSelect env e ]
                   ++ case e of
                        IRLetIn n v b -> offenders env v ++ offenders (bindS env n v) b
                        -- A tensor map's binder is an IRLambda, which the
                        -- fragment otherwise refuses as data-dependent
                        -- application. Here it is a compile-time unroll over a
                        -- static extent -- exactly what the IREnumSum this
                        -- lowering replaces did with a Varname field -- so the
                        -- walk goes through it to the body, skipping the
                        -- lambda node itself (design ir-tensor-values).
                        IRBuiltin BMap [IRLambda _ b, t] ->
                          offenders env b ++ offenders env t
                        _             -> concatMap (offenders env) (getIRSubExprs e)
    -- The dichotomy guard (design heterogeneous-batch-inference): a per-element
    -- branch may not choose between two *structures*. Bucketing removes the
    -- structural branches whose condition is shape-directed; one whose condition
    -- is value-dependent has no tensor form at all (torch.where cannot select
    -- between lists of different length), so it is refused here rather than
    -- emitted as something that dies at run time.
    structureSelect env (IRSelect _ t f) = listValued env t || listValued env f
    structureSelect env (IRIf c t f)     = not (structural env c)
                                        && (listValued env t || listValued env f)
    structureSelect _   _                = False
    structureSelectReason =
      "a value-dependent branch (select) whose arms have different structure; "
      ++ "torch.where cannot select between structures -- only shape-directed "
      ++ "branching is bucketable (design heterogeneous-batch-inference)"

-- | Is this node one the batched expression emitter handles?
emittable :: IRExpr -> Bool
emittable e = case e of
  IRIf{}         -> True   -- defensive: a residual if lowers like a select
  IRSelect{}     -> True
  IROp{}         -> True
  IRUnaryOp op _ -> op /= OpIsAny   -- isAny must have been pruned
  IRConst v      -> isJust (batchedVal v)   -- scalar/tuple leaves only; see 'batchedVal'
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
  IREnumSum _ mv _  -> scalarDiscreteMulti mv  -- enum sum, unrolled over the enum axis (M2b)
  -- Paired (probability, branchCount) enum sum -- only built by a
  -- countBranches compile. Same unrolling as 'IREnumSum', reduced
  -- componentwise; the log-space variant is refused, exactly as the
  -- single-scalar 'IRLogEnumSum' is.
  IREnumSumPaired lg _ mv _ -> not lg && scalarDiscreteMulti mv
  IRIsPossible mv _ -> scalarDiscreteMulti mv  -- membership over a scalar enum (M2b)
  -- The tensor builtins (design ir-tensor-values). All four are emittable: a
  -- tensor is a Python list of [B] tensors, uniform across a bucket, and its
  -- shape is static, so a map is a bucket-uniform unroll and a reduce/index is
  -- one kernel over the [E, B] stack. Nothing here is value-dependent
  -- branching, which is the only thing the batched backend cannot bucket.
  IRBuiltin{}    -> True
  IRError{}      -> True   -- refusal arm, emitted as a selected-away NaN poison (M3)
  IRSample{}     -> True   -- a fresh random draw, batched via rand(n)/randn(n) (M4);
                           -- only ever produced by a generate body, never prob/integ
  -- Structure-of-arrays list access (design heterogeneous-batch-inference, M1):
  -- within a shape bucket a list is a fixed-length Python spine whose leaves are
  -- [B] tensors, so head/tail/cons are the same Python operations the scalar
  -- backend emits -- they are shape operations, uniform across the bucket.
  IRHead{}       -> True
  IRTail{}       -> True
  IRCons{}       -> True
  -- Either dispatch (M2): the tag is part of the shape signature, so within a
  -- bucket `isinstance(x, Left)` is a bucket-uniform Python bool and the arm
  -- accessor is always the legal one.
  IRIsLeft{}     -> True
  IRIsRight{}    -> True
  IRFromLeft{}   -> True
  IRFromRight{}  -> True
  IRLeft{}       -> True
  IRRight{}      -> True
  _              -> False

-- | Render a constant as batched Python, or 'Nothing' if its shape has no
-- batched representation.
--
-- This deliberately does /not/ reuse the scalar backend's
-- 'SPLL.CodeGenPyTorch.pyVal', and that is the whole point: @pyVal@ is total
-- over @IRValue@ against the *scalar* @pythonLib.py@, so it happily names
-- runtime constructors that do not exist in @pythonLibBatched.py@ —
-- @ConsInferenceList@/@EmptyInferenceList@ for lists, @Left@/@Right@ for
-- 'VEither', ADT constructors, @'ANY'@, @throw@, @None@. Emitting any of those
-- produces batched Python that dies with a @NameError@ at run time instead of
-- being refused at compile time. Borrowing @pyVal@ here was a live defect, not
-- a hypothetical one: six corpus programs (the @planEnumCont*@ family,
-- @planEnumInlineBool@, @autoNeuralEncodeTupleDiscrete@) passed 'batchedGuard'
-- and emitted @indexOf(..., ConsInferenceList(True, ...))@ — the enum-index
-- lookup 'SPLL.AutoNeural.indexOf' builds over a 'VList' constant, which the
-- old blanket @IRConst{} -> True@ admitted. The list survives to codegen
-- whenever 'SPLL.IROptimizer.indexmagic' cannot fold it away (it only fires for
-- a @[0..n]@ naturals list, so a @[True, False]@ enumeration keeps the call).
--
-- Keeping this partial, and gating 'IRConst' on it in 'emittable', makes the
-- whole class of defect a compile-time refusal by construction rather than one
-- predicate per call site. The module does not import @pyVal@ at all, so the
-- compiler enforces that.
batchedVal :: IRValue -> Maybe String
batchedVal (VFloat f) = Just (pyDouble f)
batchedVal (VInt i)   = Just (show i)
batchedVal (VBool b)  = Just (if b then "True" else "False")
-- The empty-list constant is the one list constant with a batched form: it is
-- pure structure, and both the shape probe (@sample == []@) and a fixed-length
-- list's spine terminator need it (design heterogeneous-batch-inference, M1). A
-- *non-empty* list constant stays refused — it carries per-element data (e.g.
-- the enumeration `SPLL.AutoNeural.indexOf` builds over, see task
-- batched-bool-enum-index) that the batched runtime has no reader for.
batchedVal (VList EmptyList) = Just "EmptyInferenceList()"
-- An Either constant is a tag plus a payload: the tag is structure (uniform
-- across the bucket), the payload is whatever it is (M2).
batchedVal (VEither (Left v))  = ("Left("  ++) . (++ ")") <$> batchedVal v
batchedVal (VEither (Right v)) = ("Right(" ++) . (++ ")") <$> batchedVal v
batchedVal (VTuple a b) = do
  a' <- batchedVal a
  b' <- batchedVal b
  return ("T(" ++ a' ++ ", " ++ b' ++ ")")
batchedVal _ = Nothing

-- | 'batchedVal' for the emitters, which run only on a body 'batchedGuard' has
-- already accepted. A 'Nothing' here means the guard and the emitter have
-- drifted apart, so it fails the same way the emitter's own catch-all node case
-- does rather than emitting a name the batched runtime lib does not define.
batchedValOrDie :: IRValue -> String
batchedValOrDie v = fromMaybe
  (error ("batched PyTorch codegen: constant with no batched representation: " ++ show v))
  (batchedVal v)

-- | A 'MultiValue' that is a flat enumeration of scalar values — the only shape
-- the two 'MultiValue'-carrying nodes may have. Their emitters ('IRIsPossible' →
-- an elementwise @x in {..}@ mask, 'IREnumSum' → an inline unrolling over the
-- enum axis) render each enumerated value individually, so a composite
-- 'MultiValue' would need a composite constant — refused by 'batchedVal' for the
-- reasons given there. Tuple leaves are excluded here (rather than deferred to
-- 'batchedVal') because neither @is_member@ nor the enum unrolling is known to
-- behave correctly on a structure-of-arrays @T@; widening that needs a test, not
-- an assumption.
--
-- The composite-'MultiValue' direction is not reachable from a real program
-- (an Either/ADT-shaped decoder trips 'IRIsLeft' or the ADT-declaration bail
-- first), so its positive control is the synthetic-IR row in
-- @TestInternals.batchedRefusalUnitTests@ rather than a corpus program.
scalarDiscreteMulti :: MultiValue -> Bool
scalarDiscreteMulti (MultiDiscretes vs) = not (null vs) && all isScalarV vs
  where isScalarV (VInt _)   = True
        isScalarV (VBool _)  = True
        isScalarV (VFloat _) = True
        isScalarV _          = False
scalarDiscreteMulti _ = False

-- | A human-readable name for an unsupported node, for the refusal diagnostic.
-- Only nodes 'emittable' rejects can reach here, so there is no row for the
-- list/Either constructs heterogeneous M1/M2 admitted.
reason :: IRExpr -> String
reason e = case e of
  IRMap{}         -> "list map (IRMap)"
  IRElementOf{}   -> "list membership (IRElementOf)"
  IRApply{}       -> "function application (IRApply); a call did not inline"
  IRLambda{}      -> "inner lambda (IRLambda)"
  IRIsPossible{}  -> "membership check (IRIsPossible) over a non-scalar enumeration"
  IREnumSum{}     -> "enumeration sum (IREnumSum) over a non-scalar enumeration"
  IREnumSumPaired True _ _ _ -> "log-space paired enumeration sum (IREnumSumPaired)"
  IREnumSumPaired{}  -> "paired enumeration sum (IREnumSumPaired) over a non-scalar enumeration"
  IRConformsTo{}  -> "type-conformance check (IRConformsTo)"
  IRConst VAny        -> "marginal ANY sentinel (IRConst VAny); marginal queries are outside the tensor fragment"
  IRConst (VAnyExcept _) -> "marginal ANY-except sentinel (IRConst VAnyExcept); marginal queries are outside the tensor fragment"
  IRConst v       -> "constant with no batched representation (" ++ show v
                     ++ "); the batched runtime lib defines no counterpart for it "
                     ++ "(see batchedVal), so only float/int/bool leaves in "
                     ++ "fixed-shape tuples are admitted"
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
batchedBlock :: SEnv -> IRExpr -> [String]
batchedBlock env (IRLetIn name val body) =
  batchedAssign env name val ++ batchedBlock (bindS env name val) body
-- A structural (shape-directed) if is real Python control flow: within a shape
-- bucket its condition is a plain Python bool, so only one arm runs -- which is
-- what makes structure-directed recursion terminate and what keeps an arm that
-- is illegal for this shape (e.g. `head sample` on an empty list) unevaluated.
batchedBlock env (IRIf c t f) | structural env c =
  ["if " ++ structuralCond env c ++ ":"] ++ indentOnce (batchedBlock env t)
  ++ ["else:"] ++ indentOnce (batchedBlock env f)
batchedBlock env (IRTCons f s) =
  batchedAssign env "_r0" f ++ batchedAssign env "_r1" s ++ ["return T(_r0, _r1)"]
batchedBlock env e = ["return " ++ batchedExpr env e]

-- | Emit a let binding as one or more assignment statements, splitting a
-- let-spine and a tuple construction into separate statements so sharing and
-- statement form are preserved down the tree.
batchedAssign :: SEnv -> String -> IRExpr -> [String]
batchedAssign env name (IRLetIn innerName innerVal body) =
  batchedAssign env innerName innerVal
  ++ batchedAssign (bindS env innerName innerVal) name body
batchedAssign env name (IRIf c t f) | structural env c =
  ["if " ++ structuralCond env c ++ ":"] ++ indentOnce (batchedAssign env name t)
  ++ ["else:"] ++ indentOnce (batchedAssign env name f)
batchedAssign env name (IRTCons f s) =
  batchedAssign env (name ++ "_0") f
  ++ batchedAssign env (name ++ "_1") s
  ++ [name ++ " = T(" ++ name ++ "_0, " ++ name ++ "_1)"]
batchedAssign env name e = [name ++ " = " ++ batchedExpr env e]

-- | Emit a /structural/ condition ('structural') as a plain Python bool
-- expression, rather than the tensor form 'batchedExpr' would give it. The
-- value is a Python bool by construction (a bucket-uniform shape fact), and a
-- Python @if@ should see it as one: @not(x) and not(y)@, not
-- @torch.logical_not(asmask(x)) & ...@, which would only work by 0-d tensor
-- truthiness. It also keeps the failure mode honest — if this ever runs on
-- something that is secretly per-element, torch raises "Boolean value of Tensor
-- with more than one element is ambiguous" instead of silently picking a branch
-- for the whole bucket.
structuralCond :: SEnv -> IRExpr -> String
structuralCond env e = case e of
  IRUnaryOp OpNot a -> "not(" ++ structuralCond env a ++ ")"
  IROp OpAnd a b    -> "(" ++ structuralCond env a ++ " and " ++ structuralCond env b ++ ")"
  IROp OpOr  a b    -> "(" ++ structuralCond env a ++ " or "  ++ structuralCond env b ++ ")"
  _                 -> batchedExpr env e

-- | Emit an expression as branch-free, elementwise Python. Every conditional is
-- a @torch.where@; math functions and boolean operators are their tensor twins.
batchedExpr :: SEnv -> IRExpr -> String
batchedExpr _env (IRConst v)   = batchedValOrDie v
-- A nullary ADT constructor is referred to by a bare 'IRVar', but the emitted
-- name is a *class*: it never satisfies an @is\<Ctor\>@ predicate and never
-- compares equal to an instance. Instantiate it, exactly as the scalar backend's
-- callableNames does.
batchedExpr env (IRVar name)
  | name `elem` sNullaryCtors env = "(" ++ name ++ ")()"
  | otherwise                     = name
batchedExpr env (IROp OpApprox l r) = "isclose(" ++ batchedExpr env l ++ ", " ++ batchedExpr env r ++ ")"
batchedExpr env (IROp OpAnd l r)    = "(" ++ batchedExpr env l ++ " & " ++ batchedExpr env r ++ ")"
batchedExpr env (IROp OpOr l r)     = "(" ++ batchedExpr env l ++ " | " ++ batchedExpr env r ++ ")"
-- OpDiv is gradient-unsafe (division by zero in a masked-away arm yields NaN
-- gradients); route it through the double-where 'safe_div' (design M3).
batchedExpr env (IROp OpDiv l r)    = "safe_div(" ++ batchedExpr env l ++ ", " ++ batchedExpr env r ++ ")"
batchedExpr env (IROp op l r)       = "(" ++ batchedExpr env l ++ " " ++ batchedOp op ++ " " ++ batchedExpr env r ++ ")"
batchedExpr env (IRUnaryOp OpNot e) = "torch.logical_not(asmask(" ++ batchedExpr env e ++ "))"
batchedExpr env (IRUnaryOp OpNeg e) = "(-(" ++ batchedExpr env e ++ "))"
batchedExpr env (IRUnaryOp OpExp e) = "torch.exp(astensor(" ++ batchedExpr env e ++ "))"
-- OpLog is gradient-unsafe (log of a non-positive value in a masked-away arm
-- yields NaN gradients); route it through the double-where 'safe_log' (M3).
batchedExpr env (IRUnaryOp OpLog e) = "safe_log(" ++ batchedExpr env e ++ ")"
-- astensor: these are total on tensors but reject a plain Python float, which a
-- fully constant-folded subexpression (e.g. a literal theta scale) can still be.
batchedExpr env (IRUnaryOp OpAbs e) = "torch.abs(astensor(" ++ batchedExpr env e ++ "))"
batchedExpr env (IRUnaryOp OpSign e) = "sign(" ++ batchedExpr env e ++ ")"
batchedExpr env (IRSelect c t f) = torchWhere env c t f
batchedExpr env (IRIf c t f)     = torchWhere env c t f
-- A fresh random draw (M4): the whole batch's worth at once, shape [_batchN].
-- Both arms of an enclosing select draw independently (see the M4 header
-- comment above 'batchNVar'), so this is correct even under eager both-arm
-- evaluation.
batchedExpr _env (IRSample IRNormal)  = "randn(" ++ batchNVar ++ ")"
batchedExpr _env (IRSample IRUniform) = "rand(" ++ batchNVar ++ ")"
batchedExpr env (IRTCons a b)    = "T(" ++ batchedExpr env a ++ ", " ++ batchedExpr env b ++ ")"
batchedExpr env (IRTFst e)       = "(" ++ batchedExpr env e ++ ")[0]"
batchedExpr env (IRTSnd e)       = "(" ++ batchedExpr env e ++ ")[1]"
batchedExpr env (IRTheta e i)    = "(" ++ batchedExpr env e ++ ")[0][" ++ show i ++ "]"
batchedExpr env (IRSubtree e i)  = "(" ++ batchedExpr env e ++ ")[1][" ++ show i ++ "]"
batchedExpr env (IRDensity d e)    = "density_" ++ batchedDist d ++ "(" ++ batchedExpr env e ++ ")"
batchedExpr env (IRCumulative d e) = "cumulative_" ++ batchedDist d ++ "(" ++ batchedExpr env e ++ ")"
-- A call chain: the raw network invocation @net(sym)@ (returning a @[B, n]@
-- logit tensor) or a cross-function decoder call @decoder.forward(logits, sample)@
-- (the function name already rewritten to @class.method@ form by the LUT).
batchedExpr env e@(IRApply _ _) =
  let (fn, args) = collectApplyChain e
  in batchedExpr env fn ++ "(" ++ intercalate ", " (map (batchedExpr env) args) ++ ")"
-- Indexing a @[B, n]@ logit tensor. A constant logit slot is the last-axis
-- select @out[..., i]@ (dim 0 stays the batch); a per-element index (a @[B]@
-- @sample@ tensor) is a batched gather @nn_gather(out, idx)@.
batchedExpr env (IRIndex l (IRConst (VInt i))) =
  "(" ++ batchedExpr env l ++ ")[..., " ++ show i ++ "]"
batchedExpr env (IRIndex l idx) =
  "nn_gather(" ++ batchedExpr env l ++ ", " ++ batchedExpr env idx ++ ")"
-- An enumeration sum: sum the body over its enumerable values. The enum axis is
-- known at compile time (a resolved 'MultiValue'), so we unroll it inline —
-- binding @name@ to each value and summing the resulting @[B]@ tensors — rather
-- than going through the scalar backend's runtime @multiValueToValueList@
-- storage (the batched backend keeps no global-storage state). This is the
-- @[E, B]@ enum-axis stack of the design's "Central insight": each arm is
-- evaluated against the whole batch, then reduced over the enum axis.
batchedExpr env (IREnumSum name multiVal expr) =
  "sum(map((lambda " ++ name ++ ": " ++ batchedExpr env expr ++ "), ["
    ++ intercalate ", " (map (batchedValOrDie . valueToIR) (multiValueToValueList multiVal)) ++ "]))"
-- The paired form of the above: the body yields a (probability, branchCount)
-- pair per enumerated value, and the two components reduce independently.
-- Evaluating the body once per value and reducing componentwise is the whole
-- point of the node (see 'IREnumSumPaired'), so the unrolled body must appear
-- exactly once here too.
batchedExpr env (IREnumSumPaired _ name multiVal expr) =
  "enum_sum_paired(list(map((lambda " ++ name ++ ": " ++ batchedExpr env expr ++ "), ["
    ++ intercalate ", " (map (batchedValOrDie . valueToIR) (multiValueToValueList multiVal)) ++ "])))"
-- A membership test @x in {v0, ..}@ over a scalar enumeration (e.g. \"is the
-- residual @c - a@ a valid digit?\" in MNIST addition). Rendered as an
-- elementwise @[B]@ bool mask via 'is_member', which evaluates @x@ once.
batchedExpr env (IRIsPossible multiVal expr) =
  "is_member(" ++ batchedExpr env expr ++ ", ["
    ++ intercalate ", " (map (batchedValOrDie . valueToIR) (multiValueToValueList multiVal)) ++ "])"
-- The tensor builtins (design ir-tensor-values). 'BTensor' and 'BMap' produce
-- a Python list of [B] tensors: a map's body is arbitrary IR, so it is
-- evaluated once per element exactly as the enum-sum unrolling above does. The
-- vectorization is in the consumers -- 'BReduce' and 'BIndex' stack that list
-- into one [E, B] tensor and run a single kernel, instead of the E-1
-- sequential adds a Python `sum` over tensors performs, or the E-arm
-- torch.where cascade an if-chain read compiles to. That stacking is the
-- "tensor of primitive lowers to a real tensor" specialization; here an
-- element is always a [B] tensor, so it always applies.
--
-- Rank 1 and axis 0 only, as in the scalar backends: the [E, B] stack already
-- spends the one axis torch is given, and the batch is the other.
batchedExpr env (IRBuiltin (BTensor sh) elems)
  | shapeRank sh == 1 = "[" ++ intercalate ", " (map (batchedExpr env) elems) ++ "]"
  | otherwise = error (batchedRankUnsupported "BTensor" (shapeRank sh))
batchedExpr env (IRBuiltin BMap [IRLambda name body, t]) =
  "[" ++ batchedExpr env body ++ " for " ++ name ++ " in " ++ batchedExpr env t ++ "]"
batchedExpr env (IRBuiltin BMap [f, t]) =
  "list(map(" ++ batchedExpr env f ++ ", " ++ batchedExpr env t ++ "))"
batchedExpr env (IRBuiltin (BReduce op 0) [t]) =
  batchedReduceOp op ++ "(" ++ batchedExpr env t ++ ")"
batchedExpr env (IRBuiltin (BIndex 0) [t, k]) =
  "tensor_index(" ++ batchedExpr env t ++ ", " ++ batchedExpr env k ++ ")"
batchedExpr _ (IRBuiltin (BReduce _ ax) _) = error (batchedAxisUnsupported "BReduce" ax)
batchedExpr _ (IRBuiltin (BIndex ax) _) = error (batchedAxisUnsupported "BIndex" ax)
batchedExpr _ e@(IRBuiltin b args) =
  error ("batched PyTorch codegen: malformed tensor builtin " ++ show b ++ " with "
         ++ show (length args) ++ " arguments: " ++ irPrintFlat e)
batchedExpr env (IRLetIn name val body) =
  "((" ++ name ++ " := " ++ batchedExpr env val ++ "), "
  ++ batchedExpr (bindS env name val) body ++ ")[1]"
-- Structure-of-arrays list access (design heterogeneous-batch-inference, M1):
-- the spine is a Python object, uniform across the bucket; the leaves are [B]
-- tensors. These are exactly the scalar backend's forms.
batchedExpr env (IRHead e)   = "(" ++ batchedExpr env e ++ ")[0]"
batchedExpr env (IRTail e)   = "(" ++ batchedExpr env e ++ ")[1:]"
batchedExpr env (IRCons a b) =
  "ConsInferenceList(" ++ batchedExpr env a ++ ", " ++ batchedExpr env b ++ ")"
-- Either: the same forms the scalar backend emits. The tag test is structural,
-- so it only ever ends up in a Python `if`, never in a torch.where mask.
batchedExpr env (IRLeft e)      = "Left(" ++ batchedExpr env e ++ ")"
batchedExpr env (IRRight e)     = "Right(" ++ batchedExpr env e ++ ")"
batchedExpr env (IRFromLeft e)  = "fromLeft(" ++ batchedExpr env e ++ ")"
batchedExpr env (IRFromRight e) = "fromRight(" ++ batchedExpr env e ++ ")"
batchedExpr env (IRIsLeft e)    = "isinstance(" ++ batchedExpr env e ++ ", Left)"
batchedExpr env (IRIsRight e)   = "isinstance(" ++ batchedExpr env e ++ ", Right)"
-- A refusal/error arm has no batched value; emit a NaN poison constant that the
-- enclosing torch.where selects away (design M3). A poison that survives into
-- the output shows up as NaN, caught by the value differential.
batchedExpr _env (IRError _) = "poison()"
batchedExpr _ e = error ("batched PyTorch codegen: unexpected node " ++ irPrintFlat e)

-- | @torch.where@: the condition is coerced to a bool tensor ('asmask') so a
-- batch-independent (Python-bool) mask -- e.g. a comparison of two folded
-- constants -- still broadcasts against the tensor arms.
torchWhere :: SEnv -> IRExpr -> IRExpr -> IRExpr -> String
torchWhere env c t f =
  "torch.where(asmask(" ++ batchedExpr env c ++ "), "
  ++ batchedExpr env t ++ ", " ++ batchedExpr env f ++ ")"

-- | The batched runtime function reducing a tensor axis with each operator.
-- Both stack the axis and run one kernel; see pythonLibBatched.py.
batchedReduceOp :: ReduceOp -> String
batchedReduceOp ROpAdd = "tensor_sum"
batchedReduceOp ROpLogSumExp = "tensor_logsumexp"

-- | Diagnostics for the tensor ranks and axes this backend does not emit.
batchedRankUnsupported :: String -> Int -> String
batchedRankUnsupported what r =
  what ++ ": only rank-1 tensors are emitted, got rank " ++ show r
       ++ " (the representation admits it; no backend lowers it yet)"

batchedAxisUnsupported :: String -> Int -> String
batchedAxisUnsupported what ax =
  what ++ ": only axis 0 is emitted, got axis " ++ show ax
       ++ " (the representation admits it; no backend lowers it yet)"

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
