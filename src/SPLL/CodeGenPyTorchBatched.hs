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
import SPLL.Lang.Types (CompilerError, GenericValue(..))
import SPLL.CodeGenPyTorch (pyVal)
import Data.Char (toUpper)
import Data.List (intercalate)

-- | Entry point mirroring 'SPLL.CodeGenPyTorch.generateFunctions', but for the
-- batched backend and fallible: it runs the fragment guard over every emitted
-- prob/integ body and returns a refusal diagnostic ('Left') if any is outside
-- the tensor fragment. The 'Bool' is the same generate-boilerplate flag.
generateFunctionsBatched :: Bool -> IREnv -> Either CompilerError [String]
generateFunctionsBatched genBoil (IREnv funcs adts consts)
  | not (null adts) =
      Left "batched mode: ADT declarations are not in the tensor fragment (no tensor representation for constructor-tagged values)."
  | otherwise = do
      classes <- mapM generateClass funcs
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

-- | Emit one function group's class. Only the prob ('forward') and integ
-- ('integrate') methods are emitted: batched sampling is milestone M4, so a
-- group's generate function is skipped here.
generateClass :: IRFunGroup -> Either CompilerError [String]
generateClass (IRFunGroup name _ prob integ _ _ doc) = do
  p <- maybe (Right []) (generateMethod "forward" name) prob
  i <- maybe (Right []) (generateMethod "integrate" name) integ
  let commentLines = map ("# " ++) (lines doc)
      initLine = "class " ++ onHead toUpper name ++ "(Module):"
  return $ commentLines ++ [initLine] ++ indentOnce (i ++ [""] ++ p)

-- | Emit one method: peel the query-type guard and any @isAny@ marginal
-- branches (batched v1 excludes @VAny@), check the residue lies in the tensor
-- fragment, then render it as a let-spine ending in a @return@.
generateMethod :: String -> String -> IRFunDecl -> Either CompilerError [String]
generateMethod methodName groupName (expr, doc) = do
  let (args, body) = unwrapLambdas (prepBatchedBody expr)
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

-- | Push a select whose arms are tuple constructions into per-component selects,
-- so @torch.where@ only ever selects scalar tensors:
-- @select c (T a b) (T x y)  ->  T (select c a x) (select c b y)@.
distributeSelects :: IRExpr -> IRExpr
distributeSelects = irMap d
  where
    d (IRSelect c (IRTCons a b) (IRTCons x y)) =
      IRTCons (distributeSelects (IRSelect c a x)) (distributeSelects (IRSelect c b y))
    d (IRIf c (IRTCons a b) (IRTCons x y)) =
      IRTCons (distributeSelects (IRIf c a x)) (distributeSelects (IRIf c b y))
    d e = e

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
  _              -> False

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
  IREnumSum{}     -> "enumeration sum (IREnumSum); neural/enumerable programs are a later milestone"
  IRIsPossible{}  -> "membership check (IRIsPossible)"
  IRSample{}      -> "random sample (IRSample); batched generate is milestone M4"
  IRError{}       -> "refusal/error arm (IRError); poison-masking is milestone M3"
  IRConformsTo{}  -> "type-conformance check (IRConformsTo)"
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
batchedExpr (IROp op l r)       = "(" ++ batchedExpr l ++ " " ++ batchedOp op ++ " " ++ batchedExpr r ++ ")"
batchedExpr (IRUnaryOp OpNot e) = "torch.logical_not(" ++ batchedExpr e ++ ")"
batchedExpr (IRUnaryOp OpNeg e) = "(-(" ++ batchedExpr e ++ "))"
batchedExpr (IRUnaryOp OpExp e) = "torch.exp(" ++ batchedExpr e ++ ")"
batchedExpr (IRUnaryOp OpLog e) = "torch.log(" ++ batchedExpr e ++ ")"
batchedExpr (IRUnaryOp OpAbs e) = "torch.abs(" ++ batchedExpr e ++ ")"
batchedExpr (IRUnaryOp OpSign e) = "sign(" ++ batchedExpr e ++ ")"
batchedExpr (IRSelect c t f) = torchWhere c t f
batchedExpr (IRIf c t f)     = torchWhere c t f
batchedExpr (IRTCons a b)    = "T(" ++ batchedExpr a ++ ", " ++ batchedExpr b ++ ")"
batchedExpr (IRTFst e)       = "(" ++ batchedExpr e ++ ")[0]"
batchedExpr (IRTSnd e)       = "(" ++ batchedExpr e ++ ")[1]"
batchedExpr (IRTheta e i)    = "(" ++ batchedExpr e ++ ")[0][" ++ show i ++ "]"
batchedExpr (IRSubtree e i)  = "(" ++ batchedExpr e ++ ")[1][" ++ show i ++ "]"
batchedExpr (IRDensity d e)    = "density_" ++ batchedDist d ++ "(" ++ batchedExpr e ++ ")"
batchedExpr (IRCumulative d e) = "cumulative_" ++ batchedDist d ++ "(" ++ batchedExpr e ++ ")"
batchedExpr (IRLetIn name val body) =
  "((" ++ name ++ " := " ++ batchedExpr val ++ "), " ++ batchedExpr body ++ ")[1]"
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
