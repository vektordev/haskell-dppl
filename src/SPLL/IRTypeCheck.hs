-- | A type discipline for the IR (docs-repo task
-- ir-fuzz-generator-m0-ir-type-checker, design ir-fuzz-generator).
--
-- 'IRExpr' is untyped: nothing stops @IROp OpPlus (IRConst (VBool True))
-- (IRSample IRUniform)@ from being built, and only evaluation finds out. This
-- module is the IR's written contract: a small value-type language, 'IRType',
-- and a checker that accepts or rejects an 'IREnv' against it. An IR fuzz
-- generator draws within it, and the optimizer or a code generator can assert
-- against it.
--
-- The checker is Hindley-Milner inference without annotations, since the IR
-- carries none:
--
-- * Top-level bindings ('reduceIREnv') are split into strongly connected
--   components of their call graph and generalised one component at a time,
--   so a polymorphic helper can be used at two types. Recursion within a
--   component is monomorphic. @let@ is monomorphic.
-- * The standard library ("StandardLibrary") is checked from its IR bodies,
--   not from hand-written types. The implicit functions of every ADT the
--   environment declares get their types from the declaration.
-- * Operations whose typing depends on a type not known yet are deferred
--   constraints: numeric and ordered operands, equality, and every tensor
--   builtin whose result depends on its operand's shape ('BMap', 'BReduce',
--   'BIndex', 'BZip', 'BCategoricalIndex'). A deferred constraint is
--   re-tried as unification learns more. A constraint that is still
--   undecided once its component is generalised travels with the scheme and
--   is re-checked at every use.
--
-- What the contract says, per construct, is in the notes on 'inferExpr'.
-- Where it is stricter or looser than the interpreter is said there too.
--
-- Known looseness: a constraint over type variables that are never resolved
-- is accepted, because some instantiation satisfies each one on its own.
-- Two such constraints on one variable can be jointly unsatisfiable (a
-- variable that is both a tensor reduced by 'BReduce' and an operand of
-- 'OpPlus'), and the checker does not see that.
module SPLL.IRTypeCheck
  ( IRType(..)
  , IRTypeError(..)
  , showIRType
  , showIRTypeError
  , checkIREnv
  , checkIREnvWith
  , inferIRExpr
  , irTypeOfRType
  , neuralExternals
  ) where

import SPLL.IntermediateRepresentation
import SPLL.Lang.Types
import SPLL.Typing.RType (RType(..), TVarR, shapeNumel, dropAxis, prettyShape)
import SPLL.Typing.AlgebraicDataTypes (implicitFunctionRTypes)
import SPLL.Lang.Lang (neuralInputType)
import Data.Maybe (mapMaybe)
import StandardLibrary (standardEnv)

import Control.Monad (forM, forM_, unless, when, zipWithM_, foldM)
import Control.Monad.State.Strict (StateT, evalStateT, get, gets, put, modify', lift)
import Data.Graph (stronglyConnComp, flattenSCC)
import Data.List (nub)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | The value types of the IR.
--
-- Unlike 'RType', a tensor's element type is not restricted to a scalar: the
-- compiler builds 'BTensor's over enumerated domains of tuples, 'Either's and
-- ADT values (an enumerated sum maps over one). A tensor's shape is part of
-- its type, as in 'TTensor', and two tensor types unify only at equal shapes.
data IRType
  = ITBool
  | ITInt
  | ITFloat
  | ITSymbol
  | ITUnit
  | ITThetaTree
  | ITList IRType
  | ITTuple IRType IRType
  | ITEither IRType IRType
  | ITADT String          -- ^ By type name, as 'TADT'.
  | ITTensor Shape IRType
  | ITArrow IRType IRType
  | ITVar Int             -- ^ A type variable. In a checker result, a variable is universally quantified.
  deriving (Show, Eq, Ord)

-- | Why an expression or environment was rejected.
data IRTypeError = IRTypeError
  { typeErrorBinding :: String  -- ^ The top-level binding being checked, or empty for a bare expression.
  , typeErrorExpr    :: IRExpr  -- ^ The innermost expression the failure was found at.
  , typeErrorMessage :: String
  } deriving (Show, Eq)

showIRTypeError :: IRTypeError -> String
showIRTypeError (IRTypeError b e msg) =
  "IR type error" ++ (if null b then "" else " in " ++ b) ++ ": " ++ msg
  ++ "\n  at: " ++ abbreviate 400 (show e)
  where abbreviate n s = if length s > n then take n s ++ " ..." else s

-- | A type with its variables renamed @a@, @b@, ... in order of appearance,
-- so that two types equal up to renaming print the same.
showIRType :: IRType -> String
showIRType t = go False t
  where
    names = Map.fromList (zip (nub (varsOf t)) [0 :: Int ..])
    varName i = let k = Map.findWithDefault i i names
                in if k < 26 then [toEnum (fromEnum 'a' + k)] else 't' : show k
    go _ ITBool = "Bool"
    go _ ITInt = "Int"
    go _ ITFloat = "Float"
    go _ ITSymbol = "Symbol"
    go _ ITUnit = "()"
    go _ ITThetaTree = "ThetaTree"
    go _ (ITList a) = "[" ++ go False a ++ "]"
    go _ (ITTuple a b) = "(" ++ go False a ++ ", " ++ go False b ++ ")"
    go p (ITEither a b) = paren p ("Either " ++ go True a ++ " " ++ go True b)
    go _ (ITADT n) = n
    go p (ITTensor sh a) = paren p ("Tensor" ++ prettyShape sh ++ " " ++ go True a)
    go p (ITArrow a b) = paren p (go True a ++ " -> " ++ go False b)
    go _ (ITVar i) = varName i
    paren True s = "(" ++ s ++ ")"
    paren False s = s

varsOf :: IRType -> [Int]
varsOf (ITVar i) = [i]
varsOf (ITList a) = varsOf a
varsOf (ITTuple a b) = varsOf a ++ varsOf b
varsOf (ITEither a b) = varsOf a ++ varsOf b
varsOf (ITTensor _ a) = varsOf a
varsOf (ITArrow a b) = varsOf a ++ varsOf b
varsOf ITBool = []
varsOf ITInt = []
varsOf ITFloat = []
varsOf ITSymbol = []
varsOf ITUnit = []
varsOf ITThetaTree = []
varsOf (ITADT _) = []

-- ---------------------------------------------------------------------------
-- Deferred constraints

data Constraint
  = CNumeric IRType                     -- ^ Float or Int.
  | COrdered IRType                     -- ^ What 'OpLessThan' compares: numbers, and tuples and lists of them.
  | CEquatable IRType                   -- ^ What 'OpEq' compares: no functions, tensors or theta trees.
  | CMap IRType IRType IRType           -- ^ function, tensor, result of 'BMap'.
  | CReduce Int IRType IRType           -- ^ axis, tensor, result of 'BReduce'.
  | CIndex Int IRType IRType            -- ^ axis, tensor, result of 'BIndex'.
  | CZip Operand IRType IRType IRType   -- ^ operator, two tensors, result of 'BZip'.
  | CWeights IRType                     -- ^ A float list or rank-1 float tensor ('BCategoricalIndex').
  deriving (Show, Eq)

-- | A constraint with the expression it arose at, for the error message.
data Pending = Pending IRExpr Constraint

data Scheme = Scheme [Int] [Pending] IRType

data TCState = TCState
  { tcNext    :: !Int
  , tcSubst   :: IM.IntMap IRType
  , tcPending :: [Pending]
  , tcBinding :: String
  }

type TC = StateT TCState (Either IRTypeError)

data Ctx = Ctx
  { ctxGlobals :: Map.Map String Scheme
  , ctxADTs    :: [ADTDecl]
  , ctxLocals  :: Map.Map String IRType
  }

failAt :: IRExpr -> String -> TC a
failAt e msg = do
  b <- gets tcBinding
  lift (Left (IRTypeError b e msg))

fresh :: TC IRType
fresh = do
  s <- get
  put s { tcNext = tcNext s + 1 }
  return (ITVar (tcNext s))

defer :: IRExpr -> Constraint -> TC ()
defer e c = modify' (\s -> s { tcPending = Pending e c : tcPending s })

-- | Resolve the outermost variable binding.
shallow :: IRType -> TC IRType
shallow t@(ITVar i) = do
  sub <- gets tcSubst
  case IM.lookup i sub of
    Just t' -> shallow t'
    Nothing -> return t
shallow t = return t

zonk :: IRType -> TC IRType
zonk t = do
  t' <- shallow t
  case t' of
    ITList a -> ITList <$> zonk a
    ITTuple a b -> ITTuple <$> zonk a <*> zonk b
    ITEither a b -> ITEither <$> zonk a <*> zonk b
    ITTensor sh a -> ITTensor sh <$> zonk a
    ITArrow a b -> ITArrow <$> zonk a <*> zonk b
    _ -> return t'

unify :: IRExpr -> IRType -> IRType -> TC ()
unify e a0 b0 = do
  a <- shallow a0
  b <- shallow b0
  case (a, b) of
    (ITVar i, ITVar j) | i == j -> return ()
    (ITVar i, t) -> bindVar i t
    (t, ITVar i) -> bindVar i t
    (ITList x, ITList y) -> unify e x y
    (ITTuple x1 x2, ITTuple y1 y2) -> unify e x1 y1 >> unify e x2 y2
    (ITEither x1 x2, ITEither y1 y2) -> unify e x1 y1 >> unify e x2 y2
    (ITArrow x1 x2, ITArrow y1 y2) -> unify e x1 y1 >> unify e x2 y2
    (ITTensor s1 x, ITTensor s2 y) | s1 == s2 -> unify e x y
    _ | a == b -> return ()
    _ -> do
      a' <- zonk a0
      b' <- zonk b0
      failAt e ("cannot match " ++ showIRType a' ++ " with " ++ showIRType b')
  where
    bindVar i t = do
      t' <- zonk t
      when (i `elem` varsOf t') $ failAt e ("infinite type: a variable occurs in " ++ showIRType t')
      modify' (\s -> s { tcSubst = IM.insert i t' (tcSubst s) })

-- | Try to discharge a constraint. 'False' means it is still undecided (its
-- deciding type is a variable); a failure is an error.
attempt :: Pending -> TC Bool
attempt (Pending e c) = case c of
  CNumeric t -> shallow t >>= \t' -> case t' of
    ITFloat -> done
    ITInt -> done
    ITVar _ -> stuck
    other -> bad "a number (Float or Int)" other
  COrdered t -> shallow t >>= \t' -> case t' of
    ITFloat -> done
    ITInt -> done
    ITTuple a b -> defer e (COrdered a) >> defer e (COrdered b) >> done
    ITList a -> defer e (COrdered a) >> done
    ITVar _ -> stuck
    other -> bad "an ordered type (numbers, or tuples or lists of them)" other
  CEquatable t -> shallow t >>= \t' -> case t' of
    ITArrow _ _ -> bad "a type with equality" t'
    ITTensor _ _ -> bad "a type with equality" t'
    ITThetaTree -> bad "a type with equality" t'
    ITList a -> defer e (CEquatable a) >> done
    ITTuple a b -> defer e (CEquatable a) >> defer e (CEquatable b) >> done
    ITEither a b -> defer e (CEquatable a) >> defer e (CEquatable b) >> done
    ITVar _ -> stuck
    _ -> done
  CMap f t r -> shallow t >>= \t' -> case t' of
    ITTensor sh a -> do
      b <- fresh
      unify e f (ITArrow a b)
      unify e r (ITTensor sh b)
      done
    ITVar _ -> stuck
    other -> bad "a tensor" other
  CReduce ax t r -> shallow t >>= \t' -> case t' of
    ITTensor sh a -> do
      unify e a ITFloat
      sh' <- axisDropped ax sh
      unify e r (reshaped sh' ITFloat)
      done
    ITVar _ -> stuck
    other -> bad "a tensor" other
  CIndex ax t r -> shallow t >>= \t' -> case t' of
    ITTensor sh a -> do
      sh' <- axisDropped ax sh
      unify e r (reshaped sh' a)
      done
    ITVar _ -> stuck
    other -> bad "a tensor" other
  CZip op a b r -> do
    a' <- shallow a
    b' <- shallow b
    case (a', b') of
      (ITTensor sh _, _) -> zipAt sh
      (_, ITTensor sh _) -> zipAt sh
      (ITVar _, ITVar _) -> stuck
      (ITVar _, other) -> bad "a tensor" other
      (other, _) -> bad "a tensor" other
    where
      zipAt sh = do
        x <- fresh
        y <- fresh
        z <- fresh
        unify e a (ITTensor sh x)
        unify e b (ITTensor sh y)
        unify e r (ITTensor sh z)
        operandConstraint e op x y z
        done
  CWeights t -> shallow t >>= \t' -> case t' of
    ITList a -> unify e a ITFloat >> done
    ITTensor [_] a -> unify e a ITFloat >> done
    ITVar _ -> stuck
    other -> bad "a list or rank-1 tensor of Float weights" other
  where
    done = return True
    stuck = return False
    bad what t = do
      t' <- zonk t
      failAt e ("expected " ++ what ++ ", got " ++ showIRType t')
    axisDropped ax sh = case dropAxis ax sh of
      Just sh' -> return sh'
      Nothing -> failAt e ("axis " ++ show ax ++ " is out of range for shape " ++ prettyShape sh)
    -- Reducing or indexing the only axis yields the element, not a rank-0 tensor.
    reshaped [] a = a
    reshaped sh a = ITTensor sh a

-- | Re-try the pending constraints until none makes progress.
solve :: TC ()
solve = do
  ps <- gets tcPending
  modify' (\s -> s { tcPending = [] })
  results <- mapM attempt ps
  let undecided = [p | (p, False) <- zip ps results]
  modify' (\s -> s { tcPending = undecided ++ tcPending s })
  when (or results) solve

-- ---------------------------------------------------------------------------
-- Schemes

instantiate :: Scheme -> TC IRType
instantiate (Scheme vs cs t) | null vs = do
  modify' (\s -> s { tcPending = cs ++ tcPending s })
  return t
instantiate (Scheme vs cs t) = do
  fs <- mapM (const fresh) vs
  let m = IM.fromList (zip vs fs)
  forM_ cs $ \(Pending e c) -> defer e (substC m c)
  return (substT m t)

substT :: IM.IntMap IRType -> IRType -> IRType
substT m t = case t of
  ITVar i -> IM.findWithDefault t i m
  ITList a -> ITList (substT m a)
  ITTuple a b -> ITTuple (substT m a) (substT m b)
  ITEither a b -> ITEither (substT m a) (substT m b)
  ITTensor sh a -> ITTensor sh (substT m a)
  ITArrow a b -> ITArrow (substT m a) (substT m b)
  _ -> t

substC :: IM.IntMap IRType -> Constraint -> Constraint
substC m c = case c of
  CNumeric t -> CNumeric (s t)
  COrdered t -> COrdered (s t)
  CEquatable t -> CEquatable (s t)
  CMap f t r -> CMap (s f) (s t) (s r)
  CReduce ax t r -> CReduce ax (s t) (s r)
  CIndex ax t r -> CIndex ax (s t) (s r)
  CZip op a b r -> CZip op (s a) (s b) (s r)
  CWeights t -> CWeights (s t)
  where s = substT m

zonkC :: Constraint -> TC Constraint
zonkC c = case c of
  CNumeric t -> CNumeric <$> zonk t
  COrdered t -> COrdered <$> zonk t
  CEquatable t -> CEquatable <$> zonk t
  CMap f t r -> CMap <$> zonk f <*> zonk t <*> zonk r
  CReduce ax t r -> CReduce ax <$> zonk t <*> zonk r
  CIndex ax t r -> CIndex ax <$> zonk t <*> zonk r
  CZip op a b r -> CZip op <$> zonk a <*> zonk b <*> zonk r
  CWeights t -> CWeights <$> zonk t

constraintVars :: Constraint -> [Int]
constraintVars c = case c of
  CNumeric t -> varsOf t
  COrdered t -> varsOf t
  CEquatable t -> varsOf t
  CMap f t r -> varsOf f ++ varsOf t ++ varsOf r
  CReduce _ t r -> varsOf t ++ varsOf r
  CIndex _ t r -> varsOf t ++ varsOf r
  CZip _ a b r -> varsOf a ++ varsOf b ++ varsOf r
  CWeights t -> varsOf t

-- | A closed type's scheme: every variable in it is quantified.
closedScheme :: IRType -> Scheme
closedScheme t = Scheme (nub (varsOf t)) [] t

-- ---------------------------------------------------------------------------
-- Inference

-- | The typing rule of each construct.
--
-- * 'IRIf' and 'IRSelect': a 'ITBool' condition, both arms of one type.
-- * 'IROp': 'OpPlus', 'OpMult', 'OpSub', 'OpMax' take two numbers of one
--   type; 'OpDiv' two floats; 'OpIntDiv', 'OpMod' two ints; 'OpOr', 'OpAnd'
--   two bools; 'OpGreaterThan', 'OpLessThan' two ordered values of one type;
--   'OpEq' two values of one type with equality; 'OpApprox' two floats.
-- * 'IRUnaryOp': 'OpNeg', 'OpSign', 'OpAbs' on a number; 'OpExp', 'OpLog'
--   on a float; 'OpNot' on a bool; 'OpIsAny' on anything, answering a bool.
-- * 'IRConst': the value's type. A marginal-query hole ('VAny',
--   'VAnyExcept', 'AnyList') and 'VError' have any type.
-- * 'IRConstruct' and 'IRDestruct': tuples, cons lists, 'Either' and theta
--   trees, as their names say. The interpreter also lets 'AcFst'/'AcSnd'
--   push through a closure; the contract does not.
-- * 'IRDensity', 'IRCumulative': a float to a float. 'IRSample': a float.
-- * 'IRIsPossible', 'IRConformsTo': anything to a bool.
-- * 'IRError': any type.
-- * 'IRBuiltin': per 'Builtin'. 'BTensor' elements share one type, which may
--   be any type; 'BReduce' folds a float tensor; 'BIndex' and
--   'BListIndex' take an 'ITInt' key; 'BCategoricalIndex' takes a float and
--   a float list or rank-1 float tensor and answers an int.
-- * Arity: an 'IRConstruct' or 'IRBuiltin' with the wrong argument count is
--   rejected rather than reported by 'error' ('expectConTagArgs',
--   'expectBuiltinArgs').
--
-- 'OpEq' accepts 'ITSymbol', which the interpreter's 'OpEq' has no case for.
--
-- Value preconditions the types do not carry (the IR fuzz generator draws
-- within them; docs task ir-fuzz-generator-m1-deterministic-scalar):
-- 'OpIntDiv' and 'OpMod' are defined only for a nonzero divisor that divides
-- the dividend, the shape the compiler emits them in (the backends round
-- differently elsewhere, and the interpreter throws on a zero divisor);
-- and 'ITInt' arithmetic stays inside 64 bits (Python's ints do not wrap).
-- Both arms of an 'IRSelect' are evaluated by the batched backend (a
-- @torch.where@), so neither may raise where the condition does not select
-- it: no partial destructor ('AcHead', 'AcTail', 'AcFromLeft', 'AcFromRight')
-- or index ('BIndex', 'BListIndex') outside its domain. An 'IRError' arm is
-- masked (@poison()@), and scalar consumers lower a select to a lazy if (docs
-- task ir-fuzz-generator-m4-generate-and-batched).
inferExpr :: Ctx -> IRExpr -> TC IRType
inferExpr ctx expr = case expr of
  IRIf c a b -> conditional c a b
  IRSelect c a b -> conditional c a b
  IROp op a b -> do
    ta <- inferExpr ctx a
    tb <- inferExpr ctx b
    r <- fresh
    operandConstraint expr op ta tb r
    return r
  IRUnaryOp op a -> do
    ta <- inferExpr ctx a
    case op of
      OpNeg -> numeric ta
      OpSign -> numeric ta
      OpAbs -> numeric ta
      OpNot -> unify expr ta ITBool >> return ITBool
      OpExp -> unify expr ta ITFloat >> return ITFloat
      OpLog -> unify expr ta ITFloat >> return ITFloat
      OpIsAny -> return ITBool
  IRConst v -> valueType ctx expr v
  IRConstruct tag args -> do
    unless (length args == conTagArity tag) $
      failAt expr ("IRConstruct " ++ show tag ++ " takes " ++ show (conTagArity tag)
                   ++ " arguments, got " ++ show (length args))
    ts <- mapM (inferExpr ctx) args
    case (tag, ts) of
      (TgTuple, [a, b]) -> return (ITTuple a b)
      (TgCons, [h, t]) -> unify expr t (ITList h) >> return t
      (TgLeft, [a]) -> ITEither a <$> fresh
      (TgRight, [b]) -> (`ITEither` b) <$> fresh
      _ -> failAt expr "IRConstruct: arity mismatch"
  IRDestruct acc a -> do
    ta <- inferExpr ctx a
    case acc of
      AcFst -> do { x <- fresh; y <- fresh; unify expr ta (ITTuple x y); return x }
      AcSnd -> do { x <- fresh; y <- fresh; unify expr ta (ITTuple x y); return y }
      AcHead -> do { x <- fresh; unify expr ta (ITList x); return x }
      AcTail -> do { x <- fresh; unify expr ta (ITList x); return ta }
      AcFromLeft -> do { x <- fresh; y <- fresh; unify expr ta (ITEither x y); return x }
      AcFromRight -> do { x <- fresh; y <- fresh; unify expr ta (ITEither x y); return y }
      AcIsLeft -> do { x <- fresh; y <- fresh; unify expr ta (ITEither x y); return ITBool }
      AcIsRight -> do { x <- fresh; y <- fresh; unify expr ta (ITEither x y); return ITBool }
      AcTheta _ -> unify expr ta ITThetaTree >> return ITFloat
      AcSubtree _ -> unify expr ta ITThetaTree >> return ITThetaTree
  IRDensity _ _ a -> floatToFloat a
  IRCumulative _ _ a -> floatToFloat a
  IRSample _ -> return ITFloat
  IRLetIn v d b -> do
    td <- inferExpr ctx d
    inferExpr ctx { ctxLocals = Map.insert v td (ctxLocals ctx) } b
  IRVar v -> case Map.lookup v (ctxLocals ctx) of
    Just t -> return t
    Nothing -> case Map.lookup v (ctxGlobals ctx) of
      Just sc -> instantiate sc
      Nothing -> failAt expr ("unbound variable " ++ v)
  IRLambda v b -> do
    a <- fresh
    tb <- inferExpr ctx { ctxLocals = Map.insert v a (ctxLocals ctx) } b
    return (ITArrow a tb)
  IRApply f x -> do
    tf <- inferExpr ctx f
    tx <- inferExpr ctx x
    r <- fresh
    unify expr tf (ITArrow tx r)
    return r
  IRIsPossible _ a -> inferExpr ctx a >> return ITBool
  IRConformsTo _ a -> inferExpr ctx a >> return ITBool
  IRError _ -> fresh
  IRBuiltin b args -> builtin b args
  where
    conditional c a b = do
      tc <- inferExpr ctx c
      unify expr tc ITBool
      ta <- inferExpr ctx a
      tb <- inferExpr ctx b
      unify expr ta tb
      return ta
    numeric t = defer expr (CNumeric t) >> return t
    floatToFloat a = do
      ta <- inferExpr ctx a
      unify expr ta ITFloat
      return ITFloat
    builtin b args = do
      case b of
        BTensor sh -> do
          when (null sh) $ failAt expr "BTensor: a tensor has rank at least 1"
          unless (length args == shapeNumel sh) $
            failAt expr ("BTensor " ++ prettyShape sh ++ " takes " ++ show (shapeNumel sh)
                         ++ " elements, got " ++ show (length args))
        _ -> case builtinArity b of
          Just n | length args /= n ->
            failAt expr (show b ++ " takes " ++ show n ++ " arguments, got " ++ show (length args))
          _ -> return ()
      ts <- mapM (inferExpr ctx) args
      r <- fresh
      case (b, ts) of
        (BTensor sh, _) -> do
          forM_ ts (unify expr r)
          return (ITTensor sh r)
        (BMap, [f, t]) -> defer expr (CMap f t r) >> return r
        (BReduce _ ax, [t]) -> defer expr (CReduce ax t r) >> return r
        (BIndex ax, [t, k]) -> do
          unify expr k ITInt
          defer expr (CIndex ax t r)
          return r
        (BZip op, [x, y]) -> defer expr (CZip op x y r) >> return r
        (BMapList, [f, xs]) -> do
          a <- fresh
          unify expr xs (ITList a)
          unify expr f (ITArrow a r)
          return (ITList r)
        (BListIndex, [xs, k]) -> do
          unify expr xs (ITList r)
          unify expr k ITInt
          return r
        (BCategoricalIndex _ n, [u, w]) -> do
          when (n < 1) $ failAt expr "BCategoricalIndex: needs at least one weight"
          unify expr u ITFloat
          defer expr (CWeights w)
          return ITInt
        _ -> failAt expr (show b ++ ": arity mismatch")

-- | The typing of a binary 'Operand' applied to operands of type @a@ and @b@
-- with result type @r@. Shared by 'IROp' and the elementwise 'BZip'.
operandConstraint :: IRExpr -> Operand -> IRType -> IRType -> IRType -> TC ()
operandConstraint e op a b r = case op of
  OpPlus -> arith
  OpMult -> arith
  OpSub -> arith
  OpMax -> arith
  OpDiv -> allOf ITFloat
  OpIntDiv -> allOf ITInt
  OpMod -> allOf ITInt
  OpOr -> allOf ITBool
  OpAnd -> allOf ITBool
  OpGreaterThan -> compare' COrdered
  OpLessThan -> compare' COrdered
  OpEq -> compare' CEquatable
  OpApprox -> unify e a ITFloat >> unify e b ITFloat >> unify e r ITBool
  where
    arith = unify e a b >> unify e r a >> defer e (CNumeric a)
    allOf t = unify e a t >> unify e b t >> unify e r t
    compare' k = unify e a b >> unify e r ITBool >> defer e (k a)

-- | The type of a constant.
valueType :: Ctx -> IRExpr -> IRValue -> TC IRType
valueType ctx e v = case v of
  VBool _ -> return ITBool
  VInt _ -> return ITInt
  VSymbol _ -> return ITSymbol
  VFloat _ -> return ITFloat
  VUnit -> return ITUnit
  VThetaTree _ -> return ITThetaTree
  VList l -> do
    a <- fresh
    listElems a l
    return (ITList a)
  VTuple x y -> ITTuple <$> valueType ctx e x <*> valueType ctx e y
  VEither (Left x) -> ITEither <$> valueType ctx e x <*> fresh
  VEither (Right y) -> ITEither <$> fresh <*> valueType ctx e y
  VTensor sh xs -> do
    when (null sh) $ failAt e "a tensor value has rank at least 1"
    unless (length xs == shapeNumel sh) $
      failAt e ("a tensor value of shape " ++ prettyShape sh ++ " holds "
                ++ show (length xs) ++ " elements")
    a <- fresh
    forM_ xs $ \x -> valueType ctx e x >>= unify e a
    return (ITTensor sh a)
  VADT ctor fields -> case [ (dataName d, fs) | d <- ctxADTs ctx, (c, fs) <- constructors d, c == ctor ] of
    ((tyName, fs) : _) -> do
      unless (length fs == length fields) $
        failAt e ("constructor " ++ ctor ++ " has " ++ show (length fs) ++ " fields, the value "
                  ++ show (length fields))
      declared <- rtypesToIR (map snd fs)
      zipWithM_ (\fv ft -> valueType ctx e fv >>= unify e ft) fields declared
      return (ITADT tyName)
    [] -> failAt e ("unknown ADT constructor " ++ ctor)
  VClosure env param body -> do
    bound <- forM env $ \(n, x) -> (,) n <$> inferExpr ctx { ctxLocals = Map.empty } x
    a <- fresh
    -- The closure's environment is innermost first, as the interpreter builds it.
    let locals = Map.insert param a (Map.fromListWith (\_new old -> old) bound)
    tb <- inferExpr ctx { ctxLocals = locals } body
    return (ITArrow a tb)
  VAny -> fresh
  VAnyExcept _ -> fresh
  VError _ -> fresh
  where
    listElems a l = case l of
      EmptyList -> return ()
      AnyList -> return ()
      ListCont x rest -> do
        valueType ctx e x >>= unify e a
        listElems a rest

-- | Translate declared 'RType's (ADT fields, implicit-function signatures),
-- one variable per distinct 'TVarR' across the list. 'RType's with no
-- runtime content of their own ('NotSetYet', 'GreaterType', 'BottomTuple')
-- become fresh variables.
rtypesToIR :: [RType] -> TC [IRType]
rtypesToIR rts = evalStateT (mapM go rts) Map.empty
  where
    go :: RType -> StateT (Map.Map TVarR IRType) TC IRType
    go rt = case rt of
      TBool -> return ITBool
      TInt -> return ITInt
      TSymbol -> return ITSymbol
      TFloat -> return ITFloat
      TUnit -> return ITUnit
      TThetaTree -> return ITThetaTree
      ListOf a -> ITList <$> go a
      Tuple a b -> ITTuple <$> go a <*> go b
      TEither a b -> ITEither <$> go a <*> go b
      TADT n -> return (ITADT n)
      NullList -> ITList <$> lift fresh
      BottomTuple -> lift fresh
      TArrow a b -> ITArrow <$> go a <*> go b
      TTensor sh a -> ITTensor sh <$> go a
      TVarR v -> do
        m <- get
        case Map.lookup v m of
          Just t -> return t
          Nothing -> do
            t <- lift fresh
            put (Map.insert v t m)
            return t
      GreaterType _ _ -> lift fresh
      NotSetYet -> lift fresh

-- | A monomorphic 'RType' as an 'IRType'. 'Nothing' when it holds a type
-- variable or one of the 'RType's with no runtime content of their own.
irTypeOfRType :: RType -> Maybe IRType
irTypeOfRType rt = case rt of
  TBool -> Just ITBool
  TInt -> Just ITInt
  TSymbol -> Just ITSymbol
  TFloat -> Just ITFloat
  TUnit -> Just ITUnit
  TThetaTree -> Just ITThetaTree
  ListOf a -> ITList <$> irTypeOfRType a
  Tuple a b -> ITTuple <$> irTypeOfRType a <*> irTypeOfRType b
  TEither a b -> ITEither <$> irTypeOfRType a <*> irTypeOfRType b
  TADT n -> Just (ITADT n)
  TArrow a b -> ITArrow <$> irTypeOfRType a <*> irTypeOfRType b
  TTensor sh a -> ITTensor sh <$> irTypeOfRType a
  NullList -> Nothing
  BottomTuple -> Nothing
  TVarR _ -> Nothing
  GreaterType _ _ -> Nothing
  NotSetYet -> Nothing

-- | The externals a compiled environment needs for its neural declarations,
-- for 'checkIREnvWith'. In the IR a network maps its input to its logit
-- vector, a list of floats ("MockNN"). A 'TSymbol' input is opaque to the
-- IR (the interpreter's mocks read a tuple encoding out of it), so it is
-- typed as a variable.
neuralExternals :: [NeuralDecl] -> [(String, IRType)]
neuralExternals = mapMaybe external
  where
    external (n, rt, _) = do
      inp <- neuralInputType rt
      t <- if inp == TSymbol then Just (ITVar 0) else irTypeOfRType inp
      return (n, ITArrow t (ITList ITFloat))

-- ---------------------------------------------------------------------------
-- Binding groups

-- | Check a list of top-level bindings, a strongly connected component of
-- their call graph at a time, and add their generalised schemes to the
-- globals. A name bound twice keeps its first binding, as in the interpreter.
checkBindings :: [ADTDecl] -> Map.Map String Scheme -> [(String, IRExpr)] -> TC (Map.Map String Scheme)
checkBindings decls globals0 bindings0 = foldM checkComponent globals0 components
  where
    bindings = dedupe Set.empty bindings0
    dedupe _ [] = []
    dedupe seen ((n, e) : rest)
      | n `Set.member` seen = dedupe seen rest
      | otherwise = (n, e) : dedupe (Set.insert n seen) rest
    names = Set.fromList (map fst bindings)
    components = map flattenSCC (stronglyConnComp
      [ ((n, e), n, Set.toList (Set.intersection names (mentions e))) | (n, e) <- bindings ])
    checkComponent globals comp = do
      vars <- mapM (const fresh) comp
      let mono = Map.fromList [ (n, Scheme [] [] t) | ((n, _), t) <- zip comp vars ]
          ctx = Ctx { ctxGlobals = Map.union mono globals, ctxADTs = decls, ctxLocals = Map.empty }
      forM_ (zip comp vars) $ \((n, e), t) -> do
        modify' (\s -> s { tcBinding = n })
        te <- inferExpr ctx e
        unify e t te
        solve
      pend <- gets tcPending
      modify' (\s -> s { tcPending = [] })
      pend' <- forM pend $ \(Pending e c) -> Pending e <$> zonkC c
      ts <- mapM zonk vars
      return (Map.union (Map.fromList [ (n, generalise pend' t) | ((n, _), t) <- zip comp ts ]) globals)

-- | Quantify every variable of a type, keeping the undecided constraints
-- that reach it. A constraint reaches the type when it shares a variable with
-- it, or with another constraint that reaches it. The others concern
-- variables no use of the binding can ever instantiate, so they would stay
-- undecided forever; carrying them would copy them into every caller's
-- scheme in turn.
generalise :: [Pending] -> IRType -> Scheme
generalise pend t = Scheme (Set.toList reached) kept t
  where
    vars (Pending _ c) = Set.fromList (constraintVars c)
    reached = grow (Set.fromList (varsOf t))
    grow s = let s' = Set.unions (s : [ vars p | p <- pend, not (Set.disjoint (vars p) s) ])
             in if Set.size s' == Set.size s then s else grow s'
    kept = [ p | p <- pend, not (Set.disjoint (vars p) reached) ]

-- | Every name an expression mentions as a variable (an over-approximation of
-- its free names, which is all the call graph needs).
mentions :: IRExpr -> Set.Set String
mentions (IRVar v) = Set.singleton v
mentions (IRConst v) = valueMentions v
mentions e = Set.unions (map mentions (getIRSubExprs e))

valueMentions :: IRValue -> Set.Set String
valueMentions v = case v of
  VClosure env _ body -> Set.unions (mentions body : map (mentions . snd) env)
  VTuple a b -> valueMentions a `Set.union` valueMentions b
  VEither (Left a) -> valueMentions a
  VEither (Right a) -> valueMentions a
  VList l -> listMentions l
  VTensor _ xs -> Set.unions (map valueMentions xs)
  VADT _ xs -> Set.unions (map valueMentions xs)
  _ -> Set.empty
  where
    listMentions (ListCont x rest) = valueMentions x `Set.union` listMentions rest
    listMentions _ = Set.empty

-- | The globals every environment sees: the implicit functions of its ADTs,
-- the caller's externals, then the standard library checked from its bodies.
baseGlobals :: [ADTDecl] -> [(String, IRType)] -> TC (Map.Map String Scheme)
baseGlobals decls externals = do
  adtFns <- forM (concatMap implicitFunctionRTypes decls) $ \(n, rt) -> do
    ts <- rtypesToIR [rt]
    t <- zonk (head' ts)
    return (n, closedScheme t)
  let ext = Map.fromList [ (n, closedScheme t) | (n, t) <- externals ]
      base = Map.union ext (Map.fromList adtFns)
  modify' (\s -> s { tcBinding = "the standard library" })
  checkBindings decls base standardEnv
  where head' (t : _) = t
        head' [] = ITUnit

initState :: TCState
initState = TCState { tcNext = 0, tcSubst = IM.empty, tcPending = [], tcBinding = "" }

-- | Check an environment, returning the type of every top-level binding (in
-- 'reduceIREnv' order, a name bound twice listed once). The environment may
-- refer to its own bindings, its ADTs' implicit functions and the standard
-- library; anything else is an unbound variable.
checkIREnv :: IREnv -> Either IRTypeError [(String, IRType)]
checkIREnv = checkIREnvWith []

-- | 'checkIREnv' with further globals the environment may refer to, such as
-- neural networks. A variable in an external's type is universally
-- quantified. An external shadows a standard-library name and an ADT
-- function of the same name; a binding of the environment shadows all three.
checkIREnvWith :: [(String, IRType)] -> IREnv -> Either IRTypeError [(String, IRType)]
checkIREnvWith externals env@(IREnv _ decls _) = flip evalStateT initState $ do
  base <- baseGlobals decls externals
  let bindings = reduceIREnv env
  globals <- checkBindings decls base bindings
  return [ (n, t) | n <- nub (map fst bindings), Just (Scheme _ _ t) <- [Map.lookup n globals] ]

-- | The type of one closed expression against the standard library, the
-- given ADTs' implicit functions and the given externals. Constraints still
-- undecided at the end are accepted, as for a top-level binding.
inferIRExpr :: [ADTDecl] -> [(String, IRType)] -> IRExpr -> Either IRTypeError IRType
inferIRExpr decls externals e = flip evalStateT initState $ do
  base <- baseGlobals decls externals
  modify' (\s -> s { tcBinding = "" })
  t <- inferExpr Ctx { ctxGlobals = base, ctxADTs = decls, ctxLocals = Map.empty } e
  solve
  zonk t
