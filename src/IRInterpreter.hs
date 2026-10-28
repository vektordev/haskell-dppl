{-# LANGUAGE RankNTypes #-}

module IRInterpreter (
generateDet,
generateRand,
generateRandE,
generateReplay
) where

import Statistics.Distribution (quantile)
import SPLL.IntermediateRepresentation
import SPLL.IR.Value (elementAt, floatApproxEqThresh, valueInMultiValue)
import StandardLibrary
import SPLL.IR.Neural (NeuralOracle, NeuralPrimitive(..), lookupNeuralPrimitive)

import Control.Monad.Random
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State.Strict (StateT, runStateT, get, put)
import Statistics.Distribution.Normal (normalDistr)
import Data.Number.Erf
import Data.List (isSuffixOf)
import qualified Data.Map.Strict as Map
import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.IR.ADT
import SPLL.IR.Type (IRType(..), IRADTDecl(..))
import Data.Vector.Internal.Check (HasCallStack)

-- | 'AcTheta'/'AcSubtree' index into the theta tree their argument evaluates to.
asThetaTree :: IRValue -> ThetaTree
asThetaTree (VThetaTree t) = t
asThetaTree v = error ("Type error: theta access on a non-theta-tree value: " ++ show v)

-- | The capabilities 'generate' needs from whichever monad it is interpreting
-- in: how to draw randomness, and how to report a program-level failure.
--
-- 'failWith' is what keeps a malformed or partial program from killing the
-- compiler. 'generateDet' runs in @Either String@ and is called from
-- compile-time constant folding ('PredefinedFunctions.propagateValues'), whose
-- caller already handles a 'Left'; an 'error' there is an imprecise exception
-- that walks straight past the 'Either' plumbing and out of the compiler
-- (task compiler-throws-instead-of-returning-left). Every failure in
-- 'generate' therefore goes through 'failWith' or 'raise' rather than through
-- 'error'. In 'generateRand' 'failWith' is still 'error', and only 'raise' --
-- a failure the program itself means -- becomes a 'VError' result; see there.
--
-- Rank-2 so the comparison helpers, which answer in @m Bool@ rather than
-- @m IRValue@, can fail the same way.
data RandomFunctions m a = RandomFunctions
  { uniformGen :: m IRValue
  , normalGen :: m IRValue
  -- 'HasCallStack' so the failing site's own source location still appears
  -- in a 'generateRand' crash; without it every such failure would be
  -- reported at this record's definition site instead.
  , failWith :: forall b. HasCallStack => String -> m b
  -- | A run-time failure of a *well-typed* program: a partial destructor
  -- applied outside its domain (@head []@, @fromLeft (Right x)@). Distinct
  -- from 'failWith', which reports a value of the wrong *shape* reaching an
  -- operation -- that can only mean the compiler or interpreter is
  -- inconsistent, and 'generateRand' keeps it a loud 'error'. 'raise' is the
  -- program's own semantics: 'generateRand' answers it with a 'VError' result,
  -- 'generateDet' with 'Left' like any other failure.
  , raise :: forall b. String -> m b
  }

-- Name, Body ('reduceIREnv', from "SPLL.IntermediateRepresentation").
type ReducedIREnv = [(String, IRExpr)]

-- | The program's top-level names (its functions, the standard library, the
-- neural stubs and every ADT's implicit functions), consulted when a name is
-- not bound locally. They used to sit at the tail of the local environment, so
-- every reference to a global was a linear walk past all of them -- the
-- interpreter's single largest cost in the test suite. A name defined twice
-- keeps its first definition, as 'lookup' on the list did.
type GlobalEnv = Map.Map String IRExpr

globalEnvFrom :: ReducedIREnv -> GlobalEnv
globalEnvFrom = Map.fromListWith (\_new old -> old)

-- | A name's binding: the innermost local one, else the global one.
lookupVar :: String -> GlobalEnv -> ReducedIREnv -> Maybe IRExpr
lookupVar name globals env = case lookup name env of
  Just e  -> Just e
  Nothing -> Map.lookup name globals

-- | Draw one sample. A run-time failure of the sampled program -- @head@ or
-- @tail@ of an empty list, @fromLeft@ of a @Right@: every 'raise' site in
-- 'generate' -- is answered as a 'VError' carrying the message, rather than
-- by a Haskell 'error' (task fuzz-structured-type-bugs, item 1; decision:
-- "VError is fine"). A 'failWith' -- an ill-shaped value, i.e. an
-- interpreter/compiler inconsistency rather than anything the program means --
-- stays an 'error', so that it keeps failing loudly instead of passing for a
-- legitimate run-time failure.
--
-- Such programs are well-typed: @head (tail [x])@ type-checks, because @head@
-- is total in the type system, so nothing upstream rejects them. What they
-- mean at run time is what the emitted backends do with them -- raise -- and
-- a 'VError' is the interpreter's value for that raise. Returning it rather
-- than throwing lets a caller (the CLI, the fuzz properties) observe the
-- failure without catching an imprecise exception.
--
-- The failure short-circuits the rest of the draw, because @ExceptT@ sequences
-- every sub-evaluation. That is deliberate and matches the strict backends: a
-- failing sub-expression fails the program even if a projection would later
-- have discarded it (@fst (1, head [])@), where the lazy @Rand g@ interpreter
-- this replaces returned @1@ by never forcing the bad thunk.
--
-- 'IRError' is unchanged: it is a node the compiler emitted on purpose and
-- 'generate' still throws on it (see there).
generateRand :: (RandomGen g) => NeuralOracle -> IREnv -> [IRExpr]-> IRExpr -> Rand g IRValue
generateRand oracle env params e =
  either VError id <$> runExceptT (generate f oracle adts' (globalEnvFrom startingEnv) [] params e)
  where
    f :: RandomGen g => RandomFunctions (ExceptT String (Rand g)) a
    f = RandomFunctions {
      uniformGen = lift (irSample IRUniform),
      normalGen = lift (irSample IRNormal),
      failWith = error,
      raise = throwError}
    startingEnv = reduceIREnv env ++ standardEnv ++ concatMap implicitFunctionsToEnv adts'
    (IREnv _ adts' _) = env

-- | Like 'generateDet', failures included (every failure is a 'Left'), but with real
-- randomness for 'IRSample'. For a body that is exact apart from deliberate noise -- a
-- writeLogits vector's dead-arm slots (task writelogits-dead-arm-nan) -- where
-- 'generateDet' would refuse the draw and 'generateRand' would throw on a compiler-level
-- failure instead of reporting it.
generateRandE :: (RandomGen g) => NeuralOracle -> IREnv -> [IRExpr] -> IRExpr -> Rand g (Either String IRValue)
generateRandE oracle env params e =
  runExceptT (generate f oracle adts' (globalEnvFrom startingEnv) [] params e)
  where
    f :: RandomGen g => RandomFunctions (ExceptT String (Rand g)) a
    f = RandomFunctions {
      uniformGen = lift (irSample IRUniform),
      normalGen = lift (irSample IRNormal),
      failWith = throwError,
      raise = throwError}
    startingEnv = reduceIREnv env ++ standardEnv ++ concatMap implicitFunctionsToEnv adts'
    (IREnv _ adts' _) = env

-- | Like 'generateDet', but every 'IRSample' takes the next value of a given
-- stream instead of failing: uniforms from the first list, normals from the
-- second. Answers the value and how many draws it took. A run out of either
-- stream is a 'Left' "draw stream exhausted". This replays a backend's own
-- draws through the interpreter (the IR fuzz generator's generate bodies), so
-- a backend's sample can be checked against the interpreter's value under the
-- same randomness, in the interpreter's evaluation order.
generateReplay :: NeuralOracle -> IREnv -> ([Double], [Double]) -> [IRExpr] -> IRExpr -> Either String (IRValue, Int)
generateReplay oracle env (us0, ns0) params e =
  (\(v, (n, _, _)) -> (v, n)) <$> runStateT (generate f oracle adts' (globalEnvFrom startingEnv) [] params e) (0, us0, ns0)
  where
    f :: RandomFunctions (StateT (Int, [Double], [Double]) (Either String)) a
    f = RandomFunctions {
      uniformGen = do
        (n, us, ns) <- get
        case us of
          (u : rest) -> put (n + 1, rest, ns) >> return (VFloat u)
          [] -> throwError "draw stream exhausted",
      normalGen = do
        (n, us, ns) <- get
        case ns of
          (x : rest) -> put (n + 1, us, rest) >> return (VFloat x)
          [] -> throwError "draw stream exhausted",
      failWith = throwError,
      raise = throwError}
    startingEnv = reduceIREnv env ++ standardEnv ++ concatMap implicitFunctionsToEnv adts'
    (IREnv _ adts' _) = env

generateDet :: NeuralOracle -> IREnv -> [IRExpr]-> IRExpr -> Either String IRValue
--generateDet oracle env params e | traceShow e False = undefined
generateDet oracle env = generate f oracle adts' (globalEnvFrom startingEnv) []
  where
    f = RandomFunctions {
      uniformGen = Left "Uniform Gen is not det",
      normalGen = Left "Normal Gen is not det",
      failWith = Left,
      raise = Left}
    startingEnv = reduceIREnv env ++ standardEnv ++ concatMap implicitFunctionsToEnv adts'
    (IREnv _ adts' _) = env

-- | No 'HasCallStack' here, deliberately. With it, every entry allocates one
-- call-stack thunk per recursive call site up front, over 10 KB in all. A heap
-- check that large exceeds a block, and when it fails the RTS extends the
-- nursery instead of collecting. Entry to 'generate' is the interpreter's
-- hottest allocation, so most nursery exhaustion happened there and garbage
-- piled up uncollected: gigabytes in a second of corpus sampling, killed by
-- the OOM killer. 'failWith' keeps its own 'HasCallStack', so a failure still
-- names its site in 'generate'.
generate :: Monad m => RandomFunctions m a -> NeuralOracle -> [IRADTDecl] -> GlobalEnv -> ReducedIREnv -> [IRExpr]-> IRExpr -> m IRValue
--generate f oracle adts' globalEnv env args expr | trace ((show expr) {-++ " " ++ show env-}) False = undefined
generate f oracle adts' globalEnv env args expr | args /= [] = do
  let reverseArgs = reverse args
  let newExpr = foldr (flip IRApply) expr reverseArgs
  generate f oracle adts' globalEnv env [] newExpr
generate _ _ _ _ env [] (IRLambda name expr) = do
  return $ VClosure env name expr
-- A neural primitive ("SPLL.IR.Neural"): a name the oracle binds and no local
-- binding shadows. It takes precedence over a top-level binding of that name.
generate f oracle adts' globalEnv env [] (IRApply (IRVar name) sym)
  | Just prim <- lookupNeuralPrimitive name oracle
  , Nothing <- lookup name env = do
    symVal <- generate f oracle adts' globalEnv env [] sym
    return $ neuralEval prim symVal
generate f oracle adts' globalEnv env [] (IRApply expr val) = do
  exprVal <- generate f oracle adts' globalEnv env [] expr
  valVal <- generate f oracle adts' globalEnv env [] val
  case exprVal of
    (VClosure closEnv name lambda) -> do
      let constClosEnv = (name, IRConst valVal):closEnv
      generate f oracle adts' globalEnv constClosEnv [] lambda
    _ -> failWith f ("Type error: Expression is not a closure: " ++ show exprVal)
generate f oracle adts' globalEnv env args (IRIf cond thenCase elseCase) = do
  condVal <- generate f oracle adts' globalEnv env args cond
  case condVal of
    VBool True -> generate f oracle adts' globalEnv env args thenCase
    VBool False -> generate f oracle adts' globalEnv env args elseCase
    _ -> failWith f $ "Type error: Condition is not a boolean: " ++ show condVal
-- A select lowers to the lazy if under scalar interpretation (design
-- pytorch-tensorizer, M1): only a batched backend distinguishes the two.
generate f oracle adts' globalEnv env args (IRSelect cond thenCase elseCase) =
  generate f oracle adts' globalEnv env args (IRIf cond thenCase elseCase)
generate f oracle adts' globalEnv env [] (IROp OpPlus a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af + bf)
    (VInt af, VInt bf) -> return $ VInt (af + bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> failWith f ("Type error: Plus can only add up numbers (of the same type): " ++ show (aVal, bVal))
generate f oracle adts' globalEnv env [] (IROp OpMult a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af * bf)
    (VInt af, VInt bf) -> return $ VInt (af * bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> failWith f ("Type error: Mult can only multiply numbers (of the same type): " ++ show (aVal, bVal))
generate f oracle adts' globalEnv env [] (IROp OpGreaterThan aOrig bOrig) = do
  aVal <- generate f oracle adts' globalEnv env [] aOrig
  bVal <- generate f oracle adts' globalEnv env [] bOrig
  VBool <$> gt aVal bVal
  -- Answers in the evaluation monad rather than in 'Bool' so its failures
  -- reach 'failWith' like every other program-level failure here.
  where gt a b = case (a, b) of
          (VFloat af, VFloat bf) -> return (af > bf)
          (VInt af, VInt bf) -> return (af > bf)
          (VTuple af1 af2, VTuple bf1 bf2) -> (&&) <$> gt af1 bf1 <*> gt af2 bf2
          (VList (ListCont _ _), VList EmptyList) -> failWith f "When comparing lists, they must be of the same length"
          (VList EmptyList, VList (ListCont _ _)) -> failWith f "When comparing lists, they must be of the same length"
          (VList EmptyList, VList EmptyList) -> return False
          (VList (ListCont aHead aTail), VList (ListCont bHead bTail)) -> (&&) <$> gt aHead bHead <*> gt (VList aTail) (VList bTail)
          _ -> failWith f ("Type error: greater than can only compare two numbers (of the same type): " ++ show (a, b))
generate f oracle adts' globalEnv env [] (IROp OpLessThan aOrig bOrig) = do
  aVal <- generate f oracle adts' globalEnv env [] aOrig
  bVal <- generate f oracle adts' globalEnv env [] bOrig
  VBool <$> lt aVal bVal
  where lt a b = case (a, b) of
          (VFloat af, VFloat bf) -> return (af < bf)
          (VInt af, VInt bf) -> return (af < bf)
          (VTuple af1 af2, VTuple bf1 bf2) -> (&&) <$> lt af1 bf1 <*> lt af2 bf2
          (VList (ListCont _ _), VList EmptyList) -> failWith f "When comparing lists, they must be of the same length"
          (VList EmptyList, VList (ListCont _ _)) -> failWith f "When comparing lists, they must be of the same length"
          (VList EmptyList, VList EmptyList) -> return False
          (VList (ListCont aHead aTail), VList (ListCont bHead bTail)) -> (&&) <$> lt aHead bHead <*> lt (VList aTail) (VList bTail)
          _ -> failWith f ("Type error: less than can only compare two numbers (of the same type): " ++ show (a, b))
generate f oracle adts' globalEnv env [] (IROp OpDiv a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af / bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> failWith f ("Type error: Divide can only divide two numbers (of the same type): " ++ show (aVal, bVal))
-- Exact integer division/remainder (task int-mult-inversion-divides-and-crashes):
-- only ever emitted guarded by an applicability test asserting the modulo is
-- zero first (see PredefinedFunctions.multIInv1/multIInv2), so the rounding
-- direction never matters here.
generate f oracle adts' globalEnv env [] (IROp OpIntDiv a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VInt af, VInt bf) -> return $ VInt (af `div` bf)
    _ -> failWith f ("Type error: IntDiv can only divide two ints: " ++ show (aVal, bVal))
generate f oracle adts' globalEnv env [] (IROp OpMod a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VInt af, VInt bf) -> return $ VInt (af `mod` bf)
    _ -> failWith f ("Type error: Mod can only apply to two ints: " ++ show (aVal, bVal))
generate f oracle adts' globalEnv env [] (IROp OpSub a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (af - bf)
    (VInt af, VInt bf) -> return $ VInt (af - bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> failWith f ("Type error: Minus can only subtract two numbers (of the same type): " ++ show (aVal, bVal))
generate f oracle adts' globalEnv env [] (IROp OpMax a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VFloat (max af bf)
    (VInt af, VInt bf) -> return $ VInt (max af bf)
    _ -> failWith f ("Type error: Max can only compare two numbers (of the same type): " ++ show (aVal, bVal))
generate f oracle adts' globalEnv env [] (IROp OpOr a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VBool af, VBool bf) -> return $ VBool (af || bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> failWith f ("Type error: Or can only evaluate on two booleans: " ++ show (aVal, bVal))
generate f oracle adts' globalEnv env [] (IROp OpAnd a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VBool af, VBool bf) -> return $ VBool (af && bf)
    --(VAny, _) -> return VAny
    --(_, VAny) -> return VAny
    _ -> failWith f ("Type error: Or can only evaluate on two booleans: " ++ show (aVal, bVal))
generate f oracle adts' globalEnv env [] (IROp OpEq a b) = do
  aVal' <- generate f oracle adts' globalEnv env [] a
  bVal' <- generate f oracle adts' globalEnv env [] b
  -- Answers in the evaluation monad rather than in 'Bool' so its fallthrough
  -- reaches 'failWith' like every other program-level failure here.
  let cmp aVal bVal = case (aVal, bVal) of
        (VBool af, VBool bf) -> return (af == bf)
        (VFloat af, VFloat bf) -> return (af == bf)
        (VInt af, VInt bf) -> return (af == bf)
        (VList AnyList, VList _) -> return True
        (VList _, VList AnyList) -> return True
        (VList EmptyList, VList EmptyList) -> return True
        (VList (ListCont VAny as), VList (ListCont _ bs)) -> cmp (VList as) (VList bs)
        (VList (ListCont _ as), VList (ListCont VAny bs)) -> cmp (VList as) (VList bs)
        (VList (ListCont aElem aTail), VList (ListCont bElem bTail)) -> (&&) <$> cmp aElem bElem <*> cmp (VList aTail) (VList bTail)
        (VList _, VList _) -> return False
        -- A field recurses through 'cmp' so an ANY nested inside it (an inner
        -- tuple slot, a list element) still matches; a top-level VAny field is
        -- a wildcard here, as for ADT fields, because 'cmp' itself says
        -- VAny equals nothing.
        (VTuple af1 af2, VTuple bf1 bf2) ->
          let field x y = if x == VAny || y == VAny then return True else cmp x y
          in (&&) <$> field af1 bf1 <*> field af2 bf2
        (VEither (Left _), VEither (Right _)) -> return False
        (VEither (Right _), VEither (Left _)) -> return False
        (VEither (Left VAny), VEither (Left _)) -> return True
        (VEither (Left _), VEither (Left VAny)) -> return True
        (VEither (Right VAny), VEither (Right _)) -> return True
        (VEither (Right _), VEither (Right VAny)) -> return True
        (VEither (Left aElem), VEither (Left bElem)) -> cmp aElem bElem
        (VEither (Right aElem), VEither (Right bElem)) -> cmp aElem bElem
        (VADT n1 vs1, VADT n2 vs2)
          | n1 /= n2 -> return False
          | otherwise -> and <$> mapM (\(v1, v2) -> if v1 == VAny || v2 == VAny then return True else cmp v1 v2) (zip vs1 vs2)
        (VUnit, VUnit) -> return True
        -- Same shape and every element equal, an ANY element a wildcard as a
        -- tuple field's is (task tensor-gaussian-heads-rd-diffusion: a
        -- trajectory's witnessed state is checked against its list slot).
        (VTensor sh1 xs, VTensor sh2 ys)
          | sh1 /= sh2 -> return False
          | otherwise -> and <$> mapM (\(x, y) -> if x == VAny || y == VAny then return True else cmp x y) (zip xs ys)
        -- Any is not equal to anything
        (VAny, _) -> return False
        (_, VAny) -> return False
        _ -> failWith f ("Type error: Equals can only evaluate on two values: " ++ show (aVal, bVal))
  VBool <$> cmp aVal' bVal'
generate f oracle adts' globalEnv env [] (IROp OpApprox a b) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  bVal <- generate f oracle adts' globalEnv env [] b
  case (aVal, bVal) of
    (VFloat af, VFloat bf) -> return $ VBool $ abs (af - bf) <= floatApproxEqThresh
    _ -> failWith f ("Type error: Approx can only evaluate on two floats: " ++ show (aVal, bVal))
generate f oracle adts' globalEnv env [] (IRUnaryOp OpNot a) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  case aVal of
    VBool af -> return $ VBool (not af)
    --VAny -> return VAny
    _ -> failWith f "Type error: Not can only evaluate on a Bool"
generate f oracle adts' globalEnv env [] (IRUnaryOp OpExp a) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  case aVal of
    VFloat af -> return $ VFloat $ exp af
    --VAny -> return VAny
    _ -> failWith f "Type error: Exp can only evaluate on a floating point numbers"
generate f oracle adts' globalEnv env [] (IRUnaryOp OpLog a) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  case aVal of
    VFloat af -> return $ VFloat $ log af
    --VAny -> return VAny
    _ -> failWith f "Type error: Log can only evaluate on a floating point numbers"
generate f oracle adts' globalEnv env [] (IRUnaryOp OpNeg a) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  case aVal of
    VFloat af -> return $ VFloat (-af)
    VInt af -> return $ VInt (-af)
    --VAny -> return VAny
    _ -> failWith f "Type error: Neg can only evaluate on a number"
generate f oracle adts' globalEnv env [] (IRUnaryOp OpSign a) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  case aVal of
    VFloat af | af < 0 -> return $ VFloat (-1)
    VFloat af | af == 0 -> return $ VFloat (0)
    VFloat af | af > 0 -> return $ VFloat (1)
    VInt af | af < 0 -> return $ VInt (-1)
    VInt af | af == 0 -> return $ VInt (0)
    VInt af | af > 0 -> return $ VInt (1)
    --VAny -> return VAny
    _ -> failWith f "Type error: Neg can only evaluate on a number"
generate f oracle adts' globalEnv env [] (IRUnaryOp OpAbs a) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  case aVal of
    VFloat af -> return $ VFloat (abs af)
    VInt af -> return $ VInt (abs af)
    --VAny -> return VAny
    _ -> failWith f "Type error: Abs can only evaluate on a number"
generate f oracle adts' globalEnv env [] (IRUnaryOp OpIsAny a) = do
  aVal <- generate f oracle adts' globalEnv env [] a
  case aVal of
    VAny -> return $ VBool True
    -- The list-shaped hole is an any-value too. Julia's and Python's isAny
    -- both accept it, as does the optimizer's constant fold ('forceAnyCheck'),
    -- so the interpreter answering False here was the one dissent -- and one
    -- that only stayed invisible because the tail accessor happens to hand
    -- back a scalar VAny for a ListCont _ AnyList.
    VList AnyList -> return $ VBool True
    _ -> return $ VBool False
generate f oracle adts' globalEnv env [] (IRDestruct (AcTheta i) a) = do
  tt <- generate f oracle adts' globalEnv env [] a
  let ThetaTree thetas _ = asThetaTree tt
  return $ VFloat (thetas!!i)
generate f oracle adts' globalEnv env [] (IRDestruct (AcSubtree i) a) = do
  tt <- generate f oracle adts' globalEnv env [] a
  let ThetaTree _ subtrees = asThetaTree tt
  return $ VThetaTree (subtrees!!i)
generate _ _ _ _ _ [] (IRConst val) = return val
-- The constructor/accessor family (design ir-reengineering), dispatching on
-- 'ConTag'/'Accessor' -- same value semantics, same 'VClosure' push-through
-- for the tuple projections.
generate f oracle adts' globalEnv env [] (IRConstruct TgTuple [fstExpr, sndExpr]) = do
  fstVal <- generate f oracle adts' globalEnv env [] fstExpr
  sndVal <- generate f oracle adts' globalEnv env [] sndExpr
  return $ VTuple fstVal sndVal
generate f oracle adts' globalEnv env [] (IRConstruct TgCons [hd, tl]) = do
  ls <- generate f oracle adts' globalEnv env [] tl
  case ls of
    VList xs -> do
      x <- generate f oracle adts' globalEnv env [] hd
      return $ VList $ ListCont x xs
    VAny -> do
      x <- generate f oracle adts' globalEnv env [] hd
      return $ VList $ ListCont x AnyList
    _ -> failWith f "Type error: Tail of cons is not a list"
generate f oracle adts' globalEnv env [] (IRConstruct TgLeft [expr]) = do
  x <- generate f oracle adts' globalEnv env [] expr
  return $ VEither (Left x)
generate f oracle adts' globalEnv env [] (IRConstruct TgRight [expr]) = do
  x <- generate f oracle adts' globalEnv env [] expr
  return $ VEither (Right x)
generate f oracle adts' globalEnv env args (IRDestruct AcFst expr) = do
  val <- generate f oracle adts' globalEnv env args expr
  case val of
    VTuple first _ -> return first
    VClosure cEnv n cExpr -> return $ VClosure cEnv n (IRDestruct AcFst cExpr)
    _ -> failWith f ("Type error: Expression of Fst is not a tuple: " ++ show val)
generate f oracle adts' globalEnv env args (IRDestruct AcSnd expr) = do
  val <- generate f oracle adts' globalEnv env args expr
  case val of
    VTuple _ second -> return second
    VClosure cEnv n cExpr -> return $ VClosure cEnv n (IRDestruct AcSnd cExpr)
    _ -> failWith f ("Type error: Expression of Snd is not a tuple: " ++ show val)
generate f oracle adts' globalEnv env args (IRDestruct AcHead listExpr) = do
  listVal <- generate f oracle adts' globalEnv env args listExpr
  case listVal of
    VList (ListCont a _) -> return a
    VList EmptyList -> raise f "head of an empty list"
    _ -> failWith f ("Type error: head must be called on a list: " ++ show listVal)
generate f oracle adts' globalEnv env args (IRDestruct AcTail listExpr) = do
  listVal <- generate f oracle adts' globalEnv env args listExpr
  case listVal of
    VList (ListCont _ AnyList) -> return VAny
    VList (ListCont _ a) -> return $ VList a
    VList EmptyList -> raise f "tail of an empty list"
    _ -> failWith f ("Type error: tail must be called on a list: " ++ show listVal)
generate f oracle adts' globalEnv env args (IRBuiltin BMapList [fExpr, listExpr]) = do
  listVal <- generate f oracle adts' globalEnv env args listExpr
  case listVal of
    VList lst -> do
      newLst <- mapM (\x -> generate f oracle adts' globalEnv env args (IRApply fExpr (IRConst x))) lst
      return $ VList newLst
    _ ->  failWith f "Type error: map must be called on a list"
generate f oracle adts' globalEnv env [] (IRDestruct AcFromLeft expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  case x of
    VEither (Left l) -> return l
    VEither (Right _) -> raise f "fromLeft of a Right"
    _ -> failWith f $ "Type error: fromLeft requires an Either: " ++ show x
generate f oracle adts' globalEnv env [] (IRDestruct AcFromRight expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  case x of
    VEither (Right r) -> return r
    VEither (Left _) -> raise f "fromRight of a Left"
    _ -> failWith f $ "Type error: fromRight requires an Either: " ++ show x
generate f oracle adts' globalEnv env [] (IRDestruct AcIsLeft expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  case x of
    VEither (Left _) -> return (VBool True)
    VEither (Right _) -> return (VBool False)
    _ -> failWith f $ "Type error: isLeft requires an either: " ++ show x
generate f oracle adts' globalEnv env [] (IRDestruct AcIsRight expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  case x of
    VEither (Left _) -> return (VBool False)
    VEither (Right _) -> return (VBool True)
    _ -> failWith f $ "Type error: isLeft requires an either: " ++ show x
generate f oracle adts' globalEnv env [] (IRConformsTo t expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  return $ VBool (valueConformsTo t x)
generate f oracle adts' globalEnv env [] (IRDensity IRUniform Linear expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  return $ irPDF IRUniform x
generate f oracle adts' globalEnv env [] (IRDensity IRNormal Linear expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  return $ irPDF IRNormal x
generate f oracle adts' globalEnv env [] (IRCumulative IRUniform Linear expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  return $ irCDF IRUniform x
generate f oracle adts' globalEnv env [] (IRCumulative IRNormal Linear expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  return $ irCDF IRNormal x
generate f oracle adts' globalEnv env [] (IRDensity dist Log expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  return $ irLogPDF dist x
generate f oracle adts' globalEnv env [] (IRCumulative dist Log expr) = do
  x <- generate f oracle adts' globalEnv env [] expr
  return $ irLogCDF dist x
generate f _ _ _ _ [] (IRSample IRUniform) =
  uniformGen f
generate f _ _ _ _ [] (IRSample IRNormal) =
  normalGen f
-- Let in evaluates the declaration expression to avoid sampling the same term multiple times
generate f oracle adts' globalEnv env args (IRLetIn name decl body) = do
  declVal <- generate f oracle adts' globalEnv env args decl
  let extendedEnv = (name, IRConst declVal):env
  generate f oracle adts' globalEnv extendedEnv args body
-- A neural primitive used as a function value: a closure that applies it.
generate _ oracle _ _ env _ (IRVar name)
  | Just _ <- lookupNeuralPrimitive name oracle
  , Nothing <- lookup name env =
    return $ VClosure [] neuralArg (IRApply (IRVar name) (IRVar neuralArg))
  where neuralArg = name ++ " input"
-- To jump out of the interpreter into the implicit functions implemented in haskell we need to acuire the values of the parameter.
-- This is not possible in normal program flow, because the parameters are applied to the functions before the IRVar call.
-- To solve this we have created an artificial entry in the env table with the original name (E.g. Test) that points to a fresh name (E.g. Test_adt)
-- which is a lambda with a known bound variable. We can now find this variable in the env and have the value of our parameter
generate f oracle adts' globalEnv env args (IRVar name) | "_adt" `isSuffixOf` name && (iterate init name !! 4) `elem` implicitFunctionNames adts' = do
  let realName = iterate init name !! 4
  let lookupParams = sequence [lookupVar ("x" ++ show x) globalEnv env | x <- [0 :: Int .. implicitFunctionArity adts' realName - 1]]
  case lookupParams of
    Nothing -> failWith f ("No parameter found for " ++ name ++ " in environment")
    Just val -> do
      paramVal <- mapM (generate f oracle adts' globalEnv env args) val
      return $ implicitFunctionImpl adts' realName paramVal
generate f oracle adts' globalEnv env args (IRVar name) =
  case lookupVar name globalEnv env of
    Just expr -> generate f oracle adts' globalEnv env args expr
    Nothing -> failWith f ("Variable " ++ name ++ " not declared")
generate f oracle adts' globalEnv env [] (IRIsPossible multiVal expr) = do
  val <- generate f oracle adts' globalEnv env [] expr
  return $ VBool (valueInMultiValue multiVal val)
generate f oracle adts' globalEnv env args (IRBuiltin BListIndex [lstExpr, idxExpr]) = do
  lst <- generate f oracle adts' globalEnv env args lstExpr
  idx <- generate f oracle adts' globalEnv env args idxExpr
  case lst of
    VList l -> case idx of
      VInt i -> return $ l `elementAt` i
      _ -> failWith f "Index must be an integer"
    _ -> failWith f "Expression must be a list"
-- The tensor builtins (design ir-tensor-values). The interpreter is the
-- reference semantics, and it is the one consumer that implements the general
-- rank: a tensor is a shape plus a flat row-major block here, so reducing or
-- indexing along an arbitrary axis is stride arithmetic rather than new
-- machinery. The backends emit rank 1 only; these cases are what pin the
-- layout convention the rest of the compiler is written against.
generate f oracle adts' globalEnv env args (IRBuiltin (BTensor sh) elems) = do
  vals <- mapM (generate f oracle adts' globalEnv env args) elems
  if length vals == shapeNumel sh
    then return $ VTensor sh vals
    else failWith f ("BTensor: shape " ++ show sh ++ " needs " ++ show (shapeNumel sh)
                ++ " elements, got " ++ show (length vals))
-- The flat row-major position of every element, as an integer.
generate _ _ _ _ _ _ (IRBuiltin (BIota sh) []) =
  return $ VTensor sh (map VInt [0 .. shapeNumel sh - 1])
generate f oracle adts' globalEnv env args (IRBuiltin BMap [fExpr, tExpr]) = do
  tVal <- generate f oracle adts' globalEnv env args tExpr
  case tVal of
    VTensor sh xs -> do
      ys <- mapM (\x -> generate f oracle adts' globalEnv env args (IRApply fExpr (IRConst x))) xs
      return $ VTensor sh ys
    _ -> failWith f ("BMap: not a tensor: " ++ show tVal)
-- Reduction folds right within each fibre, matching the association order the
-- retired enum-sum family used (foldrM over the same domain), so the terms of
-- an enumeration are reduced in the same order they always were.
generate f oracle adts' globalEnv env args (IRBuiltin (BReduce op ax) [tExpr]) = do
  tVal <- generate f oracle adts' globalEnv env args tExpr
  case tVal of
    VTensor sh xs -> case fibres ax sh xs of
      Nothing -> failWith f ("BReduce: axis " ++ show ax ++ " out of range for shape " ++ show sh)
      Just (sh', groups) ->
        return $ rewrap sh' (map (foldr (reduceStep op) (reduceIdentity op)) groups)
    _ -> failWith f ("BReduce: not a tensor: " ++ show tVal)
generate f oracle adts' globalEnv env args (IRBuiltin (BIndex ax) [tExpr, keyExpr]) = do
  tVal <- generate f oracle adts' globalEnv env args tExpr
  keyVal <- generate f oracle adts' globalEnv env args keyExpr
  case (tVal, keyVal) of
    (VTensor sh xs, VInt i) -> case fibres ax sh xs of
      Nothing -> failWith f ("BIndex: axis " ++ show ax ++ " out of range for shape " ++ show sh)
      Just (sh', groups)
        | i >= 0 && i < extentSize (sh !! ax) -> return $ rewrap sh' (map (!! i) groups)
        | otherwise -> failWith f ("BIndex: key " ++ show i ++ " out of bounds for axis "
                              ++ show ax ++ " of shape " ++ show sh)
    (VTensor _ _, k) -> failWith f ("BIndex: key must be an integer, got " ++ show k)
    (t, _) -> failWith f ("BIndex: not a tensor: " ++ show t)
-- Elementwise binary op over two tensors of the same shape (task
-- categorical-product-ov-fusion).
--
-- Each pair is combined by recursing on @IROp op (IRConst x) (IRConst y)@
-- rather than by a second scalar-arithmetic implementation here -- the same
-- trick 'BMap' uses for its lambda. That is what makes a zipped multiply
-- *definitionally* the scalar multiply this interpreter already agrees with
-- the three backends on, rather than a copy that has to be kept in step with
-- it (notably for the operands with non-obvious semantics: 'OpApprox's
-- tolerance, 'OpEq' over non-numeric values).
--
-- The shape check is an equality, not a broadcast: 'BZip' deliberately does
-- not broadcast (see the soundness note on 'Builtin'), so unequal shapes are
-- a compiler bug and fail loudly.
generate f oracle adts' globalEnv env args (IRBuiltin (BZip op) [aExpr, bExpr]) = do
  aVal <- generate f oracle adts' globalEnv env args aExpr
  bVal <- generate f oracle adts' globalEnv env args bExpr
  case (aVal, bVal) of
    (VTensor shA xs, VTensor shB ys)
      | shA == shB -> do
          zs <- zipWithM (\x y -> generate f oracle adts' globalEnv env args
                                    (IROp op (IRConst x) (IRConst y))) xs ys
          return $ VTensor shA zs
      | otherwise -> failWith f ("BZip " ++ show op ++ ": shape mismatch, "
                            ++ show shA ++ " against " ++ show shB)
    (VTensor _ _, b) -> failWith f ("BZip: right operand is not a tensor: " ++ show b)
    (a, _) -> failWith f ("BZip: left operand is not a tensor: " ++ show a)
-- Inverse-CDF categorical index (task neural-categorical-sampler-nests-v-deep);
-- the contract is on 'BCategoricalIndex'. The weight vector is whatever
-- 'BListIndex' reads a logit slot out of -- a cons list here -- or a rank-1
-- tensor.
generate f oracle adts' globalEnv env args (IRBuiltin (BCategoricalIndex start n) [uExpr, wExpr]) = do
  uVal <- generate f oracle adts' globalEnv env args uExpr
  wVal <- generate f oracle adts' globalEnv env args wExpr
  u <- case uVal of
    VFloat x -> return x
    other -> failWith f ("BCategoricalIndex: uniform draw is not a float: " ++ show other)
  elems <- case wVal of
    VList l -> return (map (l `elementAt`) [start .. start + n - 1])
    VTensor [_] xs -> return (take n (drop start xs))
    other -> failWith f ("BCategoricalIndex: weights are not a list or rank-1 tensor: " ++ show other)
  ws <- mapM (\w -> case w of
                 VFloat x -> return x
                 other -> failWith f ("BCategoricalIndex: weight is not a float: " ++ show other)) elems
  if length ws /= n || n < 1
    then failWith f ("BCategoricalIndex " ++ show start ++ " " ++ show n
                ++ ": weight vector too short, got " ++ show (length ws) ++ " weights")
    else do
      let target = u * sum ws
          below = length (takeWhile (<= target) (scanl1 (+) ws))
      return (VInt (min (n - 1) below))
generate f _ _ _ _ _ e@(IRBuiltin b args) =
  failWith f ("Malformed tensor builtin" ++ show b ++ " with " ++ show (length args)
         ++ " arguments: " ++ show e)
-- 'IRError' is deliberately left throwing. It is not a compiler-internal
-- failure that escaped a channel -- it is a node the compiler *emitted on
-- purpose* to represent a run-time failure of the user's program (a
-- nonconforming query value, an unanswerable marginal), and the backends
-- render it as a raise. Routing it into 'generateDet's 'Left' would make a
-- data-dependent runtime refusal indistinguishable from a compile-time
-- rejection in @runProb@'s 'Either', which is a distinction several tests in
-- TestInternals/TestRejection exist to keep. Out of scope for task
-- compiler-throws-instead-of-returning-left, which is about compile-time
-- paths.
generate _ _ _ _ _ _ (IRError s) = error $ "Error during interpretation: " ++ s
generate f _ _ _ _ _ expr = failWith f ("Expression is not yet implemented " ++ show expr)


-- | Regroup a flat row-major block into the fibres along one axis: every group
-- is the sequence of elements that differ only in their @ax@ coordinate, in
-- increasing order of it, and the returned shape is the input shape with that
-- axis dropped. Reducing or indexing an axis is then a map over the groups.
--
-- 'Nothing' if the axis is out of range. For the rank-1 case everything today
-- takes, this is one group holding the whole block.
fibres :: Int -> Shape -> [a] -> Maybe (Shape, [[a]])
fibres ax sh xs = do
  sh' <- dropAxis ax sh
  let n     = extentSize (sh !! ax)
      inner = shapeNumel (drop (ax + 1) sh)   -- stride between consecutive ax coordinates
      outer = shapeNumel (take ax sh)
      at o i j = xs !! (((o * n) + i) * inner + j)
  return (sh', [ [ at o i j | i <- [0 .. n - 1] ] | o <- [0 .. outer - 1], j <- [0 .. inner - 1] ])

-- | Rebuild a value from the per-fibre results: a scalar when the remaining
-- shape is empty (rank 0 is not an inhabited tensor), a tensor otherwise.
rewrap :: Shape -> [GenericValue a] -> GenericValue a
rewrap [] [v] = v
rewrap sh vs  = VTensor sh vs

-- | The identity element of a tensor reduction, which is also the result of
-- reducing an empty axis.
reduceIdentity :: ReduceOp -> IRValue
reduceIdentity ROpAdd = VFloat 0
reduceIdentity ROpLogSumExp = VFloat ((-1) / 0)
reduceIdentity ROpMax = VFloat ((-1) / 0)

-- | One step of a tensor reduction. Log-sum-exp guards both infinities, so a
-- -inf term (the log-space zero) is absorbed rather than producing a NaN via
-- @exp (-inf - -inf)@.
reduceStep :: ReduceOp -> IRValue -> IRValue -> IRValue
reduceStep ROpAdd (VFloat a) (VFloat b) = VFloat (a + b)
reduceStep ROpLogSumExp (VFloat a) (VFloat b)
  | isInfinite a && a < 0 = VFloat b
  | isInfinite b && b < 0 = VFloat a
  | otherwise = let m = max a b in VFloat (m + log (exp (a - m) + exp (b - m)))
reduceStep ROpMax (VFloat a) (VFloat b) = VFloat (max a b)
reduceStep op a b =
  error ("BReduce " ++ show op ++ ": non-numeric terms: " ++ show (a, b))

irSample :: (RandomGen g) => Distribution -> Rand g IRValue
irSample IRUniform = do
  r <- getRandomR (0.0, 1.0) --uniformR (0.0, 1.0)
  return $ VFloat r
irSample IRNormal = do
  let gauss = normalDistr 0 1
  r <- getRandomR (0.0, 1.0)
  let result = quantile gauss r
  return $ VFloat $ realToFrac result

irPDF :: Distribution -> IRValue -> IRValue
--irPDF _ VAny = VFloat 1
irPDF IRUniform (VFloat x) = if x >= 0 && x <= 1 then VFloat 1 else VFloat 0
irPDF IRNormal (VFloat x) = VFloat ((1 / sqrt (2 * pi)) * exp (-0.5 * x * x))
irPDF _ x = error ("Expression must be the density of a valid distribution" ++ show x)

irCDF :: Distribution -> IRValue -> IRValue
irCDF IRUniform (VFloat x) = VFloat $ if x < 0 then 0 else if x > 1 then 1 else x
-- erfc rather than 1 + erf, which cancels in the lower tail (task
-- cumulative-normal-upper-tail-cancellation; see Semiring.upperTailComplement).
irCDF IRNormal (VFloat x) = VFloat $ erfc (-x / sqrt 2) / 2
irCDF _ x = error ("Expression must be the CDF of a valid distribution" ++ show x)

-- | Native log-pdf/log-cdf (task log-space-probability-computation): computed
-- directly from the formula rather than as @log (irPDF ...)@, so a deep tail
-- never underflows to a hard float zero (whose log would be -Infinity, losing
-- the tail entirely) before the log is taken.
irLogPDF :: Distribution -> IRValue -> IRValue
irLogPDF IRUniform (VFloat x) = if x >= 0 && x <= 1 then VFloat 0 else VFloat ((-1)/0)
irLogPDF IRNormal (VFloat x) = VFloat ((-0.5) * x * x - 0.5 * log (2 * pi))
irLogPDF _ x = error ("Expression must be the log-density of a valid distribution" ++ show x)

irLogCDF :: Distribution -> IRValue -> IRValue
irLogCDF IRUniform (VFloat x) = VFloat $ log (if x < 0 then 0 else if x > 1 then 1 else x)
irLogCDF IRNormal (VFloat x) = VFloat $ log (erfc (-x / sqrt 2) / 2)
irLogCDF _ x = error ("Expression must be the log-cumulative of a valid distribution" ++ show x)

-- | Structural runtime-tag check backing 'IRConformsTo': does the value match the
-- shape of the given return type? Used to reject wrong-typed query values (e.g.
-- p(0.5) against a Bool-returning program) at the function boundary. Deliberately
-- permissive for types that carry no meaningful runtime tag (type variables,
-- functions, unset) and for marginal-query wildcards (VAny/VAnyExcept), so the
-- guard only ever fires on an unambiguous mismatch.
valueConformsTo :: IRType -> GenericValue a -> Bool
valueConformsTo _ VAny             = True
valueConformsTo _ (VAnyExcept _)   = True
valueConformsTo _ (VError _)       = True
valueConformsTo ITBool      (VBool _)   = True
valueConformsTo ITInt       (VInt _)    = True
valueConformsTo ITSymbol    (VSymbol _) = True
valueConformsTo ITFloat     (VFloat _)  = True
valueConformsTo ITUnit      VUnit       = True
valueConformsTo ITThetaTree (VThetaTree _) = True
valueConformsTo (ITList t)   (VList xs)        = all (valueConformsTo t) (listToValues xs)
valueConformsTo (ITTuple a b)  (VTuple x y)      = valueConformsTo a x && valueConformsTo b y
valueConformsTo (ITEither a _) (VEither (Left x))  = valueConformsTo a x
valueConformsTo (ITEither _ b) (VEither (Right y)) = valueConformsTo b y
-- A tensor conforms only at its exact shape, element by element: a wrongly
-- shaped query is refused rather than answered (design tensors-in-core-language
-- §2.2, item 2).
valueConformsTo (ITTensor sh t) (VTensor sh' xs) = sh == sh' && length xs == shapeNumel sh && all (valueConformsTo t) xs
valueConformsTo (ITADT _)     (VADT _ _)        = True
-- Types with no checkable runtime tag: never reject.
valueConformsTo (ITVar _)       _ = True
valueConformsTo (ITArrow _ _)   _ = True
-- Any remaining concrete-type / value pairing is a genuine mismatch.
valueConformsTo _ _ = False

listToValues :: GenericList a -> [a]
listToValues EmptyList        = []
listToValues AnyList          = []
listToValues (ListCont x rest) = x : listToValues rest


