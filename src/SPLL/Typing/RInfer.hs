
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SPLL.Typing.RInfer (
  RTypeError (..)
, Provenance (..)
, addRTypeInfo
, addRTypeInfoAt
, renderRTypeError
, tryAddRTypeInfo
) where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity

import qualified Data.Set as Set

import Data.Foldable (foldl')
import Data.List (intercalate)
import qualified Data.Map as Map


import SPLL.Lang.Lang
import SPLL.Typing.Typing
import SPLL.Typing.RType
--import SPLL.Typing.PType( PType(..) )
import SPLL.InferenceRule
import PredefinedFunctions (globalFEnv, FPair(..), FDecl(..))
import SPLL.Lang.Types (FnDecl, ADTDecl, CompilerError, GenericValue(..), SourceSpan(..), spanPretty)
import SPLL.Typing.AlgebraicDataTypes
import Data.Bifunctor
import Control.Monad (replicateM)

-- changes: in infer and inferProg; also changed TypeSigs to remove RType of main expression.

-- The typing environment is a plain Data.Map from variable name to its Scheme.
type TEnv = Map.Map Name Scheme

-- | Where a constraint came from, in the user's terms.
--
-- The solver used to carry a 'Maybe String' here that only ever held the name
-- of the inference phase that emitted the constraint (@"Apply"@, @"Constant"@,
-- @"inferResultingType"@) -- true, and of no use to anyone who did not write
-- this module. What a diagnostic needs instead is the *source* each side came
-- from, which is what this records.
data Provenance = Provenance
  { provSpan :: Maybe SourceSpan
  -- | A context chain, innermost first, in the shape of GHC's
  -- @In the expression: ...@ lines.
  , provContext :: [String]
  } deriving (Show, Eq)

-- | Build provenance from the expression that produced a constraint.
provenanceOf :: Expr -> Maybe Provenance
provenanceOf e = Just (Provenance (srcPos (ann e)) [describeExpr e])

-- | Name an expression the way a user would refer to it.
describeExpr :: Expr -> String
describeExpr (Expr _ (InjF (Named n) _)) = "the function '" ++ n ++ "'"
describeExpr (Expr _ (Var n)) = "the variable '" ++ n ++ "'"
describeExpr (Expr _ (Apply _ _)) = "a function application"
describeExpr (Expr _ (Lambda n _)) = "the lambda '\\" ++ n ++ " -> ...'"
describeExpr (Expr _ (Constant _)) = "a literal"
describeExpr (Expr _ (IfThenElse {})) = "an if-then-else"
describeExpr (Expr _ (ReadNN n _)) = "the neural network read 'readNN " ++ n ++ "'"
describeExpr (Expr _ (ThetaI _ i)) = "the parameter 'theta ... @ " ++ show i ++ "'"
describeExpr (Expr _ (Subtree _ i)) = "the subtree 'subtree ... @ " ++ show i ++ "'"

data RTypeError
  = UnificationFail RType RType (Maybe Provenance)
  | InfiniteType TVarR RType
  | UnboundVariable String
  | UnificationMismatch [RType] [RType]
  | ExprInfo [String]
  | FalseParameterFail String
  | ClassConstraintViolation ClassConstraint RType
  | AmbiguousClassConstraint ClassConstraint
  deriving (Show, Eq)

-- | Inference monad
type Infer a = (ReaderT
                  TEnv             -- Typing TEnvironment
                  (StateT         -- Inference state
                  InferState
                  (Except         -- Inference errors
                    RTypeError))
                  a)              -- Result

-- | Inference state
data InferState = InferState { var_count :: Int, collectedClassConstraints :: [ClassConstraint] }

-- | Initial inference state
initInfer :: InferState
initInfer = InferState { var_count = 0, collectedClassConstraints = [] }

data Constraint = Constraint RType RType (Maybe Provenance)
  deriving (Eq, Show)

type Unifier = (Subst, [Constraint])

-- | Constraint solver monad
type Solve a = ExceptT RTypeError Identity a

newtype Subst = Subst (Map.Map TVarR RType)
  deriving (Eq, Show, Monoid, Semigroup)

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVarR

instance Substitutable Program where
  apply s (Program decls nns adtsDecl enc) = Program (zip (map fst decls) (map (apply s . snd) decls)) nns adtsDecl enc
  ftv _ = Set.empty

instance Substitutable Expr where
  apply s = tMap (apply s . getTypeInfo)
  ftv _ = Set.empty

instance Substitutable TypeInfo where
  apply s ti@(TypeInfo {rType=rt}) = setRType ti (apply s rt)
  ftv _ = Set.empty

instance Substitutable RType where
  apply _ TBool = TBool
  apply _ TInt = TInt
  apply _ TSymbol = TSymbol
  apply _ TFloat = TFloat
  apply _ TUnit = TUnit
  apply _ NullList = NullList
  apply _ BottomTuple = BottomTuple
  apply _ TThetaTree = TThetaTree
  apply _ (TADT ty) = TADT ty 
  apply s (ListOf t) = ListOf $ apply s t
  apply s (Tuple t1 t2) = Tuple (apply s t1) (apply s t2)
  apply s (TEither t1 t2) = TEither (apply s t1) (apply s t2)
  apply s (TArrow t1 t2) = apply s t1 `TArrow` apply s t2
  apply (Subst s) t@(TVarR a) = Map.findWithDefault t a s
  apply s (GreaterType t1 t2) = apply s t1 `GreaterType` apply s t2
  apply _ NotSetYet = NotSetYet

  ftv (ListOf t) = ftv t
  ftv (Tuple t1 t2) = Set.union (ftv t1) (ftv t2)
  ftv (TEither t1 t2) = Set.union (ftv t1) (ftv t2)
  ftv (TVarR a)       = Set.singleton a
  ftv (t1 `TArrow` t2) = ftv t1 `Set.union` ftv t2
  ftv (t1 `GreaterType` t2) = ftv t1 `Set.union` ftv t2
  ftv _ = Set.empty

instance Substitutable Scheme where
  apply (Subst s) (Forall as cs t) = Forall as (map (applyCC s') cs) (apply s' t)
                            where s' = Subst $ foldr Map.delete s as
  ftv (Forall as _ t) = ftv t `Set.difference` Set.fromList as

-- Apply a substitution to the TVarR inside a ClassConstraint (rename only).
-- If the substitution maps the TV to a concrete type (not another TVarR), we
-- intentionally leave the constraint with the original TV. checkClassConstraints
-- will apply the final Subst again at check time to resolve the concrete type.
-- Do NOT try to "complete" the check here — that is the check pass's job.
applyCC :: Subst -> ClassConstraint -> ClassConstraint
applyCC (Subst s) cc = case Map.lookup (constraintTV cc) s of
  Just (TVarR tv') -> replaceTV tv' cc
  _                -> cc   -- TV resolved to concrete type or is absent: leave for check pass
  where
    replaceTV tv' (CNum _)        = CNum tv'
    replaceTV tv' (CFractional _) = CFractional tv'
    replaceTV tv' (COrd _)        = COrd tv'
    replaceTV tv' (CEq _)         = CEq tv'
    replaceTV tv' (CDiscrete _)   = CDiscrete tv'

instance Substitutable Constraint where
   apply s (Constraint t1 t2 c) = Constraint (apply s t1) (apply s t2) c
   ftv (Constraint t1 t2 _) = ftv t1 `Set.union` ftv t2

instance Substitutable a => Substitutable [a] where
  apply = map . apply
  ftv   = foldr (Set.union . ftv) Set.empty

showConstraint :: Constraint -> String
showConstraint (Constraint a b Nothing) = prettyRType a ++ " :==: " ++ prettyRType b
showConstraint (Constraint a b (Just c)) =
  prettyRType a ++ " :==: " ++ prettyRType b ++ " (from " ++ intercalate ", " (provContext c) ++ ")"

-- | Render a type error the way GHC renders one: the position, the two types
-- that failed to reconcile, and a context chain of what the user wrote.
--
-- This is deliberately *not* a table of special cases keyed on pairs of types.
-- A rule that recognised, say, an ADT meeting a list and emitted bespoke prose
-- about cons patterns would improve exactly one program shape and would have to
-- be re-derived at the next site. Naming the source instead improves every
-- unification failure in the compiler at once, and lets the reader draw the
-- conclusion -- which is the whole point of task @opaque-user-facing-errors@.
renderRTypeError :: RTypeError -> String
renderRTypeError (UnificationFail t1 t2 prov) =
  unlines (location ++ [header] ++ context)
  where
    location = case prov >>= provSpan of
      Just sp -> [spanPretty sp ++ ":"]
      Nothing -> []
    header = "    Couldn't match type '" ++ prettyRType t1
               ++ "' with '" ++ prettyRType t2 ++ "'"
    -- A node the parser synthesized names the construct it was desugared from,
    -- so the chain never mentions a binder the user never wrote.
    desugarNote = case prov >>= provSpan >>= spanDesugaredFrom of
      Just phrase -> ["      In " ++ phrase]
      Nothing -> []
    context = map ("      In " ++) (maybe [] provContext prov) ++ desugarNote
renderRTypeError e = show e


--build the basic type environment: Take all invertible functions; ignore their inverses
basicTEnv :: [ADTDecl] -> TEnv
basicTEnv adtsDecl = Map.fromList $ (adtRTs ++ injFRTs ++ distRTs)
  where
    adtRTs = map (Data.Bifunctor.second toScheme) (concatMap implicitFunctionRTypes adtsDecl)
    injFRTs = map (\(name, FPair FDecl {contract=ty} _) -> (name, ty)) (globalFEnv adtsDecl)
    -- Distribution primitives are reserved-name Vars bound in the prelude; both draw a Float.
    distRTs = map (Data.Bifunctor.second toScheme) [("Uniform", TFloat), ("Normal", TFloat)]
    -- plain RTypes as they exist in globalFEnv are implicitly forall'd. Make it explicit.
    toScheme :: RType -> Scheme
    toScheme rty = Forall freeVars [] rty
      where
        freeVars :: [TVarR]
        freeVars = Set.toList $ ftv rty


-- | After solving, check that all emitted class constraints are satisfied.
-- For each constraint, resolve the TVarR using the final substitution.
-- A still-free TV after solving means the type is ambiguous.
checkClassConstraints :: Subst -> [ClassConstraint] -> Either RTypeError ()
checkClassConstraints subst cs = mapM_ check cs
  where
    check cc =
      let tv = constraintTV cc
          resolved = apply subst (TVarR tv)
      in case resolved of
           TVarR _ -> Right ()  -- still free = genuinely polymorphic, constraint is deferred
           t       -> if satisfiesClass cc t
                      then Right ()
                      else Left $ ClassConstraintViolation cc t

addRTypeInfo :: Program -> Either CompilerError Program
addRTypeInfo = addRTypeInfoAt 0

-- | 'addRTypeInfo', with the solver dump gated on verbosity.
--
-- The dump -- the pretty-printed program, every constraint, and the leftover
-- constraints after simplification -- used to be appended to *every* type
-- error: 88 lines of solver internals for a five-line program, none of it
-- meaningful to a user. It is a real debugging aid for someone working on this
-- module, so it is kept and moved behind @-v@ rather than deleted.
addRTypeInfoAt :: Int -> Program -> Either CompilerError Program
addRTypeInfoAt verbosity p =
  case runInfer (basicTEnv (adts p)) (inferProg p) of
    Left err -> Left (renderRTypeError err)
    Right (cs, classCs, p2) -> case runSolve cs of
      Left err -> Left (renderRTypeError err ++ dump)
          where
            (subst, leftoverConstraints) = simplify (emptySubst, cs)
            dump
              | verbosity < 1 = ""
              | otherwise =
                  "\nprog = \n" ++ (unlines $ prettyPrintProgRTyOnly p2)
                  ++ "\n\nconstraints = \n" ++ (unlines $ map showConstraint cs)
                  ++ "\n\nsimplified prog = \n" ++ (unlines $ prettyPrintProgRTyOnly (subst `apply` p2))
                  ++ "\n\nleftover constraints = \n" ++ (unlines $ map showConstraint leftoverConstraints)
      Right subst -> case checkClassConstraints subst classCs of
        Left err -> Left ("Class constraint violation: " ++ renderRTypeError err)
        Right () -> Right (apply subst p2)

tryAddRTypeInfo :: Program -> Either RTypeError Program
tryAddRTypeInfo p@(Program _ _ adtsDecl _) = do
  (cs, classCs, prog) <- runInfer (basicTEnv adtsDecl) (inferProg p)
  subst <- runSolve cs
  checkClassConstraints subst classCs
  return $ apply subst prog

rtFromScheme :: Scheme -> RType
rtFromScheme (Forall _ _ rt) = rt

--TODO: Simply give everything a fresh var as a unified first pass.
inferProg :: Program -> Infer ([Constraint], Program)
inferProg p = do
  Program decls nns adtsDecl enc <- addTVarsEverywhere p

  -- init type variable for all function decls beforehand so we can build constraints for
  -- calls between these functions
  tv_rev <- freshVars (length decls) []
  let tvs = reverse tv_rev
  -- build env from neurals
  let neurals_tvs = map (\(a, b, _) -> (a, Forall [] [] b)) (neurals p)
  -- env building with (name, scheme) for infer methods
  let func_tvs = zip (map fst decls) (map (Forall [] []) tvs)
  let typeEnv = func_tvs ++ neurals_tvs
  -- infer the type and constraints of the declaration expressions
  cts <- mapM ((inTEnvF typeEnv . infer adtsDecl) . snd) decls
  -- building the constraints that the built type variables of the functions equal
  -- the inferred function type
  let tcs = zipWith (\t1 t2 -> Constraint t1 t2 Nothing) (map (rtFromScheme . snd) func_tvs) (map fst3cts cts)
  -- combine all constraints
  return (tcs ++ concatMap snd3cts cts, Program (zip (map fst decls) (map trd3cts cts)) nns adtsDecl enc)

addTVarsEverywhere :: Program -> Infer Program
addTVarsEverywhere (Program decls nns adtsDecl enc) = do
    newdecls <- mapM addTVarsToDecl decls
    return (Program newdecls nns adtsDecl enc)
  where
    addTVarsToDecl :: FnDecl -> Infer FnDecl
    addTVarsToDecl (name, expr) = do
      e2 <- tMapM replaceIfUnset expr
      return (name, e2)
    replaceIfUnset :: Expr -> Infer TypeInfo
    replaceIfUnset expr = case rType $ getTypeInfo expr  of
      NotSetYet -> do
        tvar <- fresh
        return $ setRType (getTypeInfo expr) tvar
      _ -> return $ getTypeInfo expr

specialTreatment :: Expr -> Bool
specialTreatment e = toStub e `elem` [StubConstant, StubLambda, StubVar, StubApply, StubInjF, StubReadNN]

--TODO: Error on ambiguous InferenceRule
infer :: [ADTDecl] ->  Expr -> Infer (RType, [Constraint], Expr)
--infer expr | trace (show expr ++ show (specialTreatment expr) ++ show (solvesSimply expr)) False = undefined
infer adtsDecl expr
    | specialTreatment expr =
      --we're dealing with StubConstant here.
      case expr of
        (Expr ty (Constant (VError msg))) -> do
          -- An error can occur in place of any type, so its type is unconstrained.
          tVal <- fresh
          let constraint = Constraint (rType ty) tVal (provenanceOf expr)
          return (rType ty, [constraint], Expr ty (Constant (VError msg)))
        (Expr ty (Constant val)) -> do
          let tVal = getRType val
          let constraint = Constraint (rType ty) tVal (provenanceOf expr)
          return (rType ty, [constraint], expr)
        (Expr ti (Lambda name inExpr)) -> do
          -- rare case of needing an extra TV, because the var doesn't get one initially
          tv <- fresh
          -- give the lambda var a tv, with that TEnv infer the lambda expression
          (functionTy, cs, inExprTy) <- inTEnvF [(name, Forall [] [] tv)] (infer adtsDecl inExpr)
          -- resulting type is tv -> functionTy; propagate constraints from inner Expr.
          return (tv `TArrow` functionTy, cs, Expr (setRType ti (tv `TArrow` functionTy)) (Lambda name inExprTy))
        (Expr ti (Var name)) -> do
          t <- lookupTEnv name
          return (t, [], Expr (setRType ti t) (Var name))
        (Expr ti (Apply func arg)) -> do
          (funcTy, c1, funcExprTy) <- infer adtsDecl func
          (argTy, c2, argExprTy) <- infer adtsDecl arg
          let argConstraint = Constraint funcTy (argTy `TArrow` (rType ti)) (provenanceOf expr)
          return (rType ti, [argConstraint] ++ c1 ++ c2, Expr ti (Apply funcExprTy argExprTy))
          --expr `usingScheme` (Forall [TV "a", TV "b"] (((TVarR $ TV "a") `TArrow` (TVarR $ TV "b")) `TArrow` (TVarR $ TV "a") `TArrow` (TVarR $ TV "b")))
        e@(Expr _ (InjF (Named name) _)) ->
          case lookup name (globalFEnv adtsDecl) of
            Just (FPair FDecl {contract=scheme} _) -> usingScheme adtsDecl e scheme
            Nothing -> throwError $ UnboundVariable ("InjF " ++ name)
        (Expr ti (ReadNN name sym)) -> do
          t <- lookupTEnv name
          (symTy, c1, symTyExpr) <- infer adtsDecl sym
          let argConstraint = Constraint t (symTy `TArrow` (rType ti)) (provenanceOf expr)
          return (rType ti, [argConstraint] ++ c1, Expr ti (ReadNN name symTyExpr))
        -- 'specialTreatment' is the guard on this branch; the two must list the
        -- same stubs, so a node reaching here means one of them was extended
        -- without the other.
        e -> error ("infer: " ++ show (toStub e) ++ " passes specialTreatment but has no case in it")
    | solvesSimply expr =
        let
          plausibleAlgs = filter (checkExprMatches expr) allAlgorithms
          --since we don't care about ambiguous inference rules (i.e. multiple plausible rules)
          -- we just make sure that they agree on resulting types.
          allSchemesEq = all (\alg -> assumedRType (head plausibleAlgs) == assumedRType alg) (tail plausibleAlgs)
          scheme = assumedRType (head plausibleAlgs)
        in
          if not allSchemesEq
            then error ("unviable Inference Rule configuration" ++ (show $ map algName plausibleAlgs))
            else
              -- use ForAll scheme from InferenceRule.
              usingScheme adtsDecl expr scheme
    | otherwise = error ("no inference implemented for " ++ show expr)

usingScheme :: [ADTDecl] ->  Expr -> Scheme -> Infer (RType, [Constraint], Expr)
usingScheme adtsDecl expr scheme = do
  -- use ForAll scheme from InferenceRule.
  let subexprs = getSubExprs expr
  tuples <- mapM (infer adtsDecl) subexprs
  let localConstraints = concatMap snd3cts tuples
  let subExprTypes = map fst3cts tuples
  let typedSubExprs = map trd3cts tuples
  rescoped <- rescope scheme
  (resultingtype, recursiveConstraints) <- inferResultingType (provenanceOf expr) rescoped subExprTypes
  return (resultingtype, recursiveConstraints ++ localConstraints, reformExpr expr typedSubExprs resultingtype)

solvesSimply :: Expr -> Bool
solvesSimply e = (not (null plausibleAlgs)) && (not ((toStub e) == StubConstant))
  where
    plausibleAlgs = filter (checkExprMatches e) allAlgorithms

--put all new TVars into a scheme
--TODO: could probably be reduced to instantiate, depending on context.
rescope :: Scheme -> Infer Scheme
rescope (Forall tvars cs rty) = do
  newTVars <- mapM (const fresh) tvars
  let newvars = map unwrap newTVars
  let substitution = Subst $ Map.fromList (zip tvars newTVars)
  let substituted = apply substitution rty
  let renamedCs = map (applyCC substitution) cs
  -- Emit class constraints so they can be checked post-solve
  modify (\s -> s { collectedClassConstraints = renamedCs ++ collectedClassConstraints s })
  return (Forall newvars renamedCs substituted)
    where unwrap (TVarR tv) = tv
          -- 'fresh' only ever yields a type variable.
          unwrap t = error ("rescope: fresh produced " ++ show t ++ ", not a type variable")

-- instantiate a Scheme: Substitute each ForAll'd TV with a fresh var.
instantiate :: Scheme -> Infer RType
instantiate (Forall as cs t) = do
    as2 <- mapM (const fresh) as
    let s = Subst $ Map.fromList $ zip as as2
    -- Emit renamed class constraints so they can be checked post-solve
    let renamedCs = map (applyCC s) cs
    modify (\s' -> s' { collectedClassConstraints = renamedCs ++ collectedClassConstraints s' })
    return $ apply s t

-- into an existing expression, replace a subexpresison and rtype.
reformExpr :: Expr -> [Expr] -> RType -> Expr
reformExpr original subexprs ownTy = tMapHead (const newTy) $ setSubExprs original subexprs
  where
    newTy = setRType (getTypeInfo original) ownTy

--take a scheme like Forall [a,b,c] (a -> b -> c) and apply a list of types Int, Float to the scheme.
-- should yield (c, [a=Int, b=Float])
inferResultingType :: Maybe Provenance -> Scheme -> [RType] -> Infer (RType, [Constraint])
inferResultingType _ (Forall _ _ rtype) [] = return (rtype, [])
inferResultingType prov (Forall vars _ (TArrow fromTy toTy)) (fstTy:rtypes2) =
  do
    let constraint = Constraint fromTy fstTy prov
    -- Class constraints (cs) are emitted by rescope before inferResultingType runs;
    -- the recursive Scheme here is for type application only, not re-emission.
    (resultingType, moreConstraints) <- inferResultingType prov (Forall vars [] toTy) rtypes2
    return (resultingType, constraint:moreConstraints)
inferResultingType prov (Forall vars _ fTy) (fstTy:rtypes2) = do
  --introduce a new TV for the result.
  resultingTV <- fresh
  let constraint = Constraint fTy (fstTy `TArrow` (resultingTV)) prov
  -- Class constraints (cs) are emitted by rescope before inferResultingType runs;
  -- the recursive Scheme here is for type application only, not re-emission.
  (resultingType, moreConstraints) <- inferResultingType prov (Forall vars [] resultingTV) rtypes2
  return (resultingType, constraint:moreConstraints)
--inferResultingType a b = error ("undefined inferResulting from " ++ show a ++ " //// " ++ show b)


-- | Extend type TEnvironment
inTEnvF :: [(Name, Scheme)] -> Infer a -> Infer a
inTEnvF bindings m = local (\env -> foldl' (\e (x, sc) -> Map.insert x sc e) env bindings) m

-- | Lookup type in the TEnvironment
lookupTEnv :: Name -> Infer RType
lookupTEnv x = do
  env <- ask
  case Map.lookup x env of
      Nothing   ->  throwError $ UnboundVariable x
      Just s    ->  do t <- instantiate s
                       return t

fst3cts ::  (RType, [Constraint], Expr) -> RType
fst3cts (t, _, _) = t
snd3cts ::  (RType, [Constraint], Expr) -> [Constraint]
snd3cts (_, cts, _) = cts
trd3cts ::  (RType, [Constraint], Expr) -> Expr
trd3cts (_, _, e) = e

-------------------------------------------------------------------------------
-- Type Variable management
-------------------------------------------------------------------------------
letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer RType
fresh = do
    s <- get
    put s{var_count = var_count s + 1}
    return $ TVarR $ TV (letters !! var_count s)

freshVars :: Int -> [RType] -> Infer [RType]
freshVars 0 rts = do
    return rts
freshVars n rts = do
    s <- get
    put s{var_count = var_count s + 1}
    freshVars (n - 1)  (TVarR (TV (letters !! var_count s)):rts)


-- | Run the inference monad
runInfer :: TEnv -> Infer ([Constraint], Program) -> Either RTypeError ([Constraint], [ClassConstraint], Program)
runInfer env m = runExcept $ do
  (result, finalState) <- runStateT (runReaderT m env) initInfer
  let (cs, prog) = result
  return (cs, collectedClassConstraints finalState, prog)


-------------------------------------------------------------------------------
-- Constraint Solver
-------------------------------------------------------------------------------

-- | The empty substitution
emptySubst :: Subst
emptySubst = mempty

-- | Compose substitutions
compose :: Subst -> Subst -> Subst
(Subst s1) `compose` (Subst s2) = Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1

-- | Run the constraint solver
runSolve :: [Constraint] -> Either RTypeError Subst
runSolve cs = runIdentity $ runExceptT $ solver st
  where st = (emptySubst, cs)

-- same logic as a constraint solver,
-- except it skips but records all failing constraints
-- and produces a somewhat-informative substitution
simplify :: Unifier -> Unifier
simplify (su, []) = (su, [])
simplify (su, ((Constraint t1 t2 c): cs0)) =
  case runIdentity $ runExceptT $ unifies c t1 t2 of
    -- can't simplify the t1, t2 constraint, put it in the unusable bin.
    Left _ -> addLeftoverConstraint (simplify (su, cs0)) (Constraint t1 t2 c)
    Right newSubst -> simplify (newSubst `compose` su, apply newSubst cs0)
  where
    addLeftoverConstraint :: Unifier -> Constraint -> Unifier
    addLeftoverConstraint (suDecl, cs) cs2 = (suDecl, cs2:cs)

-- Unification solver
solver :: Unifier -> Solve Subst
solver (su, cs) =
  case cs of
    [] -> return su
    ((Constraint t1 t2 prov): cs0) -> do
      su1  <- unifies prov t1 t2
      solver (su1 `compose` su, apply su1 cs0)

-- The 'Maybe Provenance' is carried purely so that a failure can say where the
-- constraint came from; it takes no part in unification itself.
unifies :: Maybe Provenance -> RType -> RType -> Solve Subst
unifies _ t1 t2 | t1 `matches` t2 = return emptySubst
unifies _ (Tuple _ _) BottomTuple = return emptySubst
unifies _ BottomTuple (Tuple _ _) = return emptySubst
unifies _ (ListOf _) NullList = return emptySubst
unifies _ NullList (ListOf _) = return emptySubst
unifies p (ListOf t1) (ListOf t2) = unifies p t1 t2
unifies p t1 (GreaterType (TVarR v) t3) = if t1 `matches` t3 then v `bind` t1 else
  throwError $ UnificationFail t1 t3 p
unifies p t1 (GreaterType t3 (TVarR v)) = if t1 `matches` t3 then v `bind` t1 else
  throwError $ UnificationFail t1 t3 p
unifies p (TVarR v) (GreaterType t2 t3) = case greaterType t2 t3 of
  Nothing -> throwError $ UnificationFail t2 t3 p
  Just t -> v `bind` t
unifies p t1 (GreaterType t2 t3) = if t1 `matches` t2 && t2 `matches` t3 then return emptySubst else
  (case greaterType t2 t3 of
    Nothing -> throwError $ UnificationFail t1 (GreaterType t2 t3) p
    Just tt -> if t1 `matches` tt then return emptySubst else throwError $  UnificationFail t1 (GreaterType t2 t3) p)
unifies _ (TVarR v) t = v `bind` t
unifies _ t (TVarR v) = v `bind` t
unifies p (TArrow t1 t2) (TArrow t3 t4) = unifyMany p [t1, t2] [t3, t4]
unifies p (Tuple t1 t2) (Tuple t3 t4) = unifyMany p [t1, t2] [t3, t4]
unifies p (TEither t1 t2) (TEither t3 t4) = unifyMany p [t1, t2] [t3, t4]
unifies p t1 t2 = throwError $ UnificationFail t1 t2 p

unifyMany :: Maybe Provenance -> [RType] -> [RType] -> Solve Subst
unifyMany _ [] [] = return emptySubst
unifyMany p (t1 : ts1) (t2 : ts2) =
  do su1 <- unifies p t1 t2
     su2 <- unifyMany p (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1)
unifyMany _ t1 t2 = throwError $ UnificationMismatch t1 t2

bind ::  TVarR -> RType -> Solve Subst
bind a t | t `matches` TVarR a = return emptySubst
         | occursCheck a t     = throwError $ InfiniteType a t
         | otherwise           = return (Subst $ Map.singleton a t)

occursCheck ::  Substitutable a => TVarR -> a -> Bool
occursCheck a t = a `Set.member` ftv t
