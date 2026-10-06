-- | Monomorphization of genuinely polymorphic top-level functions
-- (design @polymorphic-monomorphization@).
--
-- Every pass after 'SPLL.Typing.RInfer' assumes one declaration has one
-- concrete type: IRCompiler dispatches @plus@ to @plusI@ on the node's
-- 'rType', and an inversion contract is type-specific. A function used at two
-- numeric types -- @addTwice x = x + x@ called on a @Float@ and on an @Int@ --
-- therefore has to become two declarations before those passes see it.
--
-- This module does the cloning. Its input is the result of let-generalising
-- inference (@RInfer@'s fallback path): each declaration's 'Scheme' and its
-- typed body, in which every reference to a polymorphic declaration carries
-- the instantiated type of that one use. Its output is an ordinary,
-- *untyped* program with one declaration per instantiation and every
-- reference renamed to the instance it uses -- which the existing
-- monomorphic inference then types like any other program.
--
-- Naming. A monomorphic declaration keeps its name. A polymorphic one keeps
-- its name for its generic instance (emitted when nothing else instantiates
-- it, exactly as before this pass existed, or when a generic body uses it) or
-- for its sole instance. Every other instance is named by 'mangleName'
-- (@addTwice__int@) -- so a function used at two concrete types becomes two
-- mangled declarations and no longer exists under its own name, rather than
-- one of the two types arbitrarily inheriting it.
module SPLL.Typing.Monomorphize
  ( monomorphize
  , mangleName
  , mangleRType
  ) where

import Control.Monad (unless)
import Control.Monad.State (StateT, evalStateT, get, put, lift)
import Data.Foldable (toList)
import Data.List (intercalate, nub)
import qualified Data.Map as Map
import qualified Data.Set as Set

import SPLL.Lang.Types (Expr(..), ExprF(..), Program(..), TypeInfo(..))
import SPLL.Typing.RType (RType(..), TVarR(..), Scheme(..), extentSize)

-- | An instance: a declaration name and the (canonicalised) types its scheme
-- variables are instantiated at. A monomorphic declaration has no arguments.
type Key = (String, [RType])

-- | @monomorphize prog typed@ clones @prog@'s polymorphic declarations, one
-- per instantiation reachable from a monomorphic declaration (or from a
-- generic instance kept because nothing instantiated it).
--
-- @typed@ maps each declaration name to its generalised scheme and its typed
-- body; the typed body must have the same shape as the untyped one in @prog@
-- (inference only sets annotations). A 'Left' is an internal inconsistency,
-- never a user error.
monomorphize :: Program -> Map.Map String (Scheme, Expr) -> Either String Program
monomorphize prog typed = do
  instances <- reachable
  let byDecl = Map.fromListWith (flip (++)) [ (n, [args]) | (n, args) <- Set.toList instances ]
      names = assignNames byDecl
  newDecls <- concat <$> mapM (emit byDecl names) (functions prog)
  return prog { functions = newDecls }
  where
    decls = functions prog
    declNames = map fst decls

    schemeOf n = fst <$> Map.lookup n typed

    isPoly n = case schemeOf n of
      Just (Forall (_:_) _ _) -> True
      _ -> False

    -- Which instances are used. Roots are the monomorphic declarations; a
    -- polymorphic declaration nothing instantiates is then added as its
    -- generic instance (it stays in the program as it always did), which may
    -- in turn reach further instances.
    reachable :: Either String (Set.Set Key)
    reachable = do
      let roots = [ (n, []) | n <- declNames, not (isPoly n) ]
      closeOver Set.empty roots
      where
        closeOver seen [] = do
          let uninstantiated = [ n | n <- declNames, isPoly n
                                   , not (any ((== n) . fst) (Set.toList seen)) ]
          case uninstantiated of
            [] -> return seen
            (n:_) -> closeOver seen [genericKey n]
        closeOver seen (k:ks)
          | k `Set.member` seen = closeOver seen ks
          | otherwise = do
              refs <- instanceRefs k
              closeOver (Set.insert k seen) (refs ++ ks)

    genericKey n = case schemeOf n of
      Just (Forall vs _ _) -> (n, canonical (map TVarR vs))
      Nothing -> (n, [])

    -- The polymorphic references in one instance's body, as instance keys.
    instanceRefs :: Key -> Either String [Key]
    instanceRefs k = do
      (sigma, body) <- instanceBody k
      collect sigma Set.empty body
      where
        collect sigma bound (Expr ti e) = case e of
          Var v | refersToPoly bound v -> (: []) <$> refKey sigma v ti
          Lambda x b -> collect sigma (Set.insert x bound) b
          _ -> concat <$> mapM (collect sigma bound) (toList e)

    refersToPoly bound v = not (v `Set.member` bound) && isPoly v

    -- The substitution an instance applies to its declaration's typed body.
    instanceBody :: Key -> Either String (Map.Map TVarR RType, Expr)
    instanceBody (n, args) = case Map.lookup n typed of
      Nothing -> Left ("monomorphize: no typed body for " ++ n)
      Just (Forall vs _ _, body)
        | length vs == length args -> Right (Map.fromList (zip vs args), body)
        | otherwise -> Left ("monomorphize: arity mismatch instantiating " ++ n)

    -- The instance a reference to polymorphic @v@ selects: its scheme's type
    -- matched against the reference's own (instantiated, then substituted)
    -- type.
    refKey :: Map.Map TVarR RType -> String -> TypeInfo -> Either String Key
    refKey sigma v ti = case schemeOf v of
      Just (Forall vs _ pat) -> do
        m <- maybe (Left ("monomorphize: reference to " ++ v ++ " at " ++ show refTy
                          ++ " does not instantiate its scheme " ++ show pat))
                   Right (matchRType pat refTy Map.empty)
        return (v, canonical [ Map.findWithDefault (TVarR tv) tv m | tv <- vs ])
      Nothing -> Left ("monomorphize: no scheme for " ++ v)
      where refTy = substRType sigma (rType ti)

    assignNames :: Map.Map String [[RType]] -> Map.Map Key String
    assignNames byDecl = snd (foldl assign (Set.fromList declNames, Map.empty) (Map.toList byDecl))
      where
        assign (taken, acc) (n, argss)
          | not (isPoly n) = (taken, Map.insert (n, []) n acc)
          | otherwise =
              let generic = snd (genericKey n)
                  keeper = case argss of
                    _ | generic `elem` argss -> Just generic
                    [only] -> Just only
                    _ -> Nothing
                  others = filter ((/= keeper) . Just) argss
                  (taken', named) = foldl (\(t, ns) as ->
                                             let nm = fresh t (mangleName n as)
                                             in (Set.insert nm t, (as, nm) : ns))
                                          (taken, []) others
                  acc' = maybe acc (\k -> Map.insert (n, k) n acc) keeper
              in (taken', foldr (\(as, nm) -> Map.insert (n, as) nm) acc' named)
        fresh t nm | nm `Set.member` t = fresh t (nm ++ "_")
                   | otherwise = nm

    -- The declarations one source declaration becomes.
    emit :: Map.Map String [[RType]] -> Map.Map Key String -> (String, Expr) -> Either String [(String, Expr)]
    emit byDecl names (n, src) =
      mapM one (Map.findWithDefault [] n byDecl)
      where
        one args = do
          (sigma, body) <- instanceBody (n, args)
          nm <- lookupName (n, args)
          src' <- rename sigma src body
          return (nm, src')
        lookupName k = maybe (Left ("monomorphize: unnamed instance " ++ show k)) Right (Map.lookup k names)
        -- Walk the untyped source and the typed body in lockstep, renaming
        -- each polymorphic reference to the instance it selects.
        rename sigma = go Set.empty
          where
            go bound (Expr si se) (Expr ti te) = case (se, te) of
              (Var v, Var v') | v == v' && refersToPoly bound v -> do
                k <- refKey sigma v ti
                nm <- lookupName k
                return (Expr si (Var nm))
              (Lambda x b, Lambda x' b') | x == x' -> Expr si . Lambda x <$> go (Set.insert x bound) b b'
              _ -> do
                let tcs = toList te
                unless (length tcs == length (toList se) && sameShape se te) $
                  Left ("monomorphize: typed body does not match source at " ++ show (fmap (const ()) se))
                Expr si <$> evalStateT (traverse (step bound) se) tcs
            step :: Set.Set String -> Expr -> StateT [Expr] (Either String) Expr
            step bound c = do
              ts <- get
              case ts of
                (t:rest) -> put rest >> lift (go bound c t)
                [] -> lift (Left "monomorphize: typed body has too few children")

    -- Same constructor with the same payload (a constant, a name); the
    -- children are compared by the recursion.
    sameShape a b = fmap (const ()) a == fmap (const ()) b

-- | The name of a declaration's instance at the given argument types:
-- @addTwice@ at @[Int]@ is @addTwice__int@. The type rendering is a prefix
-- (Polish) encoding over fixed-arity tokens, so it is unambiguous, and uses
-- only identifier characters, so it is valid in Python and Julia alike.
mangleName :: String -> [RType] -> String
mangleName n args = n ++ "__" ++ intercalate "_" (map mangleRType args)

mangleRType :: RType -> String
mangleRType t = case t of
  TBool -> "bool"
  TInt -> "int"
  TSymbol -> "symbol"
  TFloat -> "float"
  TUnit -> "unit"
  TThetaTree -> "thetatree"
  ListOf a -> "list_" ++ mangleRType a
  Tuple a b -> "tuple_" ++ mangleRType a ++ "_" ++ mangleRType b
  TEither a b -> "either_" ++ mangleRType a ++ "_" ++ mangleRType b
  -- the shape is one segment (@3x4@, no underscore), so the prefix encoding stays
  -- fixed-arity: @tensor3x4_float@
  TTensor sh e -> "tensor" ++ intercalate "x" (map (show . extentSize) sh) ++ "_" ++ mangleRType e
  TADT name -> name
  NullList -> "nulllist"
  BottomTuple -> "bottomtuple"
  TArrow a b -> "fn_" ++ mangleRType a ++ "_" ++ mangleRType b
  TVarR (TV v) -> v
  GreaterType a b -> "gt_" ++ mangleRType a ++ "_" ++ mangleRType b
  NotSetYet -> "unset"

-- | Rename the type variables of an argument list to @t0, t1, ...@ in order
-- of first appearance, so that two instantiations differing only in the names
-- of their leftover variables are one instance.
canonical :: [RType] -> [RType]
canonical args = map (substRType ren) args
  where
    vars = nub (concatMap tvarsOf args)
    ren = Map.fromList (zipWith (\v i -> (v, TVarR (TV ("t" ++ show (i :: Int))))) vars [0 ..])

tvarsOf :: RType -> [TVarR]
tvarsOf t = case t of
  TVarR v -> [v]
  ListOf a -> tvarsOf a
  Tuple a b -> tvarsOf a ++ tvarsOf b
  TEither a b -> tvarsOf a ++ tvarsOf b
  TTensor _ e -> tvarsOf e
  TArrow a b -> tvarsOf a ++ tvarsOf b
  GreaterType a b -> tvarsOf a ++ tvarsOf b
  _ -> []

substRType :: Map.Map TVarR RType -> RType -> RType
substRType s t = case t of
  TVarR v -> Map.findWithDefault t v s
  ListOf a -> ListOf (substRType s a)
  Tuple a b -> Tuple (substRType s a) (substRType s b)
  TEither a b -> TEither (substRType s a) (substRType s b)
  TTensor sh e -> TTensor sh (substRType s e)
  TArrow a b -> TArrow (substRType s a) (substRType s b)
  GreaterType a b -> GreaterType (substRType s a) (substRType s b)
  _ -> t

-- | One-way matching: the substitution of the pattern's variables that makes
-- it equal to the target, if one exists.
matchRType :: RType -> RType -> Map.Map TVarR RType -> Maybe (Map.Map TVarR RType)
matchRType pat target m = case (pat, target) of
  (TVarR v, _) -> case Map.lookup v m of
    Nothing -> Just (Map.insert v target m)
    Just prev | prev == target -> Just m
              | otherwise -> Nothing
  (ListOf a, ListOf b) -> matchRType a b m
  (Tuple a1 a2, Tuple b1 b2) -> pair a1 a2 b1 b2
  (TEither a1 a2, TEither b1 b2) -> pair a1 a2 b1 b2
  (TTensor s1 e1, TTensor s2 e2) | s1 == s2 -> matchRType e1 e2 m
  (TArrow a1 a2, TArrow b1 b2) -> pair a1 a2 b1 b2
  (GreaterType a1 a2, GreaterType b1 b2) -> pair a1 a2 b1 b2
  _ | pat == target -> Just m
    | otherwise -> Nothing
  where
    pair a1 a2 b1 b2 = matchRType a1 b1 m >>= matchRType a2 b2
