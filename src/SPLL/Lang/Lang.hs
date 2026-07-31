module SPLL.Lang.Lang (
  Expr (..)
, ExprF (..)
, ExprStub(..)
, toStub
, Value
, Program (..)
, ThetaTree (..)
, floatApproxEqThresh
, getTypeInfo
, setTypeInfo
, tMap
, tMapM
, makeMain
, tMapHead
, getRType
, Name
, prettyPrintProg
, prettyPrintProgRTyOnly
, prettyPrint
, prettyRType
, getSubExprs
, setSubExprs
, containedVars
, varsOfExpr
, predicateExpr
, predicateFlat
, predicateProg
, isNotTheta
, constructVList
, multiValueToValueList
, multiValueContainsContinuous
, multiValueIsFinite
, valueListToMultiValue
, valueInMultiValue
, unionMultiValues
, autoDeriveMultiValue
, resolveMultiAuto
, resolveMultiValueTypeDecl
, containsMultiValueTypeRef
, neuralValueType
, elementAt
, getFunctionNames
, lookupNeural
, printFlat
, InjFName(..)
) where

import SPLL.Lang.Types
import SPLL.Typing.RType
import SPLL.Typing.AlgebraicDataTypes

import qualified Data.Set as Set
import Data.Maybe
import Data.List (nub, transpose, find)
import Data.Traversable (mapAccumL)
import qualified Data.Bifunctor as Bifunctor

toStub :: Expr -> ExprStub
toStub expr = case node expr of
  IfThenElse {}  -> StubIfThenElse
  ThetaI {}      -> StubThetaI
  Subtree {}     -> StubSubtree
  Constant {}    -> StubConstant
  Var {}         -> StubVar
  InjF {}        -> StubInjF
  Lambda {}      -> StubLambda
  Apply {}       -> StubApply
  ReadNN {}      -> StubReadNN

floatApproxEqThresh :: Double
floatApproxEqThresh = 1e-10

predicateFlat :: (Expr -> Bool) -> Expr -> Bool
predicateFlat f e = f e && all (predicateFlat f) (getSubExprs e)

containedVars :: (Expr -> Set.Set String) -> Expr -> Set.Set String
containedVars f e = Set.union (f e) (foldl Set.union Set.empty (map (containedVars f) (getSubExprs e)))

predicateProg :: (Expr -> Bool) -> Program -> Bool
predicateProg f (Program decls _ _ _) = and (map (predicateExpr f . snd) decls)

predicateExpr :: (Expr -> Bool) -> Expr -> Bool
predicateExpr f e = f e && and (map (predicateExpr f) (getSubExprs e))

varsOfExpr :: Expr -> Set.Set String
varsOfExpr expr = case node expr of
  Var name -> Set.singleton name
  _ -> Set.empty

isNotTheta :: Expr -> Bool
isNotTheta expr = case node expr of
  ThetaI {} -> False
  _ -> True

-- | Replace the annotation on the root node only.
tMapHead :: (Expr -> TypeInfo) -> Expr -> Expr
tMapHead f expr = expr { ann = f expr }

-- | Bottom-up rewrite of every node's annotation. The callback sees the
-- *original* node (children not yet rewritten).
tMap :: (Expr -> TypeInfo) -> Expr -> Expr
tMap f expr = Expr (f expr) (fmap (tMap f) (node expr))

makeMain :: Expr -> Program
makeMain expr = Program [("main", expr)] [] [] []

-- | Monadic 'tMap'. The annotation effect runs before the children's.
tMapM :: Monad m => (Expr -> m TypeInfo) -> Expr -> m Expr
tMapM f expr = do
  t <- f expr
  n <- traverse (tMapM f) (node expr)
  return (Expr t n)

getSubExprs :: Expr -> [Expr]
getSubExprs = foldr (:) [] . node

-- | Replace the sub-expressions of a node, positionally. The replacement list
-- must have the same length as 'getSubExprs' of the same node (except for
-- 'InjF', whose arity is variable).
setSubExprs :: Expr -> [Expr] -> Expr
setSubExprs (Expr t (InjF n _)) subExprs = Expr t (InjF n subExprs)
setSubExprs expr subExprs
  | length subExprs /= length (getSubExprs expr) = error "unmatched expr in setSubExprs"
  | otherwise = Expr (ann expr) (snd (mapAccumL replace subExprs (node expr)))
  where
    replace (x:rest) _ = (rest, x)
    replace []       _ = error "unmatched expr in setSubExprs"

getTypeInfo :: Expr -> TypeInfo
getTypeInfo = ann

setTypeInfo :: Expr -> TypeInfo -> Expr
setTypeInfo expr t = expr { ann = t }

constructVList :: [GenericValue a] -> GenericValue a
constructVList xs = VList $ foldr ListCont EmptyList xs

multiValueToValueList :: MultiValue -> [Value]
-- A continuous slot has no enumerable values: any composite containing it also has none.
multiValueToValueList MultiContinuous = []
multiValueToValueList MultiAuto = error "multiValueToValueList: unresolved auto-placeholder (_); this should have been resolved before discrete-value propagation"
multiValueToValueList (MultiDiscretes vals) = vals
multiValueToValueList (MultiEither ls rs) = map (VEither . Left) lVals ++ map (VEither . Right) rVals
  where
    lVals = multiValueToValueList ls
    rVals = multiValueToValueList rs
multiValueToValueList (MultiTuple as bs) = [VTuple aVal bVal | aVal <- aVals, bVal <- bVals]
  where
    aVals = multiValueToValueList as
    bVals = multiValueToValueList bs
multiValueToValueList (MultiADT constrs) = concatMap (\(cn, fieldCombos) -> map (VADT cn) fieldCombos) constrFieldCombinations
  where allFieldCombinations = sequence . map multiValueToValueList
        constrFieldCombinations = map (Bifunctor.second allFieldCombinations) constrs

-- | True if the MultiValue has a continuous (Real) leaf anywhere. Such a value set
-- has no finite enumeration: 'multiValueToValueList' would yield only its discrete
-- residue, so enum-based inference must never be offered for it (the enum-annotation
-- pass declines to tag it, and 'isEnumerable' in the IRCompiler refuses it).
-- 'MultiTypeRef' is resolved away before MultiValues reach tags, so it is structural
-- here; 'MultiAuto' must likewise be resolved before asking.
multiValueContainsContinuous :: MultiValue -> Bool
multiValueContainsContinuous MultiContinuous = True
multiValueContainsContinuous (MultiDiscretes _) = False
multiValueContainsContinuous (MultiTuple a b) = multiValueContainsContinuous a || multiValueContainsContinuous b
multiValueContainsContinuous (MultiEither a b) = multiValueContainsContinuous a || multiValueContainsContinuous b
multiValueContainsContinuous (MultiADT constrs) = any (any multiValueContainsContinuous . snd) constrs
multiValueContainsContinuous (MultiTypeRef _) = False
multiValueContainsContinuous MultiAuto = False

-- | True if the MultiValue enumerates a non-empty, statically finite set of values,
-- so that 'multiValueToValueList' is total on it and returns every value of the
-- domain. Stricter than @not . 'multiValueContainsContinuous'@ in two ways that
-- matter to a caller who wants the enumeration itself rather than a yes/no on
-- enum-based inference: an unresolved 'MultiAuto'/'MultiTypeRef' is refused (the
-- former makes 'multiValueToValueList' @error@, the latter has no case at all),
-- and a composite is finite only if /every/ slot is -- an @Either@ with one
-- continuous arm enumerates its discrete arm alone, which is a strict subset of
-- the domain and would silently under-enumerate.
--
-- Backs the batched dense-enumeration mode (design heterogeneous-batch-inference
-- M3), which needs the whole domain or nothing.
multiValueIsFinite :: MultiValue -> Bool
multiValueIsFinite MultiContinuous = False
multiValueIsFinite MultiAuto = False
multiValueIsFinite (MultiTypeRef _) = False
multiValueIsFinite (MultiDiscretes vals) = not (null vals)
multiValueIsFinite (MultiTuple a b) = multiValueIsFinite a && multiValueIsFinite b
multiValueIsFinite (MultiEither a b) = multiValueIsFinite a && multiValueIsFinite b
-- A nullary constructor has no fields, so @all _ []@ is vacuously true and the
-- constructor contributes exactly one value -- which is what we want.
multiValueIsFinite (MultiADT constrs) = not (null constrs) && all (all multiValueIsFinite . snd) constrs

valueListToMultiValue :: [Value] -> MultiValue
valueListToMultiValue lst@((VEither _):_) | all isVEither lst = MultiEither lVals rVals
  where
    lVals = valueListToMultiValue [l | VEither (Left l) <- lst]
    rVals = valueListToMultiValue [r | VEither (Right r) <- lst]
valueListToMultiValue ((VEither _):_) = error "Not all elements in the list are Eithers"
valueListToMultiValue lst@((VTuple _ _):_) | all isVTuple lst = MultiTuple aVals bVals
  where
    aVals = valueListToMultiValue [a | VTuple a _ <- lst]
    bVals = valueListToMultiValue [b | VTuple _ b <- lst]
valueListToMultiValue ((VTuple _ _):_) = error "Not all elements in the list are Tuples"
valueListToMultiValue lst@((VADT _ _):_) | all isVADT lst = MultiADT (map reconstructConstructor cns)
  where
    cns = nub [cn | VADT cn _ <- lst]
    reconstructConstructor cn =
      let field_lists = [fields | VADT cn' fields <- lst, cn' == cn]
          transposed_fields = if null field_lists then [] else map nub (transpose field_lists)
      in (cn, map valueListToMultiValue transposed_fields)
valueListToMultiValue ((VADT _ _):_) = error "Not all elements in the list are ADTs"
valueListToMultiValue lst = MultiDiscretes lst

valueInMultiValue :: MultiValue -> Value -> Bool
valueInMultiValue MultiContinuous (VFloat _) = True
valueInMultiValue (MultiDiscretes d) x = x `elem` d
valueInMultiValue (MultiEither ml _) (VEither (Left l)) = valueInMultiValue ml l
valueInMultiValue (MultiEither _ mr) (VEither (Right r)) = valueInMultiValue mr r
valueInMultiValue (MultiTuple mf ms) (VTuple f s) = valueInMultiValue mf f && valueInMultiValue ms s
valueInMultiValue (MultiADT mConstrs) (VADT cName vals) = fromMaybe False (do
  constr <- lookup cName mConstrs
  return $ all (uncurry valueInMultiValue) (zip constr vals))

unionMultiValues :: MultiValue -> MultiValue -> MultiValue
unionMultiValues MultiContinuous MultiContinuous = MultiContinuous
unionMultiValues (MultiDiscretes as) (MultiDiscretes bs) = MultiDiscretes (nub (as ++ bs))
unionMultiValues (MultiEither ls1 rs1) (MultiEither ls2 rs2) = MultiEither (unionMultiValues ls1 ls2) (unionMultiValues rs1 rs2)
unionMultiValues (MultiTuple ls1 rs1) (MultiTuple ls2 rs2) = MultiTuple (unionMultiValues ls1 ls2) (unionMultiValues rs1 rs2)
unionMultiValues (MultiADT constrs1) (MultiADT constrs2) = MultiADT (map (\cn -> (cn, unionConstr cn)) cNames)
  where
    cNames = nub $ map fst constrs1 ++ map fst constrs2
    unionConstr cn = zipWith unionMultiValues (fromMaybe [] (lookup cn constrs1)) (fromMaybe [] (lookup cn constrs2))

-- | Attempt to derive the full MultiValue enumeration for an RType without any explicit
-- annotation. Succeeds for types with a finite, statically-known set of values (Bool, Float
-- as a continuous leaf, and Tuples/Eithers/non-recursive ADTs built from such types). Fails
-- for Int and Symbol (unbounded domains) and for recursive ADTs (would not terminate).
autoDeriveMultiValue :: [ADTDecl] -> RType -> Either String MultiValue
autoDeriveMultiValue _ TFloat = Right MultiContinuous
autoDeriveMultiValue _ TBool = Right (MultiDiscretes [VBool True, VBool False])
autoDeriveMultiValue _ TInt = Left "cannot auto-derive an enumeration for Int (unbounded) - specify the values explicitly, e.g. [0,1,2,...,10]"
autoDeriveMultiValue _ TSymbol = Left "cannot auto-derive an enumeration for Symbol - specify the values explicitly"
autoDeriveMultiValue adts (Tuple a b) = MultiTuple <$> autoDeriveMultiValue adts a <*> autoDeriveMultiValue adts b
autoDeriveMultiValue adts (TEither a b) = MultiEither <$> autoDeriveMultiValue adts a <*> autoDeriveMultiValue adts b
autoDeriveMultiValue adts (TADT name) = case find ((== name) . dataName) adts of
  Nothing -> Left ("unknown ADT '" ++ name ++ "' referenced in neural declaration")
  Just adt
    | isRecursive adt -> case adtDepth adt of
        -- A recursive type auto-derives to its declared default depth: build the
        -- constructor set with a MultiTypeRef at each self-referential field, then
        -- unroll it with the shared resolver (same one the explicit `of Nx.{...}`
        -- form uses). Without a depth there is no finite enumeration to derive.
        Just d  -> do
          body <- MultiADT <$> mapM deriveConstructorRec (constructors adt)
          return (resolveMultiValueTypeDecl d body (name, body))
        Nothing -> Left ("cannot auto-derive recursive ADT '" ++ name ++ "' without a recursion depth - add `depth N` to its `data` declaration, or give a depth-limited MultiValue explicitly, e.g. 3x." ++ name ++ ".{...}")
    | otherwise -> MultiADT <$> mapM deriveConstructor (constructors adt)
  where
    isRecursive adt = any (any ((== TADT name) . snd) . snd) (constructors adt)
    deriveConstructor (cName, fields) = (,) cName <$> mapM (autoDeriveMultiValue adts . snd) fields
    -- A directly self-referential field becomes a MultiTypeRef for the unroller;
    -- every other field auto-derives as usual. (Only direct recursion is detected;
    -- nested `ListOf (TADT name)` or mutual recursion still needs an explicit `of`.)
    deriveConstructorRec (cName, fields) = (,) cName <$> mapM deriveField fields
    deriveField (_, TADT n) | n == name = Right (MultiTypeRef name)
    deriveField (_, ft)                 = autoDeriveMultiValue adts ft
autoDeriveMultiValue _ ty = Left ("cannot auto-derive a MultiValue for type " ++ show ty ++ " - specify it explicitly")

-- | Resolve "_" (MultiAuto) placeholders within a (possibly partial) MultiValue annotation,
-- recursing alongside the corresponding RType. Leaves everything else untouched.
resolveMultiAuto :: [ADTDecl] -> RType -> MultiValue -> MultiValue
resolveMultiAuto adts ty MultiAuto = either error id (autoDeriveMultiValue adts ty)
resolveMultiAuto adts (Tuple a b) (MultiTuple l r) = MultiTuple (resolveMultiAuto adts a l) (resolveMultiAuto adts b r)
resolveMultiAuto adts (TEither a b) (MultiEither l r) = MultiEither (resolveMultiAuto adts a l) (resolveMultiAuto adts b r)
resolveMultiAuto adts (TADT name) (MultiADT cs) = MultiADT (map resolveConstr cs)
  where
    fieldTypes = case find ((== name) . dataName) adts of
      Just adt -> [(cn, map snd fs) | (cn, fs) <- constructors adt]
      Nothing -> []
    resolveConstr (cn, mvs) = (cn, zipWith (resolveMultiAuto adts) (fromMaybe [] (lookup cn fieldTypes)) mvs)
resolveMultiAuto _ _ mv = mv

-- | Unroll a recursive MultiValue to a finite depth. The @(String, MultiValue)@
-- pair is the recursion binder: every 'MultiTypeRef' whose name matches is
-- replaced by the binder's body and the depth decremented. At depth 1 the
-- constructors that would recurse again are dropped; at 0 there is nothing left
-- to unroll. Used by both the explicit @of Nx.{...}@ clause (Parser) and the
-- auto-derivation of a depth-annotated @data@ type ('autoDeriveMultiValue').
resolveMultiValueTypeDecl :: Int -> MultiValue -> (String, MultiValue) -> MultiValue
resolveMultiValueTypeDecl 0 (MultiTypeRef _) _ = error "Cannot recurse, no depth left"
resolveMultiValueTypeDecl 1 (MultiTypeRef _) (declName, MultiADT constrs) = MultiADT (filter (\(_, args) -> not $ any (containsMultiValueTypeRef declName) args) constrs)
resolveMultiValueTypeDecl depthLeft (MultiTypeRef refName) decl@(declName, declVal) | declName == refName = resolveMultiValueTypeDecl (depthLeft - 1) declVal decl
resolveMultiValueTypeDecl _ (MultiDiscretes d) _ = MultiDiscretes d
resolveMultiValueTypeDecl _ MultiContinuous _ = MultiContinuous
resolveMultiValueTypeDecl _ MultiAuto _ = MultiAuto
resolveMultiValueTypeDecl depthLeft (MultiTuple l r) decl =
  MultiTuple (resolveMultiValueTypeDecl depthLeft l decl)
             (resolveMultiValueTypeDecl depthLeft r decl)
resolveMultiValueTypeDecl depthLeft (MultiEither l r) decl =
  MultiEither (resolveMultiValueTypeDecl depthLeft l decl)
              (resolveMultiValueTypeDecl depthLeft r decl)
resolveMultiValueTypeDecl depthLeft (MultiADT cons) decl =
  MultiADT [(cname, map (\mv -> resolveMultiValueTypeDecl depthLeft mv decl) args) |
            (cname, args) <- cons]

containsMultiValueTypeRef :: String -> MultiValue -> Bool
containsMultiValueTypeRef _ (MultiDiscretes _) = False
containsMultiValueTypeRef _ MultiContinuous = False
containsMultiValueTypeRef _ MultiAuto = False
containsMultiValueTypeRef n (MultiTypeRef m) = n == m
containsMultiValueTypeRef n (MultiEither l r) = containsMultiValueTypeRef n l || containsMultiValueTypeRef n r
containsMultiValueTypeRef n (MultiTuple l r) = containsMultiValueTypeRef n l || containsMultiValueTypeRef n r
containsMultiValueTypeRef n (MultiADT constrs) = any (\(_, args) -> any (containsMultiValueTypeRef n) args) constrs

-- | The output (target) RType of a Decoder neural declaration's "Symbol -> target" arrow
-- type - i.e. the type a NeuralDecl's MultiValue annotation describes.  The (source ->
-- Symbol) Encoder direction has been removed (rejected at validation), so only the decoder
-- shape resolves to a value type.
neuralValueType :: RType -> Maybe RType
neuralValueType (TArrow TSymbol target) = Just target
neuralValueType _ = Nothing


elementAt :: ValueList a -> Int -> GenericValue a
elementAt (ListCont x _) 0 = x
elementAt (ListCont _ xs) i = elementAt xs (i-1)
elementAt EmptyList _ = error "Index out of bounds"
elementAt AnyList _ = error "Cannot iterate AnyLists"

getRType :: Value -> RType
getRType (VBool _) = TBool
getRType (VInt _) = TInt
getRType (VSymbol _) = TSymbol
getRType (VFloat _) = TFloat
getRType VUnit = TUnit
getRType (VList (ListCont a _)) = ListOf $ getRType a
getRType (VList EmptyList) = NullList
getRType (VTuple t1 t2) = Tuple (getRType t1) (getRType t2)
getRType (VEither (Left a)) = TEither (getRType a) SPLL.Typing.RType.NotSetYet
getRType (VEither (Right a)) = TEither SPLL.Typing.RType.NotSetYet (getRType a)

lookupNeural :: String -> [NeuralDecl] -> Maybe (RType, Maybe MultiValue)
lookupNeural name decls = foldr (\(n, r, t) ret -> if n == name then Just (r, t) else ret) Nothing decls

-- Returns explicit functions declared as well as implicit functions from ADTs
getFunctionNames :: Program -> [String]
getFunctionNames p = explicitFs ++ implicitFs
  where
    explicitFs = map fst (functions p)
    implicitFs = implicitFunctionNames (adts p)

prettyPrintProg :: Program -> [String]
prettyPrintProg = prettyPrintProgCustomTI prettyFullTypeInfo

prettyPrintProgRTyOnly :: Program -> [String]
prettyPrintProgRTyOnly = prettyPrintProgCustomTI prettyRTypeOnly

prettyPrintProgCustomTI :: (TypeInfo -> String) -> Program -> [String]
prettyPrintProgCustomTI fn (Program decls neurals adts _) = concatMap prettyPrintADTs adts ++  concatMap (prettyPrintDecl fn) decls ++ concatMap prettyPrintNeural neurals

prettyPrintADTs :: ADTDecl  -> [String]
prettyPrintADTs ADTDecl{dataName=name, constructors=constr, adtDepth=d} = ("data " ++ name ++ "::" ++ maybe "" (\n -> " depth " ++ show n) d):map (\rts -> "\n|"++ show rts) constr

prettyPrintNeural :: NeuralDecl -> [String]
prettyPrintNeural (name, ty, range) = l1:l2:(l3 range):[]
  where
    l1 = ("--- Neural: " ++ name ++ "---")
    l2 = ("\t :: " ++ show ty)
    l3 (Just (MultiDiscretes lst)) = ("\t" ++ (show $ length lst))
    l3 (Nothing) = ("\t" ++ (show $ 0))
    l3 _ = "prettyprint not implemented"

prettyPrintDecl :: (TypeInfo -> String) -> FnDecl -> [String]
prettyPrintDecl fn (name, expr) = ("--- Function: " ++ name ++ "---") : prettyPrintCustomTI fn expr

prettyFullTypeInfo :: TypeInfo -> String
prettyFullTypeInfo ti = show ti

prettyRTypeOnly :: TypeInfo -> String
prettyRTypeOnly ti = prettyRType (rType ti)

prettyRType :: RType -> String
prettyRType (TArrow a b) = "(" ++ prettyRType a ++ ") -> (" ++ prettyRType b ++ ")"
prettyRType (TVarR (SPLL.Typing.RType.TV name)) = name
prettyRType other = show other

prettyPrint :: Expr -> [String]
prettyPrint = prettyPrintCustomTI prettyFullTypeInfo

prettyPrintCustomTI :: (TypeInfo -> String) -> Expr -> [String]
prettyPrintCustomTI fn expr =
  fstLine : indented
    where
      childExprs = getSubExprs expr
      indented = map indent $ concatMap (prettyPrintCustomTI fn) childExprs :: [String]
      indent ls = "    " ++ ls
      fstLine = printFlat expr ++ " :: (" ++ fn (getTypeInfo expr) ++ ")"

printFlat :: Expr -> String
printFlat expr = case node expr of
  IfThenElse {} -> "IfThenElse"
  ThetaI _ i -> "Theta_" ++ show i
  Subtree _ i -> "Subtree_" ++ show i
  Constant x -> "Constant (" ++ show x ++ ")"
  Var a -> "Var " ++ a
  InjF (Named fname) _ -> "InjF (" ++ fname ++ ")"
  Lambda name _ -> "\\" ++ name  ++ " -> "
  Apply {} -> "Apply"
  ReadNN name _ -> "ReadNN " ++ name


