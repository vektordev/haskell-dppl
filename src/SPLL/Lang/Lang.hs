module SPLL.Lang.Lang (
  Expr (..)
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
, valueListToMultiValue
, valueInMultiValue
, unionMultiValues
, autoDeriveMultiValue
, resolveMultiAuto
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
import qualified Data.Bifunctor as Bifunctor

toStub :: Expr -> ExprStub
toStub expr = case expr of
  IfThenElse {}  -> StubIfThenElse
  GreaterThan {} -> StubGreaterThan
  LessThan {}    -> StubLessThan
  (ThetaI _ _ _) -> StubThetaI
  (Subtree _ _ _)-> StubSubtree
  (Constant _ _) -> StubConstant
  (Var _ _)      -> StubVar
  InjF {}        -> StubInjF
  Lambda {}      -> StubLambda
  Apply {}       -> StubApply
  (ReadNN _ _ _) -> StubReadNN

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
varsOfExpr expr = case expr of
  (Var _ name) -> Set.singleton name
  _ -> Set.empty

isNotTheta :: Expr -> Bool
isNotTheta expr = case expr of
  (ThetaI _ _ _) -> False
  _ -> True

tMapHead :: (Expr -> TypeInfo) -> Expr -> Expr
tMapHead f expr = case expr of
  (IfThenElse _ a b c) -> IfThenElse (f expr) a b c
  (GreaterThan _ a b) -> GreaterThan (f expr) a b
  (LessThan _ a b) -> LessThan (f expr) a b
  (ThetaI _ a x) -> ThetaI (f expr) a x
  (Subtree _ a x) -> Subtree (f expr) a x
  (Constant _ x) -> Constant (f expr) x
  (Var _ x) -> Var (f expr) x
  (InjF _ x a) -> InjF (f expr) x a
  (Lambda _ name a) -> Lambda (f expr) name a
  (Apply _ a b) -> Apply (f expr) a b
  (ReadNN _ n a) -> ReadNN (f expr) n a

tMap :: (Expr -> TypeInfo) -> Expr -> Expr
tMap f expr = case expr of
  (IfThenElse _ a b c) -> IfThenElse (f expr) (tMap f a) (tMap f b) (tMap f c)
  (GreaterThan _ a b) -> GreaterThan (f expr) (tMap f a) (tMap f b)
  (LessThan _ a b) -> LessThan (f expr) (tMap f a) (tMap f b)
  (ThetaI _ a x) -> ThetaI (f expr) (tMap f a) x
  (Subtree _ a x) -> Subtree (f expr) (tMap f a) x
  (Constant _ x) -> Constant (f expr) x
  (Var _ x) -> Var (f expr) x
  (InjF _ x a) -> InjF (f expr) x (map (tMap f) a)
  (Lambda _ name a) -> Lambda (f expr) name (tMap f a)
  (Apply _ a b) -> Apply (f expr) (tMap f a) (tMap f b)
  (ReadNN _ n a) -> ReadNN (f expr) n (tMap f a)

makeMain :: Expr -> Program
makeMain expr = Program [("main", expr)] [] [] []

getBinaryConstructor :: Expr -> (TypeInfo -> Expr -> Expr -> Expr)
getBinaryConstructor GreaterThan {} = GreaterThan
getBinaryConstructor LessThan {} = LessThan
getBinaryConstructor Apply {} = Apply

getUnaryConstructor :: Expr -> (TypeInfo -> Expr -> Expr)
getUnaryConstructor (ThetaI _ _ i) = \t a -> ThetaI t a i
getUnaryConstructor (Subtree _ _ i) = \t a -> Subtree t a i
getUnaryConstructor (Lambda _ x _) = (`Lambda` x)
getUnaryConstructor (ReadNN _ x _) = (`ReadNN` x)
getUnaryConstructor x = error ("getUnaryConstructor undefined for " ++ show x)

getNullaryConstructor :: Expr -> (TypeInfo -> Expr)
getNullaryConstructor (Constant _ val) = (`Constant` val)
getNullaryConstructor (Var _ x) = (`Var` x)

tMapM :: Monad m => (Expr -> m TypeInfo) -> Expr -> m Expr
tMapM f expr@(IfThenElse _ a b c) = do
  t <- f expr
  fa <- tMapM f a
  fb <- tMapM f b
  fc <- tMapM f c
  return $ IfThenElse t fa fb fc
tMapM f expr@(InjF _ name p) = do
  fp <- mapM (tMapM f) p
  t <- f expr
  return $ InjF t name fp
tMapM f expr
  | length (getSubExprs expr) == 0 = do
      t <- f expr
      return $ getNullaryConstructor expr t
  | length (getSubExprs expr) == 1 = do
       t <- f expr
       subExpr <- tMapM f (getSubExprs expr !! 0)
       return $ getUnaryConstructor expr t subExpr
  | length (getSubExprs expr) == 2 =do
       t <- f expr
       subExpr0 <- tMapM f (getSubExprs expr !! 0)
       subExpr1 <- tMapM f (getSubExprs expr !! 1)
       return $ getBinaryConstructor expr t subExpr0 subExpr1

getSubExprs :: Expr -> [Expr]
getSubExprs expr = case expr of
  (IfThenElse _ a b c) -> [a,b,c]
  (GreaterThan _ a b) -> [a,b]
  (LessThan _ a b) -> [a,b]
  (ThetaI _ a _) -> [a]
  (Subtree _ a _) -> [a]
  (Constant _ _) -> []
  (Var _ _) -> []
  (InjF _ _ a) -> a
  (Lambda _ _ a) -> [a]
  (Apply _ a b) -> [a, b]
  (ReadNN _ _ a) -> [a]

setSubExprs :: Expr -> [Expr] -> Expr
setSubExprs expr [] = case expr of
  Constant t x -> Constant t x
  Var t x -> Var t x
  InjF t n _ -> InjF t n []
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a] = case expr of
  ThetaI t _ x -> ThetaI t a x
  Subtree t _ x -> Subtree t a x
  Lambda t l _ -> Lambda t l a
  ReadNN t n _ -> ReadNN t n a
  InjF t n _ -> InjF t n [a]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a,b] = case expr of
  GreaterThan t _ _ -> GreaterThan t a b
  LessThan t _ _ -> LessThan t a b
  Apply t _ _ -> Apply t a b
  InjF t n _ -> InjF t n [a, b]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a,b,c] = case expr of
  IfThenElse t _ _ _ -> IfThenElse t a b c
  InjF t n _ -> InjF t n [a, b, c]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr subExprs = case expr of
  InjF t l _ -> InjF t l subExprs
  _ -> error "unmatched expr in setSubExprs"

getTypeInfo :: Expr -> TypeInfo
getTypeInfo expr = case expr of
  (IfThenElse t _ _ _)  -> t
  (GreaterThan t _ _)   -> t
  (LessThan t _ _)      -> t
  (ThetaI t _ _)        -> t
  (Subtree t _ _)       -> t
  (Constant t _)        -> t
  (Var t _)             -> t
  (InjF t _ _)          -> t
  (Lambda t _ _)        -> t
  (Apply t _ _)         -> t
  (ReadNN t _ _)        -> t

setTypeInfo :: Expr -> TypeInfo -> Expr
setTypeInfo expr t = case expr of
  (IfThenElse _ a b c)  -> IfThenElse t a b c
  (GreaterThan _ a b)   -> GreaterThan t a b
  (LessThan _ a b)      -> LessThan t a b
  (ThetaI _ a b)        -> ThetaI t a b
  (Subtree _ a b)       -> Subtree t a b
  (Constant _ a)        -> Constant t a
  (Var _ a)             -> Var t a
  (InjF _ a b)          -> InjF t a b
  (Lambda _ a b)        -> Lambda t a b
  (Apply _ a b)         -> Apply t a b
  (ReadNN _ a b)        -> ReadNN t a b

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
    | any (any ((== TADT name) . snd) . snd) (constructors adt) ->
        Left ("cannot auto-derive recursive ADT '" ++ name ++ "' - specify a depth-limited MultiValue explicitly, e.g. <depth>x." ++ name ++ ".{...}")
    | otherwise -> MultiADT <$> mapM deriveConstructor (constructors adt)
  where
    deriveConstructor (cName, fields) = (,) cName <$> mapM (autoDeriveMultiValue adts . snd) fields
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

-- | The output (decoder) or input (encoder) RType of a neural declaration's "Symbol <->
-- target" arrow type - i.e. the type a NeuralDecl's MultiValue annotation describes.
neuralValueType :: RType -> Maybe RType
neuralValueType (TArrow TSymbol target) = Just target
neuralValueType (TArrow source TSymbol) = Just source
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
prettyPrintADTs ADTDecl{dataName=name, constructors=constr} = ("data " ++ name ++ "::"):map (\rts -> "\n|"++ show rts) constr

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
printFlat expr = case expr of
  IfThenElse {} -> "IfThenElse"
  GreaterThan {} -> "GreaterThan"
  LessThan {} -> "LessThan"
  (ThetaI _ _ i) -> "Theta_" ++ show i
  (Subtree _ _ i) -> "Subtree_" ++ show i
  (Constant _ x) -> "Constant (" ++ show x ++ ")"
  (Var _ a) -> "Var " ++ a
  (InjF _ (Named fname) _) -> "InjF (" ++ fname ++ ")"
  (Lambda _ name _) -> "\\" ++ name  ++ " -> "
  Apply {} -> "Apply"
  (ReadNN _ name _) -> "ReadNN " ++ name


