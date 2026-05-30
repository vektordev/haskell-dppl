module SPLL.Lang.Lang (
  Expr (..)
, ExprStub(..)
, toStub
, Value (..)
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
, elementAt
, getFunctionNames
, lookupNeural
, printFlat
) where

import SPLL.Lang.Types
import SPLL.Typing.PType
import SPLL.Typing.RType
import SPLL.Typing.AlgebraicDataTypes

import qualified Data.Set as Set
import Data.Maybe
import qualified Data.Map as Map
import Control.Applicative (liftA2)
import Control.Monad.Random.Lazy (Random)
import Data.Number.Erf (Erf)
import Data.List (intercalate, nub, transpose)
import Debug.Trace
import qualified Data.Bifunctor as Bifunctor

toStub :: Expr -> ExprStub
toStub expr = case expr of
  IfThenElse {}  -> StubIfThenElse
  GreaterThan {} -> StubGreaterThan
  LessThan {}    -> StubLessThan
  Equals {}      -> StubEquals
  And {}         -> StubAnd
  Or {}          -> StubOr
  (ThetaI _ _ _) -> StubThetaI
  (Subtree _ _ _)-> StubSubtree
  (Uniform _)    -> StubUniform
  (Normal _)     -> StubNormal
  (Constant _ _) -> StubConstant
  Not {}         -> StubNot
  (Null _)       -> StubNull
  Cons {}        -> StubCons
  TCons {}       -> StubTCons
  (Var _ _)      -> StubVar
  LetIn {}       -> StubLetIn
  InjF {}        -> StubInjF
  Lambda {}      -> StubLambda
  Apply {}       -> StubApply
  (ReadNN _ _ _) -> StubReadNN
  Error _ _        -> StubError

floatApproxEqThresh :: Double
floatApproxEqThresh = 1e-10

predicateFlat :: (Expr -> Bool) -> Expr -> Bool
predicateFlat f e = f e && all (predicateFlat f) (getSubExprs e)

containedVars :: (Expr -> Set.Set String) -> Expr -> Set.Set String
containedVars f e = Set.union (f e) (foldl Set.union Set.empty (map (containedVars f) (getSubExprs e)))

predicateProg :: (Expr -> Bool) -> Program -> Bool
predicateProg f (Program decls _ _) = and (map (predicateExpr f . snd) decls)

predicateExpr :: (Expr -> Bool) -> Expr -> Bool
predicateExpr f e = f e && and (map (predicateExpr f) (getSubExprs e))

varsOfExpr :: Expr -> Set.Set String
varsOfExpr expr = case expr of
  (Var _ name) -> Set.singleton name
  _ -> Set.empty

isNotTheta :: Expr -> Bool
isNotTheta expr = case expr of
  (ThetaI _ _ name) -> False
  _ -> True

tMapHead :: (Expr -> TypeInfo) -> Expr -> Expr
tMapHead f expr = case expr of
  (IfThenElse _ a b c) -> IfThenElse (f expr) a b c
  (GreaterThan _ a b) -> GreaterThan (f expr) a b
  (LessThan _ a b) -> LessThan (f expr) a b
  (Equals _ a b) -> Equals (f expr) a b
  (ThetaI _ a x) -> ThetaI (f expr) a x
  (Subtree _ a x) -> Subtree (f expr) a x
  (Uniform _) -> Uniform (f expr)
  (Normal _) -> Normal (f expr)
  (Constant _ x) -> Constant (f expr) x
  (And _ a b) -> And (f expr) a b
  (Or _ a b) -> Or (f expr) a b
  (Not _ a) -> Not (f expr) a
  (Null _) -> Null (f expr)
  (Cons _ a b) -> Cons (f expr) a b
  (TCons _ a b) -> TCons (f expr) a b
  (Var _ x) -> Var (f expr) x
  (LetIn _ x a bi) -> LetIn (f expr) x a bi
  (InjF _ x a) -> InjF (f expr) x a
  --(LetInD t x a b) -> LetInD (f expr) x a b
  --(LetInTuple t x a b c) -> LetInTuple (f expr) x a b c
  (Lambda _ name a) -> Lambda (f expr) name a
  (Apply _ a b) -> Apply (f expr) a b
  (ReadNN t n a) -> ReadNN (f expr) n a
  (Error t e) -> Error (f expr) e

tMap :: (Expr -> TypeInfo) -> Expr -> Expr
tMap f expr = case expr of
  (IfThenElse _ a b c) -> IfThenElse (f expr) (tMap f a) (tMap f b) (tMap f c)
  (GreaterThan _ a b) -> GreaterThan (f expr) (tMap f a) (tMap f b)
  (LessThan _ a b) -> LessThan (f expr) (tMap f a) (tMap f b)
  (Equals _ a b) -> Equals (f expr) (tMap f a) (tMap f b)
  (ThetaI _ a x) -> ThetaI (f expr) (tMap f a) x
  (Subtree _ a x) -> Subtree (f expr) (tMap f a) x
  (Uniform _) -> Uniform (f expr)
  (Normal _) -> Normal (f expr)
  (Constant _ x) -> Constant (f expr) x
  (And _ a b) -> And (f expr) (tMap f a) (tMap f b)
  (Or _ a b) -> Or (f expr) (tMap f a) (tMap f b)
  (Not _ a) -> Not (f expr) (tMap f a)
  (Null _) -> Null (f expr)
  (Cons _ a b) -> Cons (f expr) (tMap f a) (tMap f b)
  (TCons _ a b) -> TCons (f expr) (tMap f a) (tMap f b)
  (Var _ x) -> Var (f expr) x
  (LetIn _ x a b) -> LetIn (f expr) x (tMap f a) (tMap f b)
  (InjF t x a) -> InjF (f expr) x (map (tMap f) a)
  --(LetInD t x a b) -> LetInD (f expr) x (tMap f a) (tMap f b)
  --(LetInTuple t x a b c) -> LetInTuple (f expr) x (tMap f a) b (tMap f c)
  (Lambda _ name a) -> Lambda (f expr) name (tMap f a)
  (Apply _ a b) -> Apply (f expr) (tMap f a) (tMap f b)
  (ReadNN _ n a) -> ReadNN (f expr) n (tMap f a)
  (Error t e) -> Error (f expr) e

makeMain :: Expr -> Program
makeMain expr = Program [("main", expr)] [] []

getBinaryConstructor :: Expr -> (TypeInfo -> Expr -> Expr -> Expr)
getBinaryConstructor GreaterThan {} = GreaterThan
getBinaryConstructor LessThan {} = LessThan
getBinaryConstructor Equals {} = Equals
getBinaryConstructor Cons {} = Cons
getBinaryConstructor TCons {} = TCons
getBinaryConstructor And {} = And
getBinaryConstructor Or {} = Or
getBinaryConstructor Apply {} = Apply
--getBinaryConstructor (LetIn t name a b) = \t2 -> \e1 -> \e2 -> LetIn t2 name e1 e2
getBinaryConstructor (LetIn _ name _ _) = (`LetIn` name)

getUnaryConstructor :: Expr -> (TypeInfo -> Expr -> Expr)
getUnaryConstructor (ThetaI _ _ i) = \t a -> ThetaI t a i
getUnaryConstructor (Subtree _ _ i) = \t a -> Subtree t a i
getUnaryConstructor (Lambda _ x _) = (`Lambda` x)
getUnaryConstructor (ReadNN _ x _) = (`ReadNN` x)
getUnaryConstructor (Not _ _) = Not
getUnaryConstructor x = error ("getUnaryConstructor undefined for " ++ show x)

getNullaryConstructor :: Expr -> (TypeInfo -> Expr)
getNullaryConstructor Uniform {} = Uniform
getNullaryConstructor Normal {} = Normal
getNullaryConstructor (Constant t val) = (`Constant` val)
getNullaryConstructor Null {} = Null
getNullaryConstructor (Var _ x) = (`Var` x)
getNullaryConstructor (Error t e) = (`Error` e)

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
  (Equals _ a b) -> [a,b]
  (ThetaI _ a _) -> [a]
  (Subtree _ a _) -> [a]
  (Uniform _) -> []
  (Normal _) -> []
  (Constant _ _) -> []
  (And _ a b) -> [a,b]
  (Or _ a b) -> [a,b]
  (Not _ a) -> [a]
  (Null _) -> []
  (Cons _ a b) -> [a,b]
  (TCons _ a b) -> [a,b]
  (LetIn _ _ a b) -> [a, b]
  (Var _ _) -> []
  (InjF _ _ a) -> a
  --(LetInD t x a b) -> [a,b]
  --(LetInTuple t x a b c) -> [a,c]
  (Lambda _ _ a) -> [a]
  (Apply _ a b) -> [a, b]
  (ReadNN _ _ a) -> [a]
  (Error _ e) -> []

setSubExprs :: Expr -> [Expr] -> Expr
setSubExprs expr [] = case expr of
  Uniform t -> Uniform t
  Normal t -> Normal t
  Constant t x -> Constant t x
  Null t -> Null t
  Var t x -> Var t x
  InjF t n _ -> InjF t n []
  Error t e -> Error t e
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a] = case expr of
  ThetaI t _ x -> ThetaI t a x
  Subtree t _ x -> Subtree t a x
  Lambda t l _ -> Lambda t l a
  Not t _ -> Not t a
  ReadNN t n _ -> ReadNN t n a
  InjF t n _ -> InjF t n [a]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a,b] = case expr of
  GreaterThan t _ _ -> GreaterThan t a b
  LessThan t _ _ -> LessThan t a b
  Equals t _ _ -> Equals t a b
  And t _ _ -> And t a b
  Or t _ _ -> Or t a b
  Cons t _ _ -> Cons t a b
  TCons t _ _ -> TCons t a b
  LetIn t x _ _ -> LetIn t x a b
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
  (Equals t _ _)        -> t
  (ThetaI t _ _)        -> t
  (Subtree t _ _)       -> t
  (Uniform t)           -> t
  (Normal t)            -> t
  (Constant t _)        -> t
  (And t _ _)           -> t
  (Or t _ _)            -> t
  (Not t _)             -> t
  (Null t)              -> t
  (Cons t _ _)          -> t
  (TCons t _ _)         -> t
  (Var t _)             -> t
  (LetIn t _ _ _)       -> t
  (InjF t _ _)          -> t
  --(LetInD t _ _ _)      -> t
  --(LetInTuple t _ _ _ _)-> t
  (Lambda t _ _)        -> t
  (Apply t _ _)         -> t
  (ReadNN t _ _)        -> t
  (Error t _)           -> t

setTypeInfo :: Expr -> TypeInfo -> Expr
setTypeInfo expr t = case expr of
  (IfThenElse _ a b c)  -> IfThenElse t a b c
  (GreaterThan _ a b)   -> GreaterThan t a b
  (LessThan _ a b)      -> LessThan t a b
  (Equals _ a b)        -> Equals t a b
  (ThetaI _ a b)        -> ThetaI t a b
  (Subtree _ a b)       -> Subtree t a b
  (Uniform _)           -> Uniform t
  (Normal _)            -> Normal t
  (Constant _ a)        -> Constant t a
  (And _ a b)           -> And t a b
  (Or _ a b)            -> Or t a b
  (Not _ a)             -> Not t a
  (Null _)              -> Null t
  (Cons _ a b)          -> Cons t a b
  (TCons _ a b)         -> TCons t a b
  (Var _ a)             -> Var t a
  (LetIn _ a b c)       -> LetIn t a b c
  (InjF _ a b)          -> InjF t a b
  --(LetInD _ a b c)     -> (LetInD t a b c)
  --(LetInTuple _ a b c d) -> (LetInTuple t a b c d)
  (Lambda _ a b)        -> Lambda t a b
  (Apply _ a b)         -> Apply t a b
  (ReadNN _ a b)        -> ReadNN t a b
  (Error _ e)           -> Error t e

constructVList :: [GenericValue a] -> GenericValue a
constructVList xs = VList $ foldr ListCont EmptyList xs

multiValueToValueList :: MultiValue -> [Value]
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
valueListToMultiValue lst@((VEither _):_) = error "Not all elements in the list are Eithers"
valueListToMultiValue lst@((VTuple _ _):_) | all isVTuple lst = MultiTuple aVals bVals
  where
    aVals = valueListToMultiValue [a | VTuple a _ <- lst]
    bVals = valueListToMultiValue [b | VTuple _ b <- lst]
valueListToMultiValue lst@((VTuple _ _):_) = error "Not all elements in the list are Tuples"
valueListToMultiValue lst@((VADT _ _):_) | all isVADT lst = MultiADT (map reconstructConstructor cns)
  where
    cns = nub [cn | VADT cn _ <- lst]
    reconstructConstructor cn = 
      let field_lists = [fields | VADT cn' fields <- lst, cn' == cn]
          transposed_fields = if null field_lists then [] else map nub (transpose field_lists)
      in (cn, map valueListToMultiValue transposed_fields)
valueListToMultiValue lst@((VADT _ _):_) = error "Not all elements in the list are ADTs"
valueListToMultiValue lst = MultiDiscretes lst

valueInMultiValue :: MultiValue -> Value -> Bool
valueInMultiValue (MultiDiscretes d) x = x `elem` d
valueInMultiValue (MultiEither ml _) (VEither (Left l)) = valueInMultiValue ml l
valueInMultiValue (MultiEither _ mr) (VEither (Right r)) = valueInMultiValue mr r
valueInMultiValue (MultiTuple mf ms) (VTuple f s) = valueInMultiValue mf f && valueInMultiValue ms s
valueInMultiValue (MultiADT mConstrs) (VADT cName vals) = fromMaybe False (do
  constr <- lookup cName mConstrs
  return $ all (uncurry valueInMultiValue) (zip constr vals))

unionMultiValues :: MultiValue -> MultiValue -> MultiValue
unionMultiValues (MultiDiscretes as) (MultiDiscretes bs) = MultiDiscretes (nub (as ++ bs))
unionMultiValues (MultiEither ls1 rs1) (MultiEither ls2 rs2) = MultiEither (unionMultiValues ls1 ls2) (unionMultiValues rs1 rs2)
unionMultiValues (MultiTuple ls1 rs1) (MultiTuple ls2 rs2) = MultiTuple (unionMultiValues ls1 ls2) (unionMultiValues rs1 rs2)
unionMultiValues (MultiADT constrs1) (MultiADT constrs2) = MultiADT (map (\cn -> (cn, unionConstr cn)) cNames)
  where
    cNames = nub $ map fst constrs1 ++ map fst constrs2
    unionConstr cn = zipWith unionMultiValues (fromMaybe [] (lookup cn constrs1)) (fromMaybe [] (lookup cn constrs1))


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
prettyPrintProgCustomTI fn (Program decls neurals adts) = concatMap prettyPrintADTs adts ++  concatMap (prettyPrintDecl fn) decls ++ concatMap prettyPrintNeural neurals

prettyPrintADTs :: ADTDecl  -> [String]
prettyPrintADTs ADTDecl{dataName=name, constructors=constr, maxDepth=d} = ("data " ++ name ++ "::"):map (\rts -> "\n|"++ show rts) constr

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
  Equals {} -> "Equals"
  (ThetaI _ _ i) -> "Theta_" ++ show i
  (Subtree _ _ i) -> "Subtree_" ++ show i
  Uniform {} -> "Uniform"
  Normal {} -> "Normal"
  (Constant _ x) -> "Constant (" ++ show x ++ ")"
  And {} -> "And"
  Or {} -> "Or"
  Not {} -> "Not"
  (Null _) -> "Null"
  Cons {} -> "Cons"
  TCons {} -> "TCons"
  (Var _ a) -> "Var " ++ a
  LetIn {} -> "LetIn"
  --(LetInD {}) -> "LetInD"
  --(LetInTuple {}) -> "LetInTuple"
  (InjF t fname _)        -> "InjF (" ++ fname ++ ")"
  (Lambda _ name _) -> "\\" ++ name  ++ " -> "
  Apply {} -> "Apply"
  (ReadNN _ name _) -> "ReadNN " ++ name
  (Error _ e)       -> "Error: " ++ e


