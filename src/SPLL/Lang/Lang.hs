module SPLL.Lang.Lang (
  Expr (..)
, ExprStub(..)
, toStub
, Value (..)
, Program (..)
, ThetaTree (..)
, getTypeInfo
, setTypeInfo
, tMap
, tMapM
, tMapProg
, makeMain
, tMapHead
, getRType
, Name
, exprMap
, prettyPrintProg
, prettyPrintProgRTyOnly
, prettyPrint
, prettyPrintProgNoReq
, prettyPrintNoReq
, prettyRType
, getVFloat
, WitnessedVars
, getSubExprs
, setSubExprs
, containedVars
, varsOfExpr
, predicateExpr
, predicateFlat
, predicateProg
, isNotTheta
, tTraverse
, constructVList
, elementAt
, getFunctionNames
) where

import SPLL.Lang.Types
import SPLL.Typing.PType
import SPLL.Typing.RType
import qualified Data.Set as Set


import qualified Data.Map as Map
import Control.Applicative (liftA2)
import Control.Monad.Random.Lazy (Random)
import Data.Number.Erf (Erf)


toStub :: Expr -> ExprStub
toStub expr = case expr of
  IfThenElse {}  -> StubIfThenElse
  GreaterThan {} -> StubGreaterThan
  LessThan {}    -> StubLessThan
  (ThetaI _ _ _)   -> StubThetaI
  (Subtree _ _ _)   -> StubSubtree
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
  Apply {}  -> StubApply
  (ReadNN _ _ _) -> StubReadNN



tInfoMap :: (a -> b) -> TypeInfo -> TypeInfo
tInfoMap f t = undefined

exprMap :: (a -> b) -> Expr -> Expr
exprMap f expr = case expr of
  (IfThenElse t a b c) -> IfThenElse (tInfoMap f t) (exprMap f b) (exprMap f b) (exprMap f c)
  (GreaterThan t a b) -> GreaterThan (tInfoMap f t) (exprMap f a) (exprMap f b)
  (LessThan t a b) -> LessThan (tInfoMap f t) (exprMap f a) (exprMap f b)
  (ThetaI t a x) -> ThetaI (tInfoMap f t) (exprMap f a) x
  (Subtree t a x) -> Subtree (tInfoMap f t) (exprMap f a) x
  (Uniform t) -> Uniform (tInfoMap f t)
  (Normal t) -> Normal (tInfoMap f t)
  (Constant t x) -> Constant (tInfoMap f t) x
  (And t a b) -> And (tInfoMap f t) (exprMap f a) (exprMap f b)
  (Or t a b) -> Or (tInfoMap f t) (exprMap f a) (exprMap f b)
  (Not t a) -> Not (tInfoMap f t) (exprMap f a)
  (Null t) -> Null (tInfoMap f t)
  (Cons t a b) -> Cons (tInfoMap f t) (exprMap f a) (exprMap f b)
  (TCons t a b) -> TCons (tInfoMap f t) (exprMap f a) (exprMap f b)
  (Var t x) -> Var (tInfoMap f t) x
  (LetIn t x a b) -> LetIn (tInfoMap f t) x (exprMap f a) (exprMap f b)
  (InjF t x a) -> InjF (tInfoMap f t) x (map (exprMap f) a)
  --(LetInD t x a b) -> LetInD t x (exprMap f a) (exprMap f b)
  --(LetInTuple t x a b c) -> LetInTuple t x (exprMap f a) (biFMap f b) (exprMap f c)
  (Lambda t name a) -> Lambda (tInfoMap f t) name (exprMap f a)
  (Apply t a b) -> Apply (tInfoMap f t) (exprMap f a) (exprMap f b)
  (ReadNN t n a) -> ReadNN (tInfoMap f t) n (exprMap f a)
  
predicateFlat :: (Expr -> Bool) -> Expr -> Bool
predicateFlat f e = f e && all (predicateFlat f) (getSubExprs e)

containedVars :: (Expr -> Set.Set String) -> Expr -> Set.Set String
containedVars f e = Set.union (f e) (foldl Set.union Set.empty (map (containedVars f) (getSubExprs e)))

predicateProg :: (Expr -> Bool) -> Program -> Bool
predicateProg f (Program decls _) = and (map (predicateExpr f . snd) decls)

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
--  (ReadNN _ a) -> ReadNN (f expr) a

tMapTails :: (Expr -> TypeInfo) -> Expr -> Expr
tMapTails f expr = case expr of
  (IfThenElse t a b c) -> IfThenElse t (tMap f a) (tMap f b) (tMap f c)
  (GreaterThan t a b) -> GreaterThan t (tMap f a) (tMap f b)
  (LessThan t a b) -> LessThan t (tMap f a) (tMap f b)
  (ThetaI t a x) -> ThetaI t (tMap f a) x
  (Subtree t a x) -> Subtree t (tMap f a) x
  (Uniform t) -> Uniform t
  (Normal t) -> Normal t
  (Constant t x) -> Constant t x
  (And t a b) -> And t (tMap f a) (tMap f b)
  (Or t a b) -> Or t (tMap f a) (tMap f b)
  (Not t a) -> Not t (tMap f a)
  (Null t) -> Null t
  (Cons t a b) -> Cons t (tMap f a) (tMap f b)
  (TCons t a b) -> TCons t (tMap f a) (tMap f b)
  (Var t x) -> Var t x
  (LetIn t x a b) -> LetIn t x (tMap f a) (tMap f b)
  (InjF t x a) -> InjF t x (map (tMap f) a)
  --(LetInD t x a b) -> LetInD t x (tMap f a) (tMap f b)
  --(LetInTuple t x a b c) -> LetInTuple t x (tMap f a) b (tMap f c)
  (Lambda t name a) -> Lambda t name (tMap f a)
  (Apply t a b) -> Apply t (tMap f a) (tMap f b)

tMap :: (Expr -> TypeInfo) -> Expr -> Expr
tMap f expr = case expr of 
  (IfThenElse _ a b c) -> IfThenElse (f expr) (tMap f a) (tMap f b) (tMap f c)
  (GreaterThan _ a b) -> GreaterThan (f expr) (tMap f a) (tMap f b)
  (LessThan _ a b) -> LessThan (f expr) (tMap f a) (tMap f b)
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

makeMain :: Expr -> Program
makeMain expr = Program [("main", expr)] []

tMapProg :: (Expr -> TypeInfo) -> Program -> Program
tMapProg f (Program decls neural) = Program (zip (map fst decls) (map (tMap f . snd) decls)) neural

getBinaryConstructor :: Expr -> (TypeInfo -> Expr -> Expr -> Expr)
getBinaryConstructor GreaterThan {} = GreaterThan
getBinaryConstructor LessThan {} = LessThan
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

tTraverse :: Applicative f => (TypeInfo -> f TypeInfo) -> Expr -> f Expr
tTraverse f expr = fmap (\t -> setTypeInfo expr t) typeinfos
  where typeinfos = f $ getTypeInfo expr

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

arity :: Expr -> Int
arity e = length $ getSubExprs e

getSubExprs :: Expr -> [Expr]
getSubExprs expr = case expr of 
  (IfThenElse _ a b c) -> [a,b,c]
  (GreaterThan _ a b) -> [a,b]
  (LessThan _ a b) -> [a,b]
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

setSubExprs :: Expr -> [Expr] -> Expr
setSubExprs expr [] = case expr of
  Uniform t -> Uniform t
  Normal t -> Normal t
  Constant t x -> Constant t x
  Null t -> Null t
  Var t x -> Var t x
  InjF t n _ -> InjF t n []
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
  And t _ _ -> And t a b
  Or t _ _ -> Or t a b
  Cons t _ b -> Cons t a b
  TCons t _ b -> TCons t a b
  LetIn t x _ b -> LetIn t x a b
  Apply t _ _ -> Apply t a b
  InjF t n _ -> InjF t n [a, b]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a,b,c] = case expr of
  IfThenElse t _ _ _ -> IfThenElse t a b c
  InjF t n _ -> InjF t n [a, b, c]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr subExprs = case expr of
  InjF t l _ -> InjF t l subExprs
  InjF t n _ -> InjF t n subExprs
  _ -> error "unmatched expr in setSubExprs"

getTypeInfo :: Expr -> TypeInfo
getTypeInfo expr = case expr of
  (IfThenElse t _ _ _)  -> t
  (GreaterThan t _ _)   -> t
  (LessThan t _ _)      -> t
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
  (Apply t _ _)    -> t
  (ReadNN t _ _)        -> t
  
setTypeInfo :: Expr -> TypeInfo -> Expr
setTypeInfo expr t = case expr of
  (IfThenElse _ a b c)  -> IfThenElse t a b c
  (GreaterThan _ a b)   -> GreaterThan t a b
  (LessThan _ a b)      -> LessThan t a b
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

constructVList :: [GenericValue a] -> GenericValue a
constructVList xs = VList $ foldr ListCont EmptyList xs

elementAt :: ValueList a -> Int -> GenericValue a
elementAt (ListCont x _) 0 = x
elementAt (ListCont _ xs) i = elementAt xs (i-1)
elementAt EmptyList _ = error "Index out of bounds"
elementAt AnyList _ = error "Cannot iterate AnyLists"

getVFloat :: Value -> Double
getVFloat (VFloat v) = v
getVFloat _ = error "not vfloat where it should be"

getRType :: Value -> RType
getRType (VBool _) = TBool
getRType (VInt _) = TInt
getRType (VSymbol _) = TSymbol
getRType (VFloat _) = TFloat
getRType (VList (ListCont a _)) = ListOf $ getRType a
getRType (VList EmptyList) = NullList
getRType (VTuple t1 t2) = Tuple (getRType t1) (getRType t2)
getRType (VEither (Left a)) = TEither (getRType a) SPLL.Typing.RType.NotSetYet 

getFunctionNames :: Program -> [String]
getFunctionNames p = map fst (functions p)

prettyPrintProg :: Program -> [String]
prettyPrintProg = prettyPrintProgCustomTI prettyFullTypeInfo

prettyPrintProgRTyOnly :: Program -> [String]
prettyPrintProgRTyOnly = prettyPrintProgCustomTI prettyRTypeOnly

prettyPrintProgCustomTI :: (TypeInfo -> String) -> Program -> [String]
prettyPrintProgCustomTI fn (Program decls neurals) = concatMap (prettyPrintDecl fn) decls ++ concatMap prettyPrintNeural neurals

prettyPrintNeural :: NeuralDecl -> [String]
prettyPrintNeural (name, ty, range) = l1:l2:(l3 range):[]
  where
    l1 = ("--- Neural: " ++ name ++ "---")
    l2 = ("\t :: " ++ show ty)
    l3 (Just (EnumList lst)) = ("\t" ++ (show $ length lst))
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

prettyPrintNoReq :: Expr -> [String]
prettyPrintNoReq expr =
  fstLine : indented
    where
      childExprs = getSubExprs expr
      indented = map indent $ concatMap prettyPrintNoReq childExprs :: [String]
      indent ls = "    " ++ ls
      fstLine = printFlatNoReq expr

prettyPrintProgNoReq :: Program -> [String]
prettyPrintProgNoReq (Program fdecls ndecls) = concatMap prettyPrintDeclNoReq fdecls ++ concatMap prettyPrintNeuralNoReq ndecls

prettyPrintNeuralNoReq :: NeuralDecl -> [String]
prettyPrintNeuralNoReq (name, ty, range) = l1:l2:(l3 range):[]
  where
    l1 = ("--- Neural: " ++ name ++ "---")
    l2 = ("\t :: " ++ show ty)
    l3 (Just (EnumList lst)) = ("\t" ++ (show $ length lst))
    l3 (Nothing) = ("\t" ++ (show $ 0))
    l3 _ = "prettyprint not implemented"


prettyPrintDeclNoReq :: FnDecl -> [String]
prettyPrintDeclNoReq (name, expr) = ("--- Function: " ++ name ++ "---"):prettyPrintNoReq expr

printFlat :: Expr -> String
printFlat expr = case expr of
  IfThenElse {} -> "IfThenElse"
  GreaterThan {} -> "GreaterThan"
  LessThan {} -> "LessThan"
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

printFlatNoReq :: Expr -> String
printFlatNoReq expr = case expr of
  IfThenElse {} -> "IfThenElse"
  GreaterThan {} -> "GreaterThan"
  LessThan {} -> "LessThan"
  (ThetaI _ _ i) -> "Theta_" ++ show i
  (Subtree _ _ i) -> "Subtree_" ++ show i
  Uniform {} -> "Uniform"
  Normal {} -> "Normal"
  (Constant _ _) -> "Constant"
  And {} -> "And"
  Or {} -> "Or"
  Not {} -> "Not"
  (Null _) -> "Null"
  Cons {} -> "Cons"
  TCons {} -> "TCons"
  Var _ _ -> "Var"
  LetIn {} -> "LetIn"
  (InjF t fname _) -> "InjF (" ++ fname ++ ")"
  --(LetInD {}) -> "LetInD"
  --(LetInTuple {}) -> "LetInTuple"
  (Lambda _ name _) -> "\\" ++ name  ++ " -> "
  Apply {} -> "Apply"
  ReadNN {} -> "ReadNN"
  
