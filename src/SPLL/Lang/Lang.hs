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
, tMapHead
, getRType
, Name
, Limits (..)
, exprMap
, swapLimits
, prettyPrintProg
, prettyPrint
, prettyPrintProgNoReq
, getVFloat
, checkLimits
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
) where

import SPLL.Lang.Types
import SPLL.Typing.PType
import SPLL.Typing.RType
import qualified Data.Set as Set


import qualified Data.Map as Map
import Control.Applicative (liftA2)
import Control.Monad.Random.Lazy (Random)
import Data.Number.Erf (Erf)


toStub :: Expr a -> ExprStub
toStub expr = case expr of
  IfThenElse {}  -> StubIfThenElse
  GreaterThan {} -> StubGreaterThan
  LessThan {}    -> StubLessThan
  (ThetaI _ _ _)   -> StubThetaI
  (Subtree _ _ _)   -> StubSubtree
  (Uniform _)    -> StubUniform
  (Normal _)     -> StubNormal
  (Constant _ _) -> StubConstant
  MultF {}       -> StubMultF
  MultI {}       -> StubMultI
  PlusF {}       -> StubPlusF
  PlusI {}       -> StubPlusI
  ExpF {}        -> StubExpF
  NegF {}        -> StubNegF
  Not {}         -> StubNot
  (Null _)       -> StubNull
  Cons {}        -> StubCons
  TCons {}       -> StubTCons
  (Call _ _)     -> StubCall
  (Var _ _)      -> StubVar
  LetIn {}       -> StubLetIn
  Arg {}         -> StubArg
  InjF {}        -> StubInjF
  CallArg {}     -> StubCallArg
  Lambda {}      -> StubLambda
  Apply {}  -> StubApply
  (ReadNN _ _ _) -> StubReadNN

vMarg :: Value a
vMarg = VRange (Limits Nothing Nothing)

checkLimits :: (Ord a) => Limits a -> Bool
checkLimits (Limits (Just (VFloat x)) (Just (VFloat y))) = x < y
checkLimits (Limits (Just (VFloat _)) Nothing) = True
checkLimits (Limits Nothing (Just (VFloat _))) = True
checkLimits (Limits Nothing Nothing) = True
checkLimits _ = False

swapLimits :: Value a -> Value a
swapLimits (VRange (Limits a b)) = VRange (Limits b a)
swapLimits _ = error "swapLimits on non-range"

tInfoMap :: (a -> b) -> TypeInfo a -> TypeInfo b
tInfoMap f t = undefined

exprMap :: (a -> b) -> Expr a -> Expr b
exprMap f expr = case expr of
  (IfThenElse t a b c) -> IfThenElse (tInfoMap f t) (exprMap f b) (exprMap f b) (exprMap f c)
  (GreaterThan t a b) -> GreaterThan (tInfoMap f t) (exprMap f a) (exprMap f b)
  (LessThan t a b) -> LessThan (tInfoMap f t) (exprMap f a) (exprMap f b)
  (ThetaI t a x) -> ThetaI (tInfoMap f t) (exprMap f a) x
  (Subtree t a x) -> Subtree (tInfoMap f t) (exprMap f a) x
  (Uniform t) -> Uniform (tInfoMap f t)
  (Normal t) -> Normal (tInfoMap f t)
  (Constant t x) -> Constant (tInfoMap f t) $ fmap f x
  (MultF t a b) -> MultF (tInfoMap f t) (exprMap f a) (exprMap f b)
  (MultI t a b) -> MultI (tInfoMap f t) (exprMap f a) (exprMap f b)
  (PlusF t a b) -> PlusF (tInfoMap f t) (exprMap f a) (exprMap f b)
  (PlusI t a b) -> PlusI (tInfoMap f t) (exprMap f a) (exprMap f b)
  (ExpF t a) -> ExpF (tInfoMap f t) (exprMap f a)
  (NegF t a) -> NegF (tInfoMap f t) (exprMap f a)
  (And t a b) -> And (tInfoMap f t) (exprMap f a) (exprMap f b)
  (Or t a b) -> Or (tInfoMap f t) (exprMap f a) (exprMap f b)
  (Not t a) -> Not (tInfoMap f t) (exprMap f a)
  (Null t) -> Null (tInfoMap f t)
  (Cons t a b) -> Cons (tInfoMap f t) (exprMap f a) (exprMap f b)
  (TCons t a b) -> TCons (tInfoMap f t) (exprMap f a) (exprMap f b)
  (Call t x) -> Call (tInfoMap f t) x
  (Var t x) -> Var (tInfoMap f t) x
  (LetIn t x a b) -> LetIn (tInfoMap f t) x (exprMap f a) (exprMap f b)
  (InjF t x a) -> InjF (tInfoMap f t) x (map (exprMap f) a)
  --(LetInD t x a b) -> LetInD t x (exprMap f a) (exprMap f b)
  --(LetInTuple t x a b c) -> LetInTuple t x (exprMap f a) (biFMap f b) (exprMap f c)
  (Arg t name r a) -> Arg (tInfoMap f t) name r (exprMap f a)
  (CallArg t name a) -> CallArg (tInfoMap f t) name (map (exprMap f) a)
  (Lambda t name a) -> Lambda (tInfoMap f t) name (exprMap f a)
  (Apply t a b) -> Apply (tInfoMap f t) (exprMap f a) (exprMap f b)
  (ReadNN t n a) -> ReadNN (tInfoMap f t) n (exprMap f a)
  
predicateFlat :: (Expr a -> Bool) -> Expr a -> Bool
predicateFlat f e = f e && all (predicateFlat f) (getSubExprs e)

containedVars :: (Expr a -> Set.Set String) -> Expr a -> Set.Set String
containedVars f e = Set.union (f e) (foldl Set.union Set.empty (map (containedVars f) (getSubExprs e)))

predicateProg :: (Expr a -> Bool) -> Program a -> Bool
predicateProg f (Program decls expr) = and (map (predicateExpr f . snd) decls) && predicateExpr f expr

predicateExpr :: (Expr a -> Bool) -> Expr a -> Bool
predicateExpr f e = f e && and (map (predicateExpr f) (getSubExprs e))

varsOfExpr :: Expr a -> Set.Set String
varsOfExpr expr = case expr of
  (Var _ name) -> Set.singleton name
  _ -> Set.empty

isNotTheta :: Expr a -> Bool
isNotTheta expr = case expr of
  (ThetaI _ _ name) -> False
  _ -> True
  
tMapHead :: (Expr a -> (TypeInfo a)) -> Expr a -> Expr a
tMapHead f expr = case expr of 
  (IfThenElse _ a b c) -> IfThenElse (f expr) a b c
  (GreaterThan _ a b) -> GreaterThan (f expr) a b
  (LessThan _ a b) -> LessThan (f expr) a b
  (ThetaI _ a x) -> ThetaI (f expr) a x
  (Subtree _ a x) -> Subtree (f expr) a x
  (Uniform _) -> Uniform (f expr)
  (Normal _) -> Normal (f expr)
  (Constant _ x) -> Constant (f expr) x
  (MultF _ a b) -> MultF (f expr) a b
  (MultI _ a b) -> MultI (f expr) a b
  (PlusF _ a b) -> PlusF (f expr) a b
  (PlusI _ a b) -> PlusI (f expr) a b
  (ExpF _ a) -> ExpF(f expr) a
  (NegF _ a) -> NegF (f expr) a
  (And _ a b) -> And (f expr) a b
  (Or _ a b) -> Or (f expr) a b
  (Not _ a) -> Not (f expr) a
  (Null _) -> Null (f expr)
  (Cons _ a b) -> Cons (f expr) a b
  (TCons _ a b) -> TCons (f expr) a b
  (Call _ x) -> Call (f expr) x
  (Var _ x) -> Var (f expr) x
  (LetIn _ x a bi) -> LetIn (f expr) x a bi
  (InjF _ x a) -> InjF (f expr) x a
  --(LetInD t x a b) -> LetInD (f expr) x a b
  --(LetInTuple t x a b c) -> LetInTuple (f expr) x a b c
  (Arg _ name r a) -> Arg (f expr) name r a
  (CallArg _ name a) -> CallArg (f expr) name a
  (Lambda _ name a) -> Lambda (f expr) name a
  (Apply _ a b) -> Apply (f expr) a b
--  (ReadNN _ a) -> ReadNN (f expr) a

tMapTails :: (Expr a -> (TypeInfo a)) -> Expr a -> Expr a
tMapTails f expr = case expr of
  (IfThenElse t a b c) -> IfThenElse t (tMap f a) (tMap f b) (tMap f c)
  (GreaterThan t a b) -> GreaterThan t (tMap f a) (tMap f b)
  (LessThan t a b) -> LessThan t (tMap f a) (tMap f b)
  (ThetaI t a x) -> ThetaI t (tMap f a) x
  (Subtree t a x) -> Subtree t (tMap f a) x
  (Uniform t) -> Uniform t
  (Normal t) -> Normal t
  (Constant t x) -> Constant t x
  (MultF t a b) -> MultF t (tMap f a) (tMap f b)
  (MultI t a b) -> MultI t (tMap f a) (tMap f b)
  (PlusF t a b) -> PlusF t (tMap f a) (tMap f b)
  (PlusI t a b) -> PlusI t (tMap f a) (tMap f b)
  (ExpF t a) -> ExpF t (tMap f a)
  (NegF t a) -> NegF t (tMap f a)
  (And t a b) -> And t (tMap f a) (tMap f b)
  (Or t a b) -> Or t (tMap f a) (tMap f b)
  (Not t a) -> Not t (tMap f a)
  (Null t) -> Null t
  (Cons t a b) -> Cons t (tMap f a) (tMap f b)
  (TCons t a b) -> TCons t (tMap f a) (tMap f b)
  (Call t x) -> Call t x
  (Var t x) -> Var t x
  (LetIn t x a b) -> LetIn t x (tMap f a) (tMap f b)
  (InjF t x a) -> InjF t x (map (tMap f) a)
  --(LetInD t x a b) -> LetInD t x (tMap f a) (tMap f b)
  --(LetInTuple t x a b c) -> LetInTuple t x (tMap f a) b (tMap f c)
  (Arg t name r a) -> Arg t name r (tMap f a)
  (Lambda t name a) -> Lambda t name (tMap f a)
  (Apply t a b) -> Apply t (tMap f a) (tMap f b)
  (CallArg t name a) -> CallArg t name (map (tMap f) a)

tMap :: (Expr a -> (TypeInfo a)) -> Expr a -> Expr a
tMap f expr = case expr of 
  (IfThenElse _ a b c) -> IfThenElse (f expr) (tMap f a) (tMap f b) (tMap f c)
  (GreaterThan _ a b) -> GreaterThan (f expr) (tMap f a) (tMap f b)
  (LessThan _ a b) -> LessThan (f expr) (tMap f a) (tMap f b)
  (ThetaI _ a x) -> ThetaI (f expr) (tMap f a) x
  (Subtree _ a x) -> Subtree (f expr) (tMap f a) x
  (Uniform _) -> Uniform (f expr)
  (Normal _) -> Normal (f expr)
  (Constant _ x) -> Constant (f expr) x
  (MultF _ a b) -> MultF (f expr) (tMap f a) (tMap f b)
  (MultI _ a b) -> MultF (f expr) (tMap f a) (tMap f b)
  (PlusF _ a b) -> PlusF (f expr) (tMap f a) (tMap f b)
  (PlusI _ a b) -> PlusI (f expr) (tMap f a) (tMap f b)
  (ExpF _ a) -> ExpF (f expr) (tMap f a) 
  (NegF _ a) -> NegF (f expr) (tMap f a)
  (And _ a b) -> And (f expr) (tMap f a) (tMap f b)
  (Or _ a b) -> Or (f expr) (tMap f a) (tMap f b)
  (Not _ a) -> Not (f expr) (tMap f a)
  (Null _) -> Null (f expr)
  (Cons _ a b) -> Cons (f expr) (tMap f a) (tMap f b)
  (TCons _ a b) -> TCons (f expr) (tMap f a) (tMap f b)
  (Call _ x) -> Call (f expr) x
  (Var _ x) -> Var (f expr) x
  (LetIn _ x a b) -> LetIn (f expr) x (tMap f a) (tMap f b)
  (InjF t x a) -> InjF (f expr) x (map (tMap f) a)
  --(LetInD t x a b) -> LetInD (f expr) x (tMap f a) (tMap f b)
  --(LetInTuple t x a b c) -> LetInTuple (f expr) x (tMap f a) b (tMap f c)
  (Arg _ name r a) -> Arg (f expr) name r (tMap f a)
  (CallArg _ name a) -> CallArg (f expr) name (map (tMap f) a)
  (Lambda _ name a) -> Lambda (f expr) name (tMap f a)
  (Apply _ a b) -> Apply (f expr) (tMap f a) (tMap f b)
  (ReadNN _ n a) -> ReadNN (f expr) n (tMap f a)

tMapProg :: (Expr a -> (TypeInfo a)) -> Program a -> Program a
tMapProg f (Program decls expr) = Program (zip (map fst decls) (map (tMap f . snd) decls)) (tMap f expr)

getBinaryConstructor :: Expr a1 -> ((TypeInfo a2) -> Expr a2 -> Expr a2 -> Expr a2)
getBinaryConstructor GreaterThan {} = GreaterThan
getBinaryConstructor LessThan {} = GreaterThan
getBinaryConstructor MultF {} = MultF
getBinaryConstructor MultI {} = MultI
getBinaryConstructor PlusF {} = PlusF
getBinaryConstructor PlusI {} = PlusI
getBinaryConstructor Cons {} = Cons
getBinaryConstructor TCons {} = TCons
getBinaryConstructor And {} = And
getBinaryConstructor Or {} = Or
getBinaryConstructor Apply {} = Apply
--getBinaryConstructor (LetIn t name a b) = \t2 -> \e1 -> \e2 -> LetIn t2 name e1 e2
getBinaryConstructor (LetIn _ name _ _) = (`LetIn` name)

getUnaryConstructor :: Expr a1 -> (TypeInfo a2 -> Expr a2 -> Expr a2)
getUnaryConstructor (ThetaI _ _ i) = \t a -> ThetaI t a i
getUnaryConstructor (Subtree _ _ i) = \t a -> Subtree t a i
getUnaryConstructor (Lambda _ x _) = (`Lambda` x)
getUnaryConstructor (ReadNN _ x _) = (`ReadNN` x)
getUnaryConstructor (Fix _ _) = Fix
getUnaryConstructor (Not _ _) = Not
getUnaryConstructor (ExpF _ _) = ExpF

getNullaryConstructor :: Expr a -> (TypeInfo a -> Expr a)
getNullaryConstructor Uniform {} = Uniform
getNullaryConstructor Normal {} = Normal
getNullaryConstructor (Constant t val) = (`Constant` val)
getNullaryConstructor Null {} = Null
getNullaryConstructor (Var _ x) = (`Var` x)
getNullaryConstructor (Call _ x) = (`Call` x)

tTraverse :: Applicative f => (TypeInfo v -> f (TypeInfo v)) -> Expr v -> f (Expr v)
tTraverse f expr = fmap (\t -> setTypeInfo expr t) typeinfos
  where typeinfos = f $ getTypeInfo expr

tMapM :: Monad m => (Expr a -> m (TypeInfo a)) -> Expr a -> m (Expr a)
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

arity :: Expr a -> Int
arity e = length $ getSubExprs e

getSubExprs :: Expr a -> [Expr a]
getSubExprs expr = case expr of 
  (IfThenElse _ a b c) -> [a,b,c]
  (GreaterThan _ a b) -> [a,b]
  (LessThan _ a b) -> [a,b]
  (ThetaI _ a _) -> [a]
  (Subtree _ a _) -> [a]
  (Uniform _) -> []
  (Normal _) -> []
  (Constant _ _) -> []
  (MultF _ a b) -> [a,b]
  (MultI _ a b) -> [a,b]
  (PlusF _ a b) -> [a,b]
  (PlusI _ a b) -> [a,b]
  (ExpF _ a) -> [a]
  (NegF _ a) -> [a]
  (And _ a b) -> [a,b]
  (Or _ a b) -> [a,b]
  (Not _ a) -> [a]
  (Null _) -> []
  (Cons _ a b) -> [a,b]
  (TCons _ a b) -> [a,b]
  (Call _ _) -> []
  (LetIn _ _ a b) -> [a, b]
  (Var _ _) -> []
  (InjF _ _ a) -> a
  --(LetInD t x a b) -> [a,b]
  --(LetInTuple t x a b c) -> [a,c]
  (Arg _ _ _ a) -> [a]
  (CallArg _ _ a) -> a
  (Lambda _ _ a) -> [a]
  (Apply _ a b) -> [a, b]
  (ReadNN _ _ a) -> [a]

setSubExprs :: Expr a -> [Expr a] -> Expr a
setSubExprs expr [] = case expr of
  Uniform t -> Uniform t
  Normal t -> Normal t
  Constant t x -> Constant t x
  Null t -> Null t
  Call t x -> Call t x
  Var t x -> Var t x
  CallArg t n _ -> CallArg t n []
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a] = case expr of
  ThetaI t _ x -> ThetaI t a x
  Subtree t _ x -> Subtree t a x
  Arg t l n _ -> Arg t l n a
  Lambda t l _ -> Lambda t l a
  ExpF t _ -> ExpF t a
  NegF t _ -> NegF t a
  Not t _ -> Not t a
  ReadNN t n _ -> ReadNN t n a
  CallArg t n _ -> CallArg t n [a]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a,b] = case expr of
  GreaterThan t _ _ -> GreaterThan t a b
  LessThan t _ _ -> LessThan t a b
  MultF t _ _ -> MultF t a b
  MultI t _ _ -> MultI t a b
  PlusF t _ _ -> PlusF t a b
  PlusI t _ _ -> PlusI t a b
  And t _ _ -> And t a b
  Or t _ _ -> Or t a b
  Cons t _ b -> Cons t a b
  TCons t _ b -> TCons t a b
  LetIn t x _ b -> LetIn t x a b
  CallArg t n _ -> CallArg t n [a,b]
  Apply t _ _ -> Apply t a b
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a,b,c] = case expr of
  IfThenElse t _ _ _ -> IfThenElse t a b c
  CallArg t n _ -> CallArg t n [a,b,c]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr subExprs = case expr of
  InjF t l _ -> InjF t l subExprs
  CallArg t n _ -> CallArg t n subExprs
  _ -> error "unmatched expr in setSubExprs"

getTypeInfo :: Expr a -> TypeInfo a
getTypeInfo expr = case expr of
  (IfThenElse t _ _ _)  -> t
  (GreaterThan t _ _)   -> t
  (LessThan t _ _)      -> t
  (ThetaI t _ _)        -> t
  (Subtree t _ _)       -> t
  (Uniform t)           -> t
  (Normal t)            -> t
  (Constant t _)        -> t
  (MultF t _ _)         -> t
  (MultI t _ _)         -> t
  (PlusF t _ _)         -> t
  (PlusI t _ _)         -> t
  (ExpF t _)            -> t
  (NegF t _)            -> t
  (And t _ _)           -> t
  (Or t _ _)            -> t
  (Not t _)             -> t
  (Null t)              -> t
  (Cons t _ _)          -> t
  (TCons t _ _)         -> t
  (Call t _)            -> t
  (Var t _)             -> t
  (LetIn t _ _ _)       -> t
  (InjF t _ _)          -> t
  --(LetInD t _ _ _)      -> t
  --(LetInTuple t _ _ _ _)-> t
  (Arg t _ _ _)         -> t
  (CallArg t _ _)       -> t
  (Lambda t _ _)        -> t
  (Apply t _ _)    -> t
  (ReadNN t _ _)        -> t
  
setTypeInfo :: Expr a -> TypeInfo a -> Expr a
setTypeInfo expr t = case expr of
  (IfThenElse _ a b c)  -> (IfThenElse t a b c)
  (GreaterThan _ a b)   -> (GreaterThan t a b)
  (LessThan _ a b)      -> (LessThan t a b)
  (ThetaI _ a b)        -> (ThetaI t a b)
  (Subtree _ a b)       -> (Subtree t a b)
  (Uniform _)           -> (Uniform t)
  (Normal _)            -> (Normal t)
  (Constant _ a)        -> (Constant t a)
  (MultF _ a b)         -> (MultF t a b)
  (MultI _ a b)         -> (MultI t a b)
  (PlusF _ a b)         -> (PlusF t a b)
  (PlusI _ a b)         -> (PlusI t a b)
  (ExpF _ a)            -> (ExpF t a)
  (NegF _ a)            -> (NegF t a)
  (And _ a b)           -> (And t a b)
  (Or _ a b)            -> (Or t a b)
  (Not _ a)             -> (Not t a)
  (Null _)              -> (Null t)
  (Cons _ a b)          -> (Cons t a b)
  (TCons _ a b)         -> (TCons t a b)
  (Call _ a)            -> (Call t a)
  (Var _ a)             -> (Var t a)
  (LetIn _ a b c)       -> (LetIn t a b c)
  (InjF _ a b)          -> (InjF t a b)
  --(LetInD _ a b c)     -> (LetInD t a b c)
  --(LetInTuple _ a b c d) -> (LetInTuple t a b c d)
  (Arg _ a b c)         -> (Arg t a b c)
  (CallArg _ a b)       -> (CallArg t a b)
  (Lambda _ a b)        -> (Lambda t a b)
  (Apply _ a b)    -> (Apply t a b)
  (ReadNN _ a b)        -> (ReadNN t a b)

getVFloat :: Value a -> a
getVFloat (VFloat v) = v
getVFloat _ = error "not vfloat where it should be"

getRType :: Value a -> RType
getRType (VBool _) = TBool
getRType (VInt _) = TInt
getRType (VSymbol _) = TSymbol
getRType (VFloat _) = TFloat
getRType (VList (a:_)) = ListOf $ getRType a
getRType (VList []) = NullList
getRType (VTuple t1 t2) = Tuple (getRType t1) (getRType t2)

prettyPrintProg :: (Num a, Show a) => Program a -> [String]
prettyPrintProg (Program decls expr) = concatMap prettyPrintDecl decls ++ mainString
  where mainString = ("--- Main Expression ---"):(prettyPrint expr:: [String])

prettyPrintDecl :: (Num a, Show a) => Decl a -> [String]
prettyPrintDecl (name, expr) = ("--- Function: " ++ name ++ "---"):prettyPrint expr

prettyPrint :: (Num a, Show a) => Expr a -> [String]
prettyPrint expr = 
  fstLine : indented
    where
      childExprs = getSubExprs expr
      indented = map indent $ concatMap prettyPrint childExprs :: [String]
      indent ls = "    " ++ ls
      fstLine = printFlat expr ++ " :: (" ++ show (getTypeInfo expr) ++ ")"

prettyPrintNoReq :: Expr a -> [String]
prettyPrintNoReq expr =
  fstLine : indented
    where
      childExprs = getSubExprs expr
      indented = map indent $ concatMap prettyPrintNoReq childExprs :: [String]
      indent ls = "    " ++ ls
      fstLine = printFlatNoReq expr

prettyPrintProgNoReq ::Program a -> [String]
prettyPrintProgNoReq (Program decls expr) = concatMap prettyPrintDeclNoReq decls ++ mainString
  where mainString = ("--- Main Expression ---"):(prettyPrintNoReq expr:: [String])

prettyPrintDeclNoReq ::Decl a -> [String]
prettyPrintDeclNoReq (name, expr) = ("--- Function: " ++ name ++ "---"):prettyPrintNoReq expr

printFlat :: Show a => Expr a -> String
printFlat expr = case expr of
  IfThenElse {} -> "IfThenElse"
  GreaterThan {} -> "GreaterThan"
  LessThan {} -> "LessThan"
  (ThetaI _ _ i) -> "Theta_" ++ show i
  (Subtree _ _ i) -> "Subtree_" ++ show i
  Uniform {} -> "Uniform"
  Normal {} -> "Normal"
  (Constant _ x) -> "Constant (" ++ show x ++ ")"
  MultF {} -> "MultF"
  MultI {} -> "MultI"
  PlusF {} -> "PlusF"
  PlusI {} -> "PlusI"
  ExpF {} -> "ExpF"
  NegF {} -> "NegF"
  And {} -> "And"
  Or {} -> "Or"
  Not {} -> "Not"
  (Null _) -> "Null"
  Cons {} -> "Cons"
  TCons {} -> "TCons"
  (Call _ a) -> "Call " ++ a
  (Var _ a) -> "Var " ++ a
  LetIn {} -> "LetIn"
  --(LetInD {}) -> "LetInD"
  --(LetInTuple {}) -> "LetInTuple"
  (InjF t _ _)        -> "InjF"
  (Arg _ var r _ ) -> "Bind " ++ var ++ "::" ++ show r
  (CallArg _ a _ ) -> "CallArg " ++ a
  (Lambda _ name _) -> "\\" ++ name  ++ " -> "
  Apply {} -> "CallLambda"
  (ReadNN _ name _) -> "ReadNN " ++ name

printFlatNoReq :: Expr a -> String
printFlatNoReq expr = case expr of
  IfThenElse {} -> "IfThenElse"
  GreaterThan {} -> "GreaterThan"
  LessThan {} -> "LessThan"
  (ThetaI _ _ i) -> "Theta_" ++ show i
  (Subtree _ _ i) -> "Subtree_" ++ show i
  Uniform {} -> "Uniform"
  Normal {} -> "Normal"
  (Constant _ _) -> "Constant"
  MultF {} -> "MultF"
  MultI {} -> "MultI"
  PlusF {} -> "PlusF"
  PlusI {} -> "PlusI"
  ExpF {} -> "ExpF"
  NegF {} -> "NegF"
  And {} -> "And"
  Or {} -> "Or"
  Not {} -> "Not"
  (Null _) -> "Null"
  Cons {} -> "Cons"
  TCons {} -> "TCons"
  (Call _ a) -> "Call " ++ a
  Var _ _ -> "Var"
  LetIn {} -> "LetIn"
  (InjF t _ _) -> "InjF"
  --(LetInD {}) -> "LetInD"
  --(LetInTuple {}) -> "LetInTuple"
  (Arg _ var r _ ) -> "Bind " ++ var ++ "::" ++ show r
  (CallArg _ a _ ) -> "CallArg" ++ a
  (Lambda _ name _) -> "\\" ++ name  ++ " -> "
  Apply {} -> "CallLambda"
  ReadNN {} -> "ReadNN"
  
