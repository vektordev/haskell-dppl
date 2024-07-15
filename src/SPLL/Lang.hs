module SPLL.Lang (
  Expr (..)
, ExprFlip (..)
, unflip
, Value (..)
, Program (..)
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
) where

import SPLL.Typing.PType
import SPLL.Typing.RType
import qualified Data.Set as Set


import qualified Data.Map as Map
import Control.Applicative (liftA2)


--Expr x (a :: Precision)
--data Precision = P32 | P64"
--type family PrecisionType P32 = Float
data Expr x a = IfThenElse x (Expr x a) (Expr x a) (Expr x a)
              | GreaterThan x (Expr x a) (Expr x a)
              | ThetaI x Int
              | Uniform x
              | Normal x
              | Constant x (Value a)
              | MultF x (Expr x a) (Expr x a)
              | MultI x (Expr x a) (Expr x a)
              | PlusF x (Expr x a) (Expr x a)
              | PlusI x (Expr x a) (Expr x a)
              | ExpF x (Expr x a)
              | NegF x (Expr x a)
              | Null x
              | Cons x (Expr x a) (Expr x a)
              | Var x String
              | TCons x (Expr x a) (Expr x a)
              | Call x String 
              --  | LetInD x String (Expr x a) (Expr x a)
              --  | LetInTuple x String (Expr x a) (BijectiveF a) (Expr x a)
              | LetIn x String (Expr x a) (Expr x a)
             -- Change params to expr
              | InjF x String [Expr x a]
              | Arg x String RType (Expr x a)
              | CallArg x String [Expr x a]
              | Lambda x String (Expr x a)
              | ReadNN x String (Expr x a)
              | Fix x (Expr x a)
              -- TODO: Needs Concat to achieve proper SPN-parity.
              deriving (Show, Eq, Ord)

-- Flipped type args newtype on Expr, so we can fmap, foldr, and traverse over types.
newtype ExprFlip x t = ExprFlip (Expr t x)

unflip :: ExprFlip x t -> Expr t x
unflip (ExprFlip x) = x

instance Functor (ExprFlip x) where
  fmap f eflip = ExprFlip $ tMap (\e -> f (getTypeInfo (e))) (unflip eflip)

instance Foldable (ExprFlip x) where
  --foldr :: (t -> b -> b) -> b -> ExprFlip x t -> b
  foldr f accum eflip = f (getTypeInfo $ unflip eflip) subexprfolds
    where
      subexprs = getSubExprs $ unflip eflip
      subexprfolds = foldr unflipf accum subexprs
      -- unflipf :: Expr t x -> b -> b
      -- unflip eflip2 :: Expr
      unflipf eflip2 accum = f (getTypeInfo eflip2) accum

instance Traversable (ExprFlip x) where
  traverse f eflip = fmap ExprFlip traversed
    where
      traversed = tTraverse f unflipped
      unflipped = unflip eflip


type Name = String

data Program x a = Program [Decl x a] (Expr x a) deriving (Show, Eq)

type Decl x a = (String, Expr x a)

type WitnessedVars = Set.Set String

data Value a = VBool Bool
           | VInt Int
           | VSymbol String
           | VFloat a
           | VList [Value a]
           | VTuple (Value a) (Value a)
           | VBranch (Value a) (Value a) String
           | VRange (Limits a)
           | VAnyList 
           -- | Value of TArrow a b could be Expr TypeInfo a, with Expr being a Lambda?
           deriving (Show, Eq, Ord)
-- likelihood [vMarg, vAnyList] - likelihood [vMarg, vMarg, vAnylist]
--Nothing indicates low/high infinity.
data Limits a = Limits (Maybe (Value a)) (Maybe (Value a))
           deriving (Show, Eq, Ord)

instance Functor Value where
  fmap = valMap

valMap :: (a -> b) -> Value a -> Value b
valMap f (VBool b) = VBool b
valMap f (VInt i) = VInt i
valMap f (VSymbol i) = VSymbol i
valMap f (VFloat a) = VFloat $ f a
valMap f (VList v) = VList $ map (valMap f) v
valMap f (VTuple v1 v2) = VTuple (valMap f v1) (valMap f v2)
valMap f (VBranch v1 v2 x ) = VBranch (valMap f v1) (valMap f v2) x
valMap f (VRange v1) = VRange (limitsMap f v1)
valMap f VAnyList = VAnyList

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

limitsMap :: (a -> b) -> Limits a -> Limits b
limitsMap f (Limits a b) = Limits (fmap (valMap f) a) (fmap (valMap f) b)

exprMap :: (a -> b) -> Expr x a -> Expr x b
exprMap f expr = case expr of
  (IfThenElse t a b c) -> IfThenElse t (exprMap f a) (exprMap f b) (exprMap f c)
  (GreaterThan t a b) -> GreaterThan t (exprMap f a) (exprMap f b)
  (ThetaI t x) -> ThetaI t x
  (Uniform t) -> Uniform t
  (Normal t) -> Normal t
  (Constant t x) -> Constant t $ fmap f x
  (MultF t a b) -> MultF t (exprMap f a) (exprMap f b)
  (MultI t a b) -> MultI t (exprMap f a) (exprMap f b)
  (PlusF t a b) -> PlusF t (exprMap f a) (exprMap f b)
  (PlusI t a b) -> PlusI t (exprMap f a) (exprMap f b)
  (ExpF t a) -> ExpF t (exprMap f a)
  (NegF t a) -> NegF t (exprMap f a)
  (Null t) -> Null t
  (Cons t a b) -> Cons t (exprMap f a) (exprMap f b)
  (TCons t a b) -> TCons t (exprMap f a) (exprMap f b)
  (Call t x) -> Call t x
  (Var t x) -> Var t x
  (LetIn t x a b) -> LetIn t x (exprMap f a) (exprMap f b)
  (InjF t x a) -> InjF t x (map (exprMap f) a)
  --(LetInD t x a b) -> LetInD t x (exprMap f a) (exprMap f b)
  --(LetInTuple t x a b c) -> LetInTuple t x (exprMap f a) (biFMap f b) (exprMap f c)
  (Arg t name r a) -> Arg t name r (exprMap f a)
  (CallArg t name a) -> CallArg t name (map (exprMap f) a)
  (Lambda t name a) -> Lambda t name (exprMap f a)
  (ReadNN t n a) -> ReadNN t n (exprMap f a)
  
predicateFlat :: (Expr x a -> Bool) -> Expr x a -> Bool
predicateFlat f e = f e && all (predicateFlat f) (getSubExprs e)

containedVars :: (Expr x a -> Set.Set String) -> Expr x a -> Set.Set String
containedVars f e = Set.union (f e) (foldl Set.union Set.empty (map (containedVars f) (getSubExprs e)))

predicateProg :: (Expr x a -> Bool) -> Program x a -> Bool
predicateProg f (Program decls expr) = and (map (predicateExpr f . snd) decls) && predicateExpr f expr

predicateExpr :: (Expr x a -> Bool) -> Expr x a -> Bool
predicateExpr f e = f e && and (map (predicateExpr f) (getSubExprs e))

varsOfExpr :: Expr x a -> Set.Set String
varsOfExpr expr = case expr of
  (Var _ name) -> Set.singleton name
  _ -> Set.empty

isNotTheta :: Expr x a -> Bool
isNotTheta expr = case expr of
  (ThetaI _ name) -> False
  _ -> True
  
tMapHead :: (Expr x a -> x) -> Expr x a -> Expr x a
tMapHead f expr = case expr of 
  (IfThenElse _ a b c) -> IfThenElse (f expr) a b c
  (GreaterThan _ a b) -> GreaterThan (f expr) a b
  (ThetaI _ x) -> ThetaI (f expr) x
  (Uniform _) -> Uniform (f expr)
  (Normal _) -> Normal (f expr)
  (Constant _ x) -> Constant (f expr) x
  (MultF _ a b) -> MultF (f expr) a b
  (MultI _ a b) -> MultI (f expr) a b
  (PlusF _ a b) -> PlusF (f expr) a b
  (PlusI _ a b) -> PlusI (f expr) a b
  (ExpF _ a) -> ExpF(f expr) a
  (NegF _ a) -> NegF (f expr) a
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
--  (Lambda _ name a) -> CallArg (f expr) name a
--  (ReadNN _ a) -> ReadNN (f expr) a

tMapTails :: (Expr x a -> x) -> Expr x a -> Expr x a
tMapTails f expr = case expr of
  (IfThenElse t a b c) -> IfThenElse t (tMap f a) (tMap f b) (tMap f c)
  (GreaterThan t a b) -> GreaterThan t (tMap f a) (tMap f b)
  (ThetaI t x) -> ThetaI t x
  (Uniform t) -> Uniform t
  (Normal t) -> Normal t
  (Constant t x) -> Constant t x
  (MultF t a b) -> MultF t (tMap f a) (tMap f b)
  (MultI t a b) -> MultI t (tMap f a) (tMap f b)
  (PlusF t a b) -> PlusF t (tMap f a) (tMap f b)
  (PlusI t a b) -> PlusI t (tMap f a) (tMap f b)
  (ExpF t a) -> ExpF t (tMap f a)
  (NegF t a) -> NegF t (tMap f a)
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
  (CallArg t name a) -> CallArg t name (map (tMap f) a)

tMap :: (Expr x a -> y) -> Expr x a -> Expr y a
tMap f expr = case expr of 
  (IfThenElse _ a b c) -> IfThenElse (f expr) (tMap f a) (tMap f b) (tMap f c)
  (GreaterThan _ a b) -> GreaterThan (f expr) (tMap f a) (tMap f b)
  (ThetaI _ x) -> ThetaI (f expr) x
  (Uniform _) -> Uniform (f expr)
  (Normal _) -> Normal (f expr)
  (Constant _ x) -> Constant (f expr) x
  (MultF _ a b) -> MultF (f expr) (tMap f a) (tMap f b)
  (MultI _ a b) -> MultF (f expr) (tMap f a) (tMap f b)
  (PlusF _ a b) -> PlusF (f expr) (tMap f a) (tMap f b)
  (PlusI _ a b) -> PlusI (f expr) (tMap f a) (tMap f b)
  (ExpF _ a) -> ExpF (f expr) (tMap f a) 
  (NegF _ a) -> NegF (f expr) (tMap f a)
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
  (ReadNN _ n a) -> ReadNN (f expr) n (tMap f a)

tMapProg :: (Expr x a -> y) -> Program x a -> Program y a
tMapProg f (Program decls expr) = Program (zip (map fst decls) (map (tMap f . snd) decls)) (tMap f expr)

getBinaryConstructor :: Expr x1 a1 -> (x2 -> Expr x2 a2 -> Expr x2 a2 -> Expr x2 a2)
getBinaryConstructor GreaterThan {} = GreaterThan
getBinaryConstructor MultF {} = MultF
getBinaryConstructor MultI {} = MultI
getBinaryConstructor PlusF {} = PlusF
getBinaryConstructor PlusI {} = PlusI
getBinaryConstructor Cons {} = Cons
getBinaryConstructor TCons {} = TCons
--getBinaryConstructor (LetIn t name a b) = \t2 -> \e1 -> \e2 -> LetIn t2 name e1 e2
getBinaryConstructor (LetIn _ name _ _) = (`LetIn` name)

getUnaryConstructor :: Expr x1 a1 -> (x2 -> Expr x2 a2 -> Expr x2 a2)
getUnaryConstructor (Lambda _ x _) = (`Lambda` x)
getUnaryConstructor (ReadNN _ x _) = (`ReadNN` x)
getUnaryConstructor (Fix _ _) = Fix

getNullaryConstructor :: Expr x1 a -> (x2 -> Expr x2 a)
getNullaryConstructor Uniform {} = Uniform
getNullaryConstructor Normal {} = Normal
getNullaryConstructor (Constant t val) = (`Constant` val)
getNullaryConstructor Null {} = Null
getNullaryConstructor (ThetaI _ x) = (`ThetaI` x)
getNullaryConstructor (Var _ x) = (`Var` x)
getNullaryConstructor (Call _ x) = (`Call` x)

tTraverse :: Applicative f => (a -> f b) -> Expr a v -> f (Expr b v)
tTraverse f (IfThenElse t a b c) = IfThenElse <$> f t <*> tTraverse f a <*> tTraverse f b <*> tTraverse f c
tTraverse f expr
  | length (getSubExprs expr) == 0 =
      getNullaryConstructor expr <$> f (getTypeInfo expr)
  | length (getSubExprs expr) == 1 =
      getUnaryConstructor expr <$> f (getTypeInfo expr) <*> tTraverse f (getSubExprs expr !! 0)
  | length (getSubExprs expr) == 2 =
      getBinaryConstructor expr <$> f (getTypeInfo expr) <*> tTraverse f (getSubExprs expr !! 0) <*> tTraverse f (getSubExprs expr !! 1)

tMapM :: Monad m => (Expr x a -> m y) -> Expr x a -> m (Expr y a)
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

arity :: Expr x a -> Int
arity e = length $ getSubExprs e

getSubExprs :: Expr x a -> [Expr x a]
getSubExprs expr = case expr of 
  (IfThenElse _ a b c) -> [a,b,c]
  (GreaterThan _ a b) -> [a,b]
  (ThetaI _ _) -> []
  (Uniform _) -> []
  (Normal _) -> []
  (Constant _ _) -> []
  (MultF _ a b) -> [a,b]
  (MultI _ a b) -> [a,b]
  (PlusF _ a b) -> [a,b]
  (PlusI _ a b) -> [a,b]
  (ExpF _ a) -> [a]
  (NegF _ a) -> [a]
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
  (ReadNN _ _ a) -> [a]

setSubExprs :: Expr x a -> [Expr x a] -> Expr x a
setSubExprs expr [] = case expr of
  ThetaI t x -> ThetaI t x
  Uniform t -> Uniform t
  Normal t -> Normal t
  Constant t x -> Constant t x
  Null t -> Null t
  Call t x -> Call t x
  Var t x -> Var t x
  CallArg t n _ -> CallArg t n []
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a] = case expr of
  Arg t l n _ -> Arg t l n a
  Lambda t l _ -> Lambda t l a
  ExpF t _ -> ExpF t a
  NegF t _ -> NegF t a
  ReadNN t n _ -> ReadNN t n a
  CallArg t n _ -> CallArg t n [a]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a,b] = case expr of
  GreaterThan t _ _ -> GreaterThan t a b
  MultF t _ _ -> MultF t a b
  MultI t _ _ -> MultI t a b
  PlusF t _ _ -> PlusF t a b
  PlusI t _ _ -> PlusI t a b
  Cons t _ b -> Cons t a b
  TCons t _ b -> TCons t a b
  LetIn t x _ b -> LetIn t x a b
  CallArg t n _ -> CallArg t n [a,b]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr [a,b,c] = case expr of
  IfThenElse t _ _ _ -> IfThenElse t a b c
  CallArg t n _ -> CallArg t n [a,b,c]
  _ -> error "unmatched expr in setSubExprs"
setSubExprs expr subExprs = case expr of
  InjF t l _ -> InjF t l subExprs
  CallArg t n _ -> CallArg t n subExprs
  _ -> error "unmatched expr in setSubExprs"

getTypeInfo :: Expr t a -> t
getTypeInfo expr = case expr of
  (IfThenElse t _ _ _)  -> t
  (GreaterThan t _ _)   -> t
  (ThetaI t _)          -> t
  (Uniform t)           -> t
  (Normal t)            -> t
  (Constant t _)        -> t
  (MultF t _ _)         -> t
  (MultI t _ _)         -> t
  (PlusF t _ _)         -> t
  (PlusI t _ _)         -> t
  (ExpF t _)            -> t
  (NegF t _)            -> t
  (Null t)              -> t
  (Cons t _ _)          -> t
  (TCons t _ _)         -> t
  (Call t _)            -> t
  (Var t _)             -> t
  (LetIn t _ _ _)       -> t
  (InjF t _ _)        -> t
  --(LetInD t _ _ _)      -> t
  --(LetInTuple t _ _ _ _)-> t
  (Arg t _ _ _)         -> t
  (CallArg t _ _)       -> t
  (Lambda t _ _)        -> t
  (ReadNN t _ _)        -> t
  
setTypeInfo :: Expr t a -> t -> Expr t a
setTypeInfo expr t = case expr of
  (IfThenElse _ a b c)  -> (IfThenElse t a b c)
  (GreaterThan _ a b)   -> (GreaterThan t a b)
  (ThetaI _ a)          -> (ThetaI t a)
  (Uniform _)           -> (Uniform t)
  (Normal _)            -> (Normal t)
  (Constant _ a)        -> (Constant t a)
  (MultF _ a b)         -> (MultF t a b)
  (MultI _ a b)         -> (MultI t a b)
  (PlusF _ a b)         -> (PlusF t a b)
  (PlusI _ a b)         -> (PlusI t a b)
  (ExpF _ a)            -> (ExpF t a)
  (NegF _ a)            -> (NegF t a)
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

prettyPrintProg :: (Num a, Show a, Show t) => Program t a -> [String]
prettyPrintProg (Program decls expr) = concatMap prettyPrintDecl decls ++ mainString
  where mainString = ("--- Main Expression ---"):(prettyPrint expr:: [String])

prettyPrintDecl :: (Num a, Show a, Show t) => Decl t a -> [String]
prettyPrintDecl (name, expr) = ("--- Function: " ++ name ++ "---"):prettyPrint expr

prettyPrint :: (Num a, Show a, Show t) => Expr t a -> [String]
prettyPrint expr = 
  fstLine : indented
    where
      childExprs = getSubExprs expr
      indented = map indent $ concatMap prettyPrint childExprs :: [String]
      indent ls = "    " ++ ls
      fstLine = printFlat expr ++ " :: (" ++ show (getTypeInfo expr) ++ ")"

prettyPrintNoReq :: Expr t a -> [String]
prettyPrintNoReq expr =
  fstLine : indented
    where
      childExprs = getSubExprs expr
      indented = map indent $ concatMap prettyPrintNoReq childExprs :: [String]
      indent ls = "    " ++ ls
      fstLine = printFlatNoReq expr

prettyPrintProgNoReq ::Program t a -> [String]
prettyPrintProgNoReq (Program decls expr) = concatMap prettyPrintDeclNoReq decls ++ mainString
  where mainString = ("--- Main Expression ---"):(prettyPrintNoReq expr:: [String])

prettyPrintDeclNoReq ::Decl t a -> [String]
prettyPrintDeclNoReq (name, expr) = ("--- Function: " ++ name ++ "---"):prettyPrintNoReq expr

printFlat :: Show a => Expr t a -> String
printFlat expr = case expr of
  IfThenElse {} -> "IfThenElse"
  GreaterThan {} -> "GreaterThan"
  (ThetaI _ i) -> "Theta_" ++ show i
  Uniform {} -> "Uniform"
  Normal {} -> "Normal"
  (Constant _ x) -> "Constant (" ++ show x ++ ")"
  MultF {} -> "MultF"
  MultI {} -> "MultI"
  PlusF {} -> "PlusF"
  PlusI {} -> "PlusI"
  ExpF {} -> "ExpF"
  NegF {} -> "NegF"
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
  (ReadNN _ name _) -> "ReadNN " ++ name

printFlatNoReq :: Expr t a -> String
printFlatNoReq expr = case expr of
  IfThenElse {} -> "IfThenElse"
  GreaterThan {} -> "GreaterThan"
  (ThetaI _ i) -> "Theta_" ++ show i
  Uniform {} -> "Uniform"
  Normal {} -> "Normal"
  (Constant _ _) -> "Constant"
  MultF {} -> "MultF"
  MultI {} -> "MultI"
  PlusF {} -> "PlusF"
  PlusI {} -> "PlusI"
  ExpF {} -> "ExpF"
  NegF {} -> "NegF"
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
  ReadNN {} -> "ReadNN"
  
