module SPLL.Lang where

import SPLL.Typing.PType
import SPLL.Typing.RType
import qualified Data.Set as Set

import qualified Data.Map as Map

data Expr x a = IfThenElse x (Expr x a) (Expr x a) (Expr x a)
              | GreaterThan x (Expr x a) (Expr x a)
              | ThetaI x Int
              | Uniform x
              | Normal x
              | Constant x (Value a)
              | Mult x (Expr x a) (Expr x a)
              | Plus x (Expr x a) (Expr x a)
              | Null x
              | Cons x (Expr x a) (Expr x a)
              | TNull x
              | TCons x (Expr x a) (Expr x a)
              | Call x String 
              --  | LetInD x String (Expr x a) (Expr x a)
              --  | LetInTuple x String (Expr x a) (BijectiveF a) (Expr x a) 
              | LetIn x String (Expr x a) (Expr x a)
             -- Change params to expr
              | InjF x String [Expr x a] (Expr x a)
              | Arg x String RType (Expr x a)
              | CallArg x String [Expr x a]
              | Lambda x String (Expr x a)
              | ReadNN x (Expr x a)
              | Fix x (Expr x a)
              | Var x String
              -- TODO: Needs Concat to achieve proper SPN-parity.
              deriving (Show, Eq, Ord)

data VEnv a
  = ValueEnv {values :: Map.Map String (Value a), branchMap :: BranchMap a}
  deriving (Eq, Show)


type BranchMap a = Map.Map (Expr TypeInfoWit a) [String]
vempty :: VEnv a
vempty = ValueEnv {values = Map.empty, branchMap = Map.empty}

vextend :: VEnv a -> (String, Value a) -> VEnv a
vextend env (x, s) = env { values = Map.insert x s (values env) }

vremove :: VEnv a -> String -> VEnv a
vremove env var = env {values = Map.delete var (values env)}

type Params a = [Value a]
-- forward, inverse, inverse'
newtype (Floating a) => FPair a = FPair (RType, Params a -> Value a -> Value a, Params a -> Value a -> Value a, Params a -> Value a -> a)
type FEnv a = [(String, FPair a)]
newtype (Floating a) => FPair2 a = FPair2 (Params a -> a -> a,  Params a -> a -> a, Params a -> a -> a)
type FEnv2 a = [(String, FPair2 a)]
type Name = String

data TypeInfo = TypeInfo RType PType deriving (Show, Eq)
data TypeInfoWit = TypeInfoWit RType PType WitnessedVars deriving (Show, Eq, Ord)

data Program x a = Program [Decl x a] (Expr x a) deriving (Show, Eq)

type TypedExpr a = Expr TypeInfo a
type TypedProg a = Program TypeInfo a
type Decl x a = (String, Expr x a)

type WitnessedVars = Set.Set String
instance Functor (Expr x) where
  fmap = exprMap

data Value a = VBool Bool
           | VInt Int
           | VSymbol String
           | VFloat a
           | VList [Value a]
           | VTuple [Value a]
           | VBranch (Value a) (Value a) String
           | VRange (Limits a)
           | VAnyList 
           -- | Value of Arrow a b could be Expr TypeInfo a, with Expr being a Lambda?
           deriving (Show, Eq, Ord)

--Nothing indicates low/high infinity.
data Limits a = Limits (Maybe (Value a)) (Maybe (Value a))
           deriving (Show, Eq, Ord)
  

instance Functor Value where
  fmap = valMap

instance Foldable Value where
  foldr = valFoldr
  foldMap = valFoldMap
 
valMap :: (a -> b) -> Value a -> Value b
valMap f (VBool b) = VBool b
valMap f (VInt i) = VInt i
valMap f (VSymbol i) = VSymbol i
valMap f (VFloat a) = VFloat $ f a
valMap f (VList v) = VList $ map (valMap f) v
valMap f (VTuple v) = VList $ map (valMap f) v
valMap f (VBranch v1 v2 x ) = VBranch (valMap f v1) (valMap f v2) x
valMap f (VRange v1) = VRange (limitsMap f v1) 
valMap f (VSymbol i) = VSymbol i
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

valFoldr :: (a -> b -> b) -> b -> Value a -> b 
valFoldr f ag (VBool b) = ag
valFoldr f ag (VInt i) = ag
valFoldr f ag (VSymbol i) = ag
valFoldr f ag (VFloat a) = f a ag
valFoldr f ag (VList []) = ag
valFoldr f ag (VList ((VFloat x):rst)) = valFoldr f (f x ag) (VList rst)
valFoldr f ag (VTuple []) = ag
valFoldr f ag (VTuple ((VFloat x):rst)) = valFoldr f (f x ag) (VList rst)

valFoldMap :: Monoid m => (a -> m) -> Value a -> m 
valFoldMap make (VBool b) = mempty
valFoldMap make (VInt i) = mempty
valFoldMap make (VSymbol i) = mempty
valFoldMap make (VFloat a) = make a
valFoldMap make (VList []) = mempty
valFoldMap make (VList ((VFloat x):rst)) = make x <> valFoldMap make (VList rst)
valFoldMap make (VTuple []) = mempty
valFoldMap make (VTuple ((VFloat x):rst)) = make x <> valFoldMap make (VTuple rst)

valTraverse :: Applicative f => (a -> f b) -> Value a -> f (Value b) 
valTraverse make (VBool b) = pure (VBool b)
valTraverse make (VInt i) = pure (VInt i)
--valTraverse make (VSymbol i) = pure (VSymbol i)
--valTraverse make (VFloat a) = VFloat <$> make a
--valTraverse make (VList v) = VList <$> (foldr (<*>) ( id) (map (traverse make) v))
--valTraverse make (VTuple v) = VTuple <$> (foldr (<*>) ( id) (map (traverse make) v))


setRType :: TypeInfo -> RType -> TypeInfo
setRType (TypeInfo _ pt) rt =  TypeInfo rt pt
getPType :: TypeInfo -> PType 
getPType (TypeInfo _ pt) = pt
setPType :: TypeInfo -> PType -> TypeInfo
setPType (TypeInfo rt _) pt =  TypeInfo rt pt
getWits :: TypeInfoWit  -> WitnessedVars
getWits (TypeInfoWit _ _ a) =  a
setWits :: TypeInfoWit  -> WitnessedVars -> TypeInfoWit
setWits (TypeInfoWit a b _) = TypeInfoWit a b
getWitsW :: Expr TypeInfoWit a -> WitnessedVars
getWitsW e = getWits (getTypeInfo e)
getPTypeW :: TypeInfoWit -> PType 
getPTypeW (TypeInfoWit _ pt _) = pt

exprMap :: (a -> b) -> Expr x a -> Expr x b
exprMap f expr = case expr of
  (IfThenElse t a b c) -> IfThenElse t (fmap f a) (fmap f b) (fmap f c)
  (GreaterThan t a b) -> GreaterThan t (fmap f a) (fmap f b)
  (ThetaI t x) -> ThetaI t x
  (Uniform t) -> Uniform t
  (Normal t) -> Normal t
  (Constant t x) -> Constant t $ fmap f x
  (Mult t a b) -> Mult t (fmap f a) (fmap f b)
  (Plus t a b) -> Plus t (fmap f a) (fmap f b)
  (Null t) -> Null t
  (Cons t a b) -> Cons t (fmap f a) (fmap f b)
  (TNull t) -> TNull t
  (TCons t a b) -> TCons t (fmap f a) (fmap f b)
  (Call t x) -> Call t x
  (Var t x) -> Var t x
  (LetIn t x a b) -> LetIn t x (fmap f a) (fmap f b)
  (InjF t x a b) -> InjF t x (map (fmap f) a) (fmap f b)
  --(LetInD t x a b) -> LetInD t x (fmap f a) (fmap f b)
  --(LetInTuple t x a b c) -> LetInTuple t x (fmap f a) (biFMap f b) (fmap f c)
  (Arg t name r a) -> Arg t name r (fmap f a)
  (CallArg t name a) -> CallArg t name (map (fmap f) a)
  (Lambda t name a) -> Lambda t name (fmap f a)
  (ReadNN t a) -> ReadNN t (fmap f a)
  
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
  (Mult _ a b) -> Mult (f expr) a b
  (Plus _ a b) -> Plus (f expr) a b
  (Null _) -> Null (f expr)
  (Cons _ a b) -> Cons (f expr) a b
  (TNull _) -> TNull (f expr)
  (TCons _ a b) -> TCons (f expr) a b
  (Call _ x) -> Call (f expr) x
  (LetIn _ x a bi) -> LetIn (f expr) x a bi
  (InjF _ x a b) -> InjF (f expr) x a b
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
  (Mult t a b) -> Mult t (tMap f a) (tMap f b)
  (Plus t a b) -> Plus t (tMap f a) (tMap f b)
  (Null t) -> Null t
  (Cons t a b) -> Cons t (tMap f a) (tMap f b)
  (TNull t) -> TNull t
  (TCons t a b) -> TCons t (tMap f a) (tMap f b)
  (Call t x) -> Call t x
  (LetIn t x a b) -> LetIn t x (tMap f a) (tMap f b)
  (InjF t x a b) -> InjF t x (map (tMap f) a) (tMap f b)
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
  (Mult _ a b) -> Mult (f expr) (tMap f a) (tMap f b)
  (Plus _ a b) -> Plus (f expr) (tMap f a) (tMap f b)
  (Null _) -> Null (f expr)
  (Cons _ a b) -> Cons (f expr) (tMap f a) (tMap f b)
  (TNull _) -> TNull (f expr)
  (TCons _ a b) -> TCons (f expr) (tMap f a) (tMap f b)
  (Call _ x) -> Call (f expr) x
  (LetIn _ x a b) -> LetIn (f expr) x (tMap f a) (tMap f b)
  (InjF t x a b) -> InjF (f expr) x (map (tMap f) a) (tMap f b)
  --(LetInD t x a b) -> LetInD (f expr) x (tMap f a) (tMap f b)
  --(LetInTuple t x a b c) -> LetInTuple (f expr) x (tMap f a) b (tMap f c)
  (Arg _ name r a) -> Arg (f expr) name r (tMap f a)
  (CallArg _ name a) -> CallArg (f expr) name (map (tMap f) a)
  (Lambda _ name a) -> Lambda (f expr) name (tMap f a)
  (ReadNN _ a) -> ReadNN (f expr) (tMap f a)
  (Var _ name) -> Var (f expr) name

tMapProg :: (Expr x a -> y) -> Program x a -> Program y a
tMapProg f (Program decls expr) = Program (zip (map fst decls) (map (tMap f . snd) decls)) (tMap f expr)

getSubExprs :: Expr x a -> [Expr x a]
getSubExprs expr = case expr of 
  (IfThenElse _ a b c) -> [a,b,c]
  (GreaterThan _ a b) -> [a,b]
  (ThetaI _ x) -> []
  (Uniform _) -> []
  (Normal _) -> []
  (Constant _ x) -> []
  (Mult _ a b) -> [a,b]
  (Plus _ a b) -> [a,b]
  (Null _) -> []
  (Cons _ a b) -> [a,b]
  (TNull _) -> []
  (TCons _ a b) -> [a,b]
  (Call _ x) -> []
  (LetIn _ x a b) -> [a, b]
  (Var _ _) -> []
  (InjF t x a b) -> a ++ [b]
  --(LetInD t x a b) -> [a,b]
  --(LetInTuple t x a b c) -> [a,c]
  (Arg _ name r a) -> [a]
  (CallArg _ name a) -> a
  (Lambda _ _ a) -> [a]
  (ReadNN _ a) -> [a]

getTypeInfo :: Expr t a -> t
getTypeInfo expr = case expr of
  (IfThenElse t _ _ _)  -> t
  (GreaterThan t _ _)   -> t
  (ThetaI t _)          -> t
  (Uniform t)           -> t
  (Normal t)            -> t
  (Constant t _)        -> t
  (Mult t _ _)          -> t
  (Plus t _ _)          -> t
  (Null t)              -> t
  (Cons t _ _)          -> t
  (TNull t)              -> t
  (TCons t _ _)          -> t
  (Call t _)            -> t
  (LetIn t _ _ _)       -> t
  (InjF t _ _ _)        -> t
  --(LetInD t _ _ _)      -> t
  --(LetInTuple t _ _ _ _)-> t
  (Var t _)             -> t
  (Arg t _ _ _)         -> t
  (CallArg t _ _)       -> t
  (Lambda t _ _)        -> t
  (ReadNN t _)          -> t

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
getRType (VTuple t) = Tuple $ map getRType t

prettyPrintProg :: (Num a, Show a, Show t) => Program t a -> [String]
prettyPrintProg (Program decls expr) = concatMap prettyPrintDecl decls ++ mainString
  where mainString = ("--- Main Expression ---"):(prettyPrint expr:: [String])

prettyPrintDecl :: (Num a, Show a, Show t) => Decl t a -> [String]
prettyPrintDecl (name, expr) = ("--- Function: " ++ name ++ "---"):prettyPrint expr

prettyPrint :: (Num a, Show a, Show t) => Expr t a -> [String]
prettyPrint expr = 
  fstLine : indented
    where
      childExprs = recurse expr
      indented = map indent $ concatMap prettyPrint childExprs :: [String]
      indent ls = "    " ++ ls
      fstLine = printFlat expr ++ " :: (" ++ show (getTypeInfo expr) ++ ")"

prettyPrintNoReq :: Expr t a -> [String]
prettyPrintNoReq expr =
  fstLine : indented
    where
      childExprs = recurse expr
      indented = map indent $ concatMap prettyPrintNoReq childExprs :: [String]
      indent ls = "    " ++ ls
      fstLine = printFlatNoReq expr

prettyPrintProgNoReq ::Program t a -> [String]
prettyPrintProgNoReq (Program decls expr) = concatMap prettyPrintDeclNoReq decls ++ mainString
  where mainString = ("--- Main Expression ---"):(prettyPrintNoReq expr:: [String])

prettyPrintDeclNoReq ::Decl t a -> [String]
prettyPrintDeclNoReq (name, expr) = ("--- Function: " ++ name ++ "---"):prettyPrintNoReq expr

recurse :: Expr t a -> [Expr t a]
recurse expr = case expr of 
  (IfThenElse _ a b c) -> [a,b,c]
  (GreaterThan _ a b) -> [a,b]
  (ThetaI _ _) -> []
  (Uniform _) -> []
  (Normal _) -> []
  (Constant _ _) -> []
  (Mult _ a b) -> [a,b]
  (Plus _ a b) -> [a,b]
  (Null _) -> []
  (Cons _ a b) -> [a,b]
  (TNull _) -> []
  (TCons _ a b) -> [a,b]
  (Call _ _) -> []
  (LetIn _ _ a b) -> [a, b]
  (InjF t _ a b)  -> a ++ [b]
  --(LetInD t _ a b) -> [a,b]
  --(LetInTuple t _ a b c) -> [a, c]
  (Var _ _)       -> []
  (Arg _ _ _ a) -> [a]
  (CallArg _ _ a) -> a
  (Lambda _ _ a) -> [a]
  (ReadNN _ a) -> [a]

printFlat :: Show a => Expr t a -> String
printFlat expr = case expr of
  IfThenElse {} -> "IfThenElse"
  GreaterThan {} -> "GreaterThan"
  (ThetaI _ i) -> "Theta_" ++ show i
  Uniform {} -> "Uniform"
  Normal {} -> "Normal"
  (Constant _ x) -> "Constant (" ++ show x ++ ")"
  Mult {} -> "Mult"
  Plus {} -> "Plus"
  (Null _) -> "Null"
  Cons {} -> "Cons"
  (TNull _) -> "TNull"
  TCons {} -> "TCons"
  (Call _ a) -> "Call " ++ a
  LetIn {} -> "LetIn"
  --(LetInD {}) -> "LetInD"
  --(LetInTuple {}) -> "LetInTuple"
  (InjF t _ _ _)        -> "InjF"
  Var _ a -> "Var " ++ a
  (Arg _ var r _ ) -> "Bind " ++ var ++ "::" ++ show r
  (CallArg _ a _ ) -> "CallArg" ++ a
  (Lambda _ name _) -> "\\" ++ name  ++ " -> "
  (ReadNN _ _) -> "ReadNN"

printFlatNoReq :: Expr t a -> String
printFlatNoReq expr = case expr of
  IfThenElse {} -> "IfThenElse"
  GreaterThan {} -> "GreaterThan"
  (ThetaI _ i) -> "Theta_" ++ show i
  Uniform {} -> "Uniform"
  Normal {} -> "Normal"
  (Constant _ _) -> "Constant"
  Mult {} -> "Mult"
  Plus {} -> "Plus"
  (Null _) -> "Null"
  Cons {} -> "Cons"
  (TNull _) -> "TNull"
  TCons {} -> "TCons"
  (Call _ a) -> "Call " ++ a
  Var _ _ -> "Var"
  LetIn {} -> "LetIn"
  (InjF t _ _ _) -> "InjF"
  --(LetInD {}) -> "LetInD"
  --(LetInTuple {}) -> "LetInTuple"
  (Arg _ var r _ ) -> "Bind " ++ var ++ "::" ++ show r
  (CallArg _ a _ ) -> "CallArg" ++ a
  (Lambda _ name _) -> "\\" ++ name  ++ " -> "
  (ReadNN _ _) -> "ReadNN"