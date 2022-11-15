module SPLL.Lang where

import SPLL.Typing.PType
import SPLL.Typing.RType

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
              | Call x String
              | LetIn x String (Expr x a) (Expr x a)
              | Arg x String RType (Expr x a)
              | CallArg x String [Expr x a]
              | Lambda x String (Expr x a)
              | ReadNN x (Expr x a)
              | Fix x (Expr x a)
              | Var x String
              -- TODO: Needs Concat to achieve proper SPN-parity.
              deriving (Show, Eq)

type Name = String

data Program x a = Program [Decl x a] (Expr x a) deriving Eq

type Decl x a = (String, Expr x a)

instance Functor (Expr x) where
  fmap = exprMap

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
  (Call t x) -> Call t x
  (LetIn t x a b) -> LetIn t x (fmap f a) (fmap f b)
  (Arg t name r a) -> Arg t name r (fmap f a)
  (CallArg t name a) -> CallArg t name (map (fmap f) a)
  (Lambda t name a) -> Lambda t name (fmap f a)
  (ReadNN t a) -> ReadNN t (fmap f a)

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
  (Call _ x) -> Call (f expr) x
  (LetIn _ x a b) -> LetIn (f expr) x a b
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
  (Call t x) -> Call t x
  (LetIn t x a b) -> LetIn t x (tMap f a) (tMap f b)
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
  (Call _ x) -> Call (f expr) x
  (LetIn _ x a b) -> LetIn (f expr) x (tMap f a) (tMap f b)
  (Arg _ name r a) -> Arg (f expr) name r (tMap f a)
  (CallArg _ name a) -> CallArg (f expr) name (map (tMap f) a)
  (Lambda _ name a) -> Lambda (f expr) name (tMap f a)
  (ReadNN _ a) -> ReadNN (f expr) (tMap f a)

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
  (Call _ x) -> []
  (LetIn _ x a b) -> [a,b]
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
  (Call t _)            -> t
  (LetIn t _ _ _)       -> t
  (Arg t _ _ _)         -> t
  (CallArg t _ _)       -> t
  (Lambda t _ _)        -> t
  (ReadNN t _)          -> t

data Value a = VBool Bool
           | VInt Int
           | VSymbol String
           | VFloat a
           | VList [Value a]
           -- | Value of Arrow a b could be Expr TypeInfo a, with Expr being a Lambda?
           deriving (Show, Eq)

data TypeInfo = TypeInfo RType PType deriving (Show, Eq)

getRType :: Value a -> RType
getRType (VBool _) = TBool
getRType (VInt _) = TInt
getRType (VSymbol _) = TSymbol
getRType (VFloat _) = TFloat
getRType (VList (a:_)) = ListOf $ getRType a
getRType (VList []) = NullList

instance Functor Value where
  fmap _ (VBool a) = VBool a
  fmap _ (VInt a) = VInt a
  fmap _ (VSymbol a) = VSymbol a
  fmap f (VFloat a) = VFloat $ f a
  fmap f (VList x) = VList $ map (fmap f) x

prettyPrint :: (Num a, Show a, Show t) => Expr t a -> [String]
prettyPrint expr = 
  fstLine : indented
    where
      childExprs = recurse expr
      indented = map indent $ concatMap prettyPrint childExprs :: [String]
      indent ls = "    " ++ ls
      fstLine = printFlat expr ++ " :: (" ++ show (getTypeInfo expr) ++ ")"

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
  (Call _ _) -> []
  (LetIn _ _ a b) -> [a,b]
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
  (Call _ a) -> "Call " ++ a
  LetIn {} -> "LetIn"
  (Arg _ var r _ ) -> "Bind " ++ var ++ "::" ++ show r
  (CallArg _ a _ ) -> "CallArg" ++ a
  (Lambda _ name _) -> "\\" ++ name  ++ " -> "
  (ReadNN _ _) -> "ReadNN"