{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Lib
    ( someFunc
    ) where


import Numeric.AD
import System.Random
import Control.Monad
import Data.List (transpose, sortBy, elemIndices, nub)
import Data.Maybe
import Control.Monad.Random
import Control.Monad.Except
import Control.Monad.Reader
import Data.Reflection (Reifies)
import Numeric.AD.Internal.Reverse ( Reverse, Tape)
--import Data.Either (fromRight)
--import Debug.Trace
import Data.Function (on)
import Data.Ord

--assumption about grad: Reverse s a is Num if a is Num.
--Thererfore, grad :: (Traversable f, Num a) => (forall s. Reifies s Tape => f (Reverse s a) -> Reverse s a) -> f a -> f a
-- essentially translates to grad :: Traversable f, Num a) => (f (Reverse s a) -> Reverse s a) -> f a -> f a
-- or more simply: grad takes any function :: Traversable f, Num a => f a -> a;
-- but then we have to sort out the type of the hypothesis (a)

--someFunc = print "Hello world"

--weatherHask lastDay = if lastDay == rainy
--  then let current = randA in (current, weatherHask current)
--  else let current = randB in (current, weatherHask current)

paramExpr :: Expr () Float
paramExpr = Arg () "iterations" TFloat (IfThenElse ()
  (GreaterThan () (Call () "iterations") (Constant () (VFloat 0.5)))
  (Cons () (Constant () (VBool True)) (CallArg () "main" [Plus () (Call () "iterations") (Constant () (VFloat (-1.0)))]))
  (Null ()))

weatherExpr :: Expr () a
weatherExpr = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Null ())
  (Cons () (Constant () (VBool True)) (Call () "main"))

--testExpr :: Num a => Expr a
testExpr :: Expr () a
testExpr = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Constant () (VBool True))
  (Constant () (VBool False))

testExpr2 :: Expr () a
testExpr2 = IfThenElse ()
  (GreaterThan () (Uniform ()) (ThetaI () 0))
  (Null ())
  (Cons () (Constant () (VBool True)) (Call () "main"))

someFunc :: IO()
someFunc =
  --let env = [("main", testExpr2)] :: Env () Float
  let env = [("main", paramExpr)] :: Env () Float
  in testRun env
  

--gradientStep thetas samples = zipWith (+) thetas $ map (0.0001 *) gradient
--  where gradient = [sum (grad (\th -> probability th datum) thetas) | datum <- samples]

--lambdathing :: forall s a2. (Num a2, Reifies s Tape) => 
--lambdathing :: Num a => Env a -> Expr a -> Value a -> [a] -> a
--lambdathing env expr sample theta = unwrapP $ probability env theta expr sample

--something :: Num a => Env a -> Expr a -> Value a -> [a] -> [a]
--something env expr sample = grad (\theta -> unwrapP $ probability (autoEnv env) theta (autoExpr expr) (autoVal sample))

myGradientAscent :: (Floating b, Ord b) => Int -> [(String, Expr TypeInfo b)] -> [b] -> Expr TypeInfo b -> [Value b] -> [([b], b)]
myGradientAscent 0 _ _ _ _ = []
myGradientAscent n env thetas expr vals =
  (thetas, loss) : myGradientAscent (n-1) env new expr vals
    where
      --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
      (loss, new) = optimizeStep env expr vals thetas

--TODO: can we fix this to use the Foldable theta?
optimizeStep :: (Floating a, Ord a) => Env TypeInfo a -> Expr TypeInfo a -> [Value a] -> [a] -> (a, [a])
optimizeStep env expr samples thetas = (loss, zipWith (+) thetas $ map (*0.00001) gradient)
  where
    -- does it make a difference if we do sum(gradients) or if we do gradient(sums)?
    -- TODO: Is it correct to apply map-sum, or do we flatten the wrong dimension here?
    --grad_loss :: [(loss :: a, grad :: [a])]
    grad_loss = [grad' (\(theta) -> log $ unwrapP $ probability (autoEnv env) (autoEnv env) theta (autoExpr expr) (autoVal sample)) thetas | sample <- samples]
    gradient = map sum $ Data.List.transpose $ map snd grad_loss
    loss = sum $ map fst grad_loss

autoExpr :: (Num a, Reifies s Tape) => Expr x a -> Expr x (Reverse s a)
autoExpr = fmap auto

autoEnv :: (Num a, Reifies s Tape) => Env x a -> Env x (Reverse s a)
autoEnv = map (\ (name, expr) -> (name, autoExpr expr))

autoVal :: (Num a, Reifies s Tape) => Value a -> Value (Reverse s a)
autoVal (VBool x) = VBool x
autoVal (VFloat y) = VFloat (auto y)
autoVal (VList xs) = VList (map autoVal xs)

--myGradientAscent :: (Num a, Num b, Num c, Num d) => Int -> Env a -> [b] -> Expr a -> [Value a] -> [([c], d)]
--myGradientAscent 0 _ _ _ _ = []
--myGradientAscent env thetas expr vals = (thetas, loss) : myGradientAscent env newHypothesis expr vals
--  where
    --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
--    loss = sum $ [unwrapP (log $ probability env thetas expr val) | val <- vals]
---    gradient = [sum (grad (\ th -> log $ unwrapP $ _ env th expr datum) thetas) | datum <- vals]
--    newHypothesis = zipWith (+) thetas $ map (\el -> 0.0001 * el) gradient
--pr_ :: (Num a, Num b) => a -> Env b -> [a]


data Expr x a = IfThenElse x (Expr x a) (Expr x a) (Expr x a)
          | GreaterThan x (Expr x a) (Expr x a)
          | ThetaI x Int
          | Uniform x
          | Constant x (Value a)
          | Mult x (Expr x a) (Expr x a)
          | Plus x (Expr x a) (Expr x a)
          | Null x
          | Cons x (Expr x a) (Expr x a)
          | Call x String
          | LetIn x String (Expr x a) (Expr x a)
          | Arg x String RType (Expr x a)
          | CallArg x String [Expr x a]
          -- TODO: Needs Concat to achieve proper SPN-parity.
          deriving (Show, Eq)

instance Functor (Expr x) where
  fmap = exprMap

exprMap :: (a -> b) -> Expr x a -> Expr x b
exprMap f (IfThenElse t a b c) = IfThenElse t (fmap f a) (fmap f b) (fmap f c)
exprMap f (GreaterThan t a b) = GreaterThan t (fmap f a) (fmap f b)
exprMap _ (ThetaI t x) = ThetaI t x
exprMap _ (Uniform t) = Uniform t
exprMap f (Constant t x) = Constant t $ fmap f x
exprMap f (Mult t a b) = Mult t (fmap f a) (fmap f b)
exprMap f (Plus t a b) = Plus t (fmap f a) (fmap f b)
exprMap _ (Null t) = Null t
exprMap f (Cons t a b) = Cons t (fmap f a) (fmap f b)
exprMap _ (Call t x) = Call t x
exprMap f (LetIn t x a b) = LetIn t x (fmap f a) (fmap f b)
exprMap f (Arg t name r a) = Arg t name r (fmap f a)
exprMap f (CallArg t name a) = CallArg t name (map (fmap f) a)

tMapHead :: (Expr x a -> x) -> Expr x a -> Expr x a
tMapHead f expr@(IfThenElse _ a b c) = IfThenElse (f expr) a b c
tMapHead f expr@(GreaterThan _ a b) = GreaterThan (f expr) a b
tMapHead f expr@(ThetaI _ x) = ThetaI (f expr) x
tMapHead f expr@(Uniform _) = Uniform (f expr)
tMapHead f expr@(Constant _ x) = Constant (f expr) x
tMapHead f expr@(Mult _ a b) = Mult (f expr) a b
tMapHead f expr@(Plus _ a b) = Plus (f expr) a b
tMapHead f expr@(Null _) = Null (f expr)
tMapHead f expr@(Cons _ a b) = Cons (f expr) a b
tMapHead f expr@(Call _ x) = Call (f expr) x
tMapHead f expr@(LetIn _ x a b) = LetIn (f expr) x a b
tMapHead f expr@(Arg _ name r a) = Arg (f expr) name r a
tMapHead f expr@(CallArg _ name a) = CallArg (f expr) name a

tMapTails :: (Expr x a -> x) -> Expr x a -> Expr x a
tMapTails f (IfThenElse t a b c) = IfThenElse t (tMap f a) (tMap f b) (tMap f c)
tMapTails f (GreaterThan t a b) = GreaterThan t (tMap f a) (tMap f b)
tMapTails _ (ThetaI t x) = ThetaI t x
tMapTails _ (Uniform t) = Uniform t
tMapTails _ (Constant t x) = Constant t x
tMapTails f (Mult t a b) = Mult t (tMap f a) (tMap f b)
tMapTails f (Plus t a b) = Plus t (tMap f a) (tMap f b)
tMapTails _ (Null t) = Null t
tMapTails f (Cons t a b) = Cons t (tMap f a) (tMap f b)
tMapTails _ (Call t x) = Call t x
tMapTails f (LetIn t x a b) = LetIn t x (tMap f a) (tMap f b)
tMapTails f (Arg t name r a) = Arg t name r (tMap f a)
tMapTails f (CallArg t name a) = CallArg t name (map (tMap f) a)

tMap :: (Expr x a -> y) -> Expr x a -> Expr y a
tMap f expr@(IfThenElse _ a b c) = IfThenElse (f expr) (tMap f a) (tMap f b) (tMap f c)
tMap f expr@(GreaterThan _ a b) = GreaterThan (f expr) (tMap f a) (tMap f b)
tMap f expr@(ThetaI _ x) = ThetaI (f expr) x
tMap f expr@(Uniform _) = Uniform (f expr)
tMap f expr@(Constant _ x) = Constant (f expr) x
tMap f expr@(Mult _ a b) = Mult (f expr) (tMap f a) (tMap f b)
tMap f expr@(Plus _ a b) = Plus (f expr) (tMap f a) (tMap f b)
tMap f expr@(Null _) = Null (f expr)
tMap f expr@(Cons _ a b) = Cons (f expr) (tMap f a) (tMap f b)
tMap f expr@(Call _ x) = Call (f expr) x
tMap f expr@(LetIn _ x a b) = LetIn (f expr) x (tMap f a) (tMap f b)
tMap f expr@(Arg _ name r a) = Arg (f expr) name r (tMap f a)
tMap f expr@(CallArg _ name a) = CallArg (f expr) name (map (tMap f) a)

data TypeInfo = TypeInfo RType PType deriving (Show, Eq)

data RType = TBool
           | TFloat
           | ListOf RType
           | NullList
           | RIdent String
           | RConstraint String RType RType
           | Arrow RType RType
           deriving (Show)

data PType = Deterministic
           | Integrate
           | Chaos
           | PIdent String [(PType, PType)]
           deriving (Show, Eq)

--data TExpr a = TExpr RType PType (Expr a)
--           deriving (Show)

-- Because Env will be polluted by local symbols as we evaluate, we need to reset when calling functions.
-- Therefore, we define that all functions must exist in the global namespace.
-- That way, it is sufficient to carry only the global namespace as reset point.
-- local functions are in principle possible, but they need to carry their own environment with them,
-- e.g. by expanding Env to be of [(String, Env x a, Expr x a)], where [] indicates a shorthand for the global scope.
type Env x a = [(String, Expr x a)]

data Value a = VFloat a
           | VBool Bool
           | VList [Value a]
           deriving (Show, Eq)

getRType :: Value a -> RType
getRType (VFloat _) = TFloat
getRType (VBool _) = TBool
getRType (VList (a:_)) = ListOf $ getRType a
getRType (VList []) = NullList

instance Functor Value where
    fmap f (VFloat a) = VFloat $ f a
    fmap _ (VBool a) = VBool a
    fmap f (VList x) = VList $ map (fmap f) x

data Probability a = PDF a
                 | DiscreteProbability a
                 deriving (Show)

type Check a = ExceptT TypeError (Reader (Env () a))

data TypeError = Mismatch RType RType
               deriving (Show, Eq)

--Nothing indicates low/high infinity.
data Limits a = Limits (Maybe (Value a)) (Maybe (Value a))

--TODO: Assert that downgrade Chaos Deterministic = Chaos
downgrade :: PType -> PType -> PType
downgrade (PIdent name assigns) right = reduce
  (PIdent name $ map (\(nametype, exprtype) -> (nametype, downgrade right exprtype)) assigns)
downgrade left p@(PIdent _ _) = downgrade p left
downgrade Chaos _ = Chaos
downgrade _ Chaos = Chaos
downgrade Integrate Integrate = Integrate
downgrade Integrate Deterministic = Integrate
downgrade Deterministic Integrate = Integrate
downgrade Deterministic Deterministic = Deterministic

reduce :: PType -> PType
reduce p@(PIdent _ [(_, x), (_,y), (_,z)]) = if x == y && y == z then x else p
reduce x = x

upgrade :: PType -> PType -> PType
upgrade (PIdent name assigns) right = reduce
  (PIdent name $ map (\(nametype, exprtype) -> (nametype, upgrade right exprtype)) assigns)
upgrade left p@(PIdent _ _) = downgrade p left
upgrade _ Deterministic = Deterministic
upgrade Deterministic _ = Deterministic
upgrade Chaos _ = Chaos
upgrade _ Chaos = Chaos
upgrade Integrate Integrate = Integrate

pAnd :: Num a => Probability a -> Probability a -> Probability a
pAnd (PDF a) (PDF b) = PDF (a*b)
pAnd (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a*b)
pAnd (PDF a) (DiscreteProbability b) = PDF (a*b)
pAnd (DiscreteProbability a) (PDF b) = PDF (a*b)

pOr :: Num a => Probability a -> Probability a -> Probability a
pOr (PDF a) (PDF b) = PDF (a+b)
pOr (DiscreteProbability a) (DiscreteProbability b) = DiscreteProbability (a+b)
pOr (PDF a) (DiscreteProbability b) = PDF (a+b)
pOr (DiscreteProbability a) (PDF b) = PDF (a+b)

unwrapP :: Probability a -> a
unwrapP (PDF x) = x
unwrapP (DiscreteProbability x) = x

matchRExpr :: Expr () a -> Expr () a -> Check a RType
matchRExpr e1 e2 = do
  e1R <- inferR e1
  e2R <- inferR e2
  matchRType e1R e2R
  --if e1R /= e2R
  ---then throwError $ Mismatch e1R e2R
  --else return e1R

instance Eq RType where
  (==) TBool TBool = True
  (==) TFloat TFloat = True
  (==) (ListOf x) (ListOf y) = x == y
  (==) NullList NullList = True
  (==) (RIdent a) (RIdent b) = a == b
  (==) (RConstraint _ _ retT) (RConstraint _ _ retT2) = retT == retT2
  (==) _ _ = False

rIntersect :: RType -> RType -> Maybe RType
--here be all cases where types are "equal" but one is more strict
-- or where we can match unequal types anyway.
rIntersect l@(RConstraint _ _ retT) r@(RConstraint _ _ retT2) =
  if retT == retT2 && isJust sectType
  -- We need to worry about recursive Constraint types.
  then Just $ buildConstraints (getConstraints l ++ getConstraints r) $ fromJust sectType --Just $ RConstraint name constraint $ RConstraint name2 constraint2 retT2
  else Nothing
    where
      getFinal (RConstraint _ _ b) = getFinal b
      getFinal other = other
      getConstraints (RConstraint x y ys) = (x, y) : getConstraints ys
      getConstraints _ = []
      buildConstraints [] finalR = finalR
      buildConstraints ((a,b):cs) finalR = RConstraint a b (buildConstraints cs finalR)
      leftFinal = getFinal retT
      rightFinal = getFinal retT2
      sectType = rIntersect leftFinal rightFinal
rIntersect left (RConstraint name constraint retT) =
  if isNothing sectType
  then Nothing
  else Just $ RConstraint name constraint $ fromJust sectType
    where sectType = rIntersect left retT
rIntersect (RConstraint name constraint retT) right =
  if isNothing sectType
  then Nothing
  else Just $ RConstraint name constraint $ fromJust sectType
    where sectType = rIntersect right retT
--TODO: Validate the next two lines
rIntersect (RIdent name) t = Just $ RConstraint name t t
rIntersect t (RIdent name) = Just $ RConstraint name t t
rIntersect (ListOf x) NullList = Just $ ListOf x
rIntersect NullList (ListOf x) = Just $ ListOf x
rIntersect left right = if left == right then Just left else Nothing

matchRType :: RType -> RType -> Check a RType
matchRType t1 t2 =
  if isNothing intersection
  then throwError $ Mismatch t1 t2
  else return $ fromJust intersection
    where intersection = rIntersect t1 t2

matchTwoReturnThird :: RType -> RType -> RType -> Check a RType
matchTwoReturnThird a b ret =
  if isNothing intersection
  then throwError $ Mismatch a b
  else return ret
    where intersection = rIntersect a b

getTypeInfo :: Expr t a -> t
getTypeInfo (IfThenElse t _ _ _) = t
getTypeInfo (GreaterThan t _ _) = t
getTypeInfo (ThetaI t _) = t
getTypeInfo (Uniform t) = t
getTypeInfo (Constant t _) = t
getTypeInfo (Mult t _ _) = t
getTypeInfo (Plus t _ _) = t
getTypeInfo (Null t) = t
getTypeInfo (Cons t _ _) = t
getTypeInfo (Call t _) = t
getTypeInfo (LetIn t _ _ _) = t
getTypeInfo (Arg t _ _ _) = t
getTypeInfo (CallArg t _ _) = t

{---setTypeInfo :: Expr x a -> t -> Expr t a
setTypeInfo (IfThenElse x a b c)  t = IfThenElse t a b c
setTypeInfo (GreaterThan x a b)   t = GreaterThan t a b
setTypeInfo (ThetaI x a)          t = ThetaI t a
setTypeInfo (Uniform x)           t = Uniform t
setTypeInfo (Constant x a)        t = Constant t a
setTypeInfo (Mult x a b)          t = Mult t a b
setTypeInfo (Plus x a b)          t = Plus t a b
setTypeInfo (Null x)              t = Null t
setTypeInfo (Cons x a b)          t = Cons t a b
setTypeInfo (Call x a)            t = Call t a
setTypeInfo (LetIn x a b c)       t = LetIn t a b c--}

getR :: Expr TypeInfo a -> RType
getR expr = r
  where
    TypeInfo r _ = getTypeInfo expr

getP :: Expr TypeInfo a -> PType
getP expr = p
  where
    TypeInfo _ p = getTypeInfo expr

-- make no assumption about thetas
inferR :: Expr () a -> Check a RType
inferR (IfThenElse () cond left right) = do
  condR <- inferR cond
  ret <- matchRExpr left right
  matchTwoReturnThird condR TBool ret
  --if condR /= TBool
  --then throwError $ Mismatch condR TBool
  --else matchRExpr left right
inferR (GreaterThan () left right) = do
  e1R <- inferR left
  e2R <- inferR right
  matchTwoReturnThird e1R e2R TBool
  --if e1R /= e2R
  --then throwError $ Mismatch e1R e2R
  --else return TBool
inferR (ThetaI () _) = return TFloat
inferR (Uniform ()) = return TFloat
inferR (Constant () val) = return $ getRType val
--inferR (Constant () (VFloat _)) = return TFloat
--inferR (Constant () (VBool _)) = return TBool
--inferR (Constant () (VList xs)) = return $ ListOf xs
inferR (Mult () e1 e2) = matchRExpr e1 e2
inferR (Plus () e1 e2) = matchRExpr e1 e2
inferR (Null ()) = return NullList
inferR (Cons () headX tailX) = do
  tHead <- inferR headX
  tTail <- inferR tailX
  case tTail of
    ListOf innerType -> liftM ListOf $ matchRType innerType tHead
    NullList -> return (ListOf tHead)
    _ -> matchRType tTail (ListOf tHead)
inferR (Call () name) = return $ RIdent name

inferP :: Expr () a -> Check a PType
inferP (IfThenElse _ cond left right) = do
  condP <- inferP cond
  leftP <- inferP left
  rightP <- inferP right
  -- assumption: cond is always binomial - this should follow from typing rules.
  return $ downgrade condP $ downgrade leftP rightP
inferP (GreaterThan _ left right) = do
  leftP <- inferP left
  rightP <- inferP right
  return $ downgrade leftP rightP
inferP (ThetaI _ _) = return Deterministic
inferP (Constant _ _) = return Deterministic
inferP (Uniform _) = return Integrate
inferP (Mult _ left right) = do
  leftP <- inferP left
  rightP <- inferP right
  if downgrade leftP rightP == Deterministic
  then return $ upgrade leftP rightP
  -- we do not know how to integrate over a product
  else return Chaos
inferP (Plus _ left right) = do
  leftP <- inferP left
  rightP <- inferP right
  if downgrade leftP rightP == Deterministic
  then return $ upgrade leftP rightP
  -- we do not know how to integrate over a sum
  else return Chaos
inferP (Null _) = return Deterministic
inferP (Cons _ headX tailX) = do
  -- TODO: Assumes independence. Invalid if there exists x elem Env that is used in head and tail.
  headP <- inferP headX
  tailP <- inferP tailX
  return $ downgrade headP tailP
inferP (Call _ name) = return $ PIdent name [(Deterministic, Deterministic), (Integrate, Integrate), (Chaos, Chaos)]--TODO: here there be dragons
--inferP (LetIn _ name assignment inExpr) = inferP inExpr
--TODO: Arg needs to make sure the variable has proper type, same as let_in
--inferP (Arg _ name inExpr) = inferP inExpr
--inferP (CallArg _ name withExpr) = return $ PIdent name [(Deterministic, Deterministic), (Integrate, Integrate), (Chaos, Chaos)]


--note: We need detGenerate in order to be able to solve probability: Reverse s a does not have a Random instance,
-- so we have to make do without in probability. Hence if we need to generate, we need to generate deterministically.
detGenerate :: (Fractional a,Ord a) => Env TypeInfo a -> [a] -> Expr TypeInfo a -> Value a
detGenerate env thetas (IfThenElse _ cond left right) = do
  case detGenerate env thetas cond of
    VBool True -> detGenerate env thetas left
    VBool False -> detGenerate env thetas right
    _ -> error "Type error"
detGenerate env thetas (GreaterThan _ left right) =
  case (a,b) of
    (VFloat af, VFloat bf) -> VBool (af > bf)
    _ -> error "Type error"
  where
    a = detGenerate env thetas left
    b = detGenerate env thetas right
detGenerate _ thetas (ThetaI _ i) = VFloat (thetas !! i)
detGenerate _ _ (Uniform _) = error "tried to detGenerate from random atom"
detGenerate _ _ (Constant _ x) = x
detGenerate _ _ (Null _) = VList []
detGenerate env thetas (Cons _ hd tl) = VList (detGenerate env thetas hd : xs)
  where VList xs = detGenerate env thetas tl
detGenerate _ _ expr =
  if pt /= Deterministic
  then error "tried detGenerate on non-deterministic expr"
  else error "detGenerate not defined for expr"
    where TypeInfo rt pt = getTypeInfo expr

generate :: (Fractional a, RandomGen g, Ord a, Random a) => Env TypeInfo a -> Env TypeInfo a -> [a] -> Expr TypeInfo a -> Rand g (Value a)
generate globalEnv env thetas (IfThenElse _ cond left right) = do
  condV <- generate globalEnv env thetas cond
  case condV of
    VBool True -> generate globalEnv env thetas left
    VBool False -> generate globalEnv env thetas right
    _ -> error "Type error"
generate globalEnv env thetas (GreaterThan _ left right) = do
  a <- generate globalEnv env thetas left
  b <- generate globalEnv env thetas right
  case (a,b) of
    (VFloat af, VFloat bf) -> return $ VBool (af > bf)
    _ -> error "Type error"
generate _ _ thetas (ThetaI _ i) = return $ VFloat (thetas !! i)
generate _ _ _ (Uniform _) = do
  r <- getRandomR (0.0, 1.0) --uniformR (0.0, 1.0)
  return $ VFloat r
generate _ _ _ (Constant _ x) = return x
generate _ _ _ (Null _) = return $ VList []
generate globalEnv env thetas (Cons _ hd tl) = do
  ls <- generate globalEnv env thetas tl
  case ls of
    VList xs -> do
      x <- generate globalEnv env thetas hd
      return $ VList (x : xs)
    _ -> error "type error in list cons"
--Call leaves function context, pass GlobalEnv to ensure env is cleaned up.
generate globalEnv env thetas (Call t name) = generate globalEnv globalEnv thetas expr
  where Just expr = lookup name env

probability :: (Fractional a, Ord a) => Env TypeInfo a -> Env TypeInfo a -> [a] -> Expr TypeInfo a -> Value a -> Probability a
-- possible problems in the probability math in there:
probability globalEnv env thetas (IfThenElse t cond left right) val = pOr (pAnd pCond pLeft) (pAnd pCondInv pRight)
  where
    pCond = probability globalEnv env thetas cond (VBool True)
    pCondInv = DiscreteProbability (1 - unwrapP pCond)
    pLeft = probability globalEnv env thetas left val
    pRight = probability globalEnv env thetas right val
probability globalEnv env thetas (GreaterThan t left right) (VBool x)
  | leftP == Deterministic && rightP == Integrate && x     = PDF $ integrate right thetas env (Limits (Just leftGen) Nothing)
  | rightP == Deterministic && leftP == Integrate && x     = PDF $ integrate left thetas env (Limits Nothing (Just rightGen))
  | leftP == Deterministic && rightP == Integrate && not x = PDF $ 1 - integrate right thetas env (Limits (Just leftGen) Nothing)
  | rightP == Deterministic && leftP == Integrate && not x = PDF $ 1 - integrate left thetas env (Limits Nothing (Just rightGen))
  | otherwise = error "undefined probability for greaterThan"
  where
    leftP = getP left
    rightP = getP right
    leftGen = detGenerate env thetas left
    rightGen = detGenerate env thetas right
probability _ _ thetas (ThetaI _ x) (VFloat val) = if val == (thetas !! x) then DiscreteProbability 1 else DiscreteProbability 0
probability _ _ _ (ThetaI _ _) _ = error "typing error in probability - ThetaI"
probability _ _ _ (Uniform _) (VFloat x) = if 0 <= x && x <= 1 then PDF 1 else PDF 0
probability _ _ _ (Uniform _) _ = error "typing error in probability - Uniform"
probability _ _ _ (Constant _ val) val2 = if val == val2 then DiscreteProbability 1 else DiscreteProbability 0
probability globalEnv env thetas (Mult _ left right) (VFloat x)
  | leftP == Deterministic = probability globalEnv env thetas right (VFloat inverse)
  | rightP == Deterministic = probability globalEnv env thetas left (VFloat inverse)
  | otherwise = error "can't solve Mult"
  where
    leftP = getP left
    rightP = getP right
    VFloat leftGen = detGenerate env thetas left
    VFloat rightGen = detGenerate env thetas right
    inverse = if leftP == Deterministic then x / leftGen else x / rightGen
probability _ _ _ (Null _) (VList []) = DiscreteProbability 1
probability _ _ _ (Null _) _ = DiscreteProbability 0
probability _ _ _ (Cons _ _ _) (VList []) = DiscreteProbability 0
probability globalEnv env thetas (Cons _ hd tl) (VList (x:xs)) = pAnd (probability globalEnv env thetas hd x) (probability globalEnv env thetas tl $ VList xs)
probability globalEnv env thetas (Call _ name) val = probability globalEnv globalEnv thetas expr val
  where Just expr = lookup name env


integrate :: (Num a, Ord a) => Expr TypeInfo a -> [a] -> Env TypeInfo a -> Limits a -> a
integrate (Uniform t) thetas env (Limits low high) = h2 - l2
  where
    h2 = min 1 $ maybe 1 unwrap high
    l2 = max 0 $ maybe 0 unwrap low
    unwrap vflt = case vflt of
      VFloat x -> x
      _ -> error "unexpected type-error in RT:Integrate"
integrate _ _ _ _ = error "undefined integrate for expr"

prettyPrint :: (Num a, Show a) => Env TypeInfo a -> Expr TypeInfo a -> [String]
prettyPrint env expr = 
  fstLine : indented
    where
      childExprs = recurse expr
      indented = map indent $ concatMap (prettyPrint env) childExprs :: [String]
      indent ls = "    " ++ ls
      rType = getR expr
      pType = getP expr
      fstLine = printFlat expr ++ " [" ++ show rType ++ " | " ++ show pType ++ "]"

recurse :: Expr t a -> [Expr t a]
recurse (IfThenElse _ a b c) = [a,b,c]
recurse (GreaterThan _ a b) = [a,b]
recurse (ThetaI _ _) = []
recurse (Uniform _) = []
recurse (Constant _ _) = []
recurse (Mult _ a b) = [a,b]
recurse (Plus _ a b) = [a,b]
recurse (Null _) = []
recurse (Cons _ a b) = [a,b]
recurse (Call _ _) = []
recurse (LetIn _ _ a b) = [a,b]
recurse (Arg _ _ r a) = [a]
recurse (CallArg _ _ a) = a

printFlat :: Show a => Expr t a -> String
printFlat (IfThenElse _ _ _ _) = "IfThenElse"
printFlat (GreaterThan _ _ _) = "GreaterThan"
printFlat (ThetaI _ i) = "Theta_" ++ show i
printFlat (Uniform _) = "Uniform"
printFlat (Constant _ x) = "Constant (" ++ show x ++ ")"
printFlat (Mult _ _ _) = "Mult"
printFlat (Plus _ _ _) = "Plus"
printFlat (Null _) = "Null"
printFlat (Cons _ _ _) = "Cons"
printFlat (Call _ a) = "Call " ++ a
printFlat (LetIn _ _ _ _ ) = "LetIn"
printFlat (Arg _ var r _ ) = "Bind " ++ var ++ "::" ++ show r
printFlat (CallArg _ a _ ) = "CallArg" ++ a

--Needs to resolve constrained types as a second step.
typeCheckEnv :: Env () a -> Env TypeInfo a
typeCheckEnv env = [(name, typeCheckExpr env expr) | (name, expr) <- env]

--TODO: This should iterate to a fixed point.
resolveConstraints :: Eq a => Env TypeInfo a -> Env TypeInfo a
resolveConstraints en = fixedPointIteration en (\env -> fmap (\(name, t) -> (name, resolveConstraintsExpr env name t)) env) --does this need (Check a ..) type?

--TODO: This may not pass name to subexpr. Instead, name should be left blank then.
resolveConstraintsExpr :: Env TypeInfo a -> String -> Expr TypeInfo a -> Expr TypeInfo a
resolveConstraintsExpr env name = tMapHead (rDeconstrain env name)
                                . tMapHead (pDeconstrain env name)
                                . tMapTails (rDeconstrain env "")
                                . tMapTails (pDeconstrain env "")

--TODO: Verify Env changes are done in a sane manner.

pDeconstrain ::  Env TypeInfo a -> String -> Expr TypeInfo a -> TypeInfo
pDeconstrain env defName expr = TypeInfo rt $ case pt of
    Deterministic -> Deterministic
    Integrate -> Integrate
    Chaos -> Chaos
    -- we're going to have to do a Fixed-point-iteration here to resolve constraints. Only use the lookup results if concrete value
    PIdent name assigns -> if name == defName
        -- direct recursion
        then fixedPointLookup assigns Deterministic
        -- depends on another symbol
        else fromMaybe (PIdent name assigns) pResult
      where
        exprName = lookup name env
        TypeInfo _ pName = getTypeInfo $ fromJust exprName
        pResult = lookup pName assigns
  where
    TypeInfo rt pt = getTypeInfo expr

fixedPointIteration :: Eq a => a -> (a -> a) -> a
fixedPointIteration a f = if b == a then b else fixedPointIteration b f
  where b = f a

fixedPointLookup :: Eq a => [(a, a)] -> a -> a
fixedPointLookup table start = if res == start then start else fixedPointLookup table res
  where
    res = fromJust $ lookup start table

rDeconstrain ::  Env TypeInfo a -> String -> Expr TypeInfo a -> TypeInfo
rDeconstrain env defName expr = TypeInfo rt pt
  where
    TypeInfo rtOld pt = getTypeInfo expr
    rt = case rtOld of
      TBool -> TBool
      TFloat -> TFloat
      ListOf x -> ListOf x
      NullList -> NullList
      RIdent name -> rOfName
        where 
          TypeInfo rOfName _ = getTypeInfo $ fromJust $ lookup name env
      RConstraint name ofType resType -> let TypeInfo rOfName _ = getTypeInfo $ fromJust $ lookup name env in
        if defName == name
          --simple recursion
          then if rOfName == RConstraint name resType resType
            --"fn is of type x as long as fn is of type x.
            then resType
            else if rOfName == ofType
              then resType
              else error ("type error in return type constraintA - " ++ show rOfName ++ show ofType)
          else if rOfName == ofType
            then resType
            else RConstraint name ofType resType

--TODO: if Expr is Let_in or otherwise affects Env.
typeCheckExpr :: Env () a -> Expr () a -> Expr TypeInfo a
typeCheckExpr env = tMap (mkTypeInfo2 env)
--  where
--    tc2 expr
--    pType = fromRight undefined $ runReader (runExceptT (inferP expr)) env
--    rType = fromRight undefined $ runReader (runExceptT (inferR expr)) env
--    mappedSubExprs = tMap (tc env) expr

mkTypeInfo2 :: Env () a -> Expr () a -> TypeInfo
mkTypeInfo2 env expr =
  case mkTypeInfo env expr of
    Left err -> error $ show err
    Right result -> result

mkTypeInfo :: Env () a -> Expr () a -> Either TypeError TypeInfo
mkTypeInfo env expr =
  do
    pType <- runReader (runExceptT (inferP expr)) env
    rType <- runReader (runExceptT (inferR expr)) env
    return $ TypeInfo rType pType
  --where
  --  pType = fromRight undefined $ runReader (runExceptT (inferP expr)) env
  --  rType = fromRight undefined $ runReader (runExceptT (inferR expr)) env

testRun :: (Floating a, Ord a, Random a, Show a) => Env () a -> IO ()
testRun env = do
  print env
  let pretypedEnv = typeCheckEnv env
  let Just pre_main = lookup "main" pretypedEnv
  putStrLn $ unlines $ prettyPrint pretypedEnv pre_main
  let typedEnv = resolveConstraints pretypedEnv
  let Just main = lookup "main" typedEnv
  putStrLn $ unlines $ prettyPrint typedEnv main
  let resultR = getR main
  print resultR
  let resultP = getP main
  print resultP
  samples <- mkSamples 1000 typedEnv [0.5] main
  mapM_ print $ count samples
  let thetasRecovered = myGradientAscent 100 typedEnv [0.1] main samples
  mapM_ print thetasRecovered

mkSamples :: (Fractional a, Ord a, Random a) => Int -> Env TypeInfo a -> [a] -> Expr TypeInfo a -> IO [Value a]
mkSamples 0 _ _ _ = return []
mkSamples n env thetas expr = do
  sample <- evalRandIO $ generate env env thetas expr
  remainder <- mkSamples (n-1) env thetas expr
  return (sample:remainder)

count :: Eq a => [a] -> [(Int, a)]
count lst = sortBy (compare `on` (Down . fst)) [(length $ elemIndices x lst, x) | x <- nub lst]

{--
flip theta alpha = if alpha < theta then True else False

probabilityFlip theta sample = if sample then 1 - theta else theta

--test_ad :: [Float]
test_ad = grad (\[x,y,z] -> x*y+z) [1.0,2.0,3.0]

test_ad_2 theta sample = grad (\[th] -> probabilityFlip th sample) [theta]

someFunc :: IO()
someFunc = do
  replicateM_ 10 asdf
  asdf2

sample theta = do
  alpha <- randomIO :: IO Float
  return (Lib.flip theta alpha)

asdf2 = do
  let theta = 0.5
  samples :: [Bool] <- replicateM 1000 (sample theta)
  print samples
  print $ nub samples
  print [(elem, length [x | x <- samples, x == elem]) | elem <- nub samples]
  let gdResult :: [(Float, Float)] = gaIterate 100 0.1 samples --gradientAscent (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [0.1]
  mapM_ print gdResult

gaIterate :: (Eq t, Num t, Floating b) => t -> b -> [Bool] -> [(b, b)]
gaIterate 0 hypothesis samples = [(hypothesis, loss)]
  where
    loss = sum $ [probabilityFlip hypothesis datum | datum <- samples]
gaIterate iterations hypothesis samples = (hypothesis, loss) : gaIterate (iterations-1 ) newHypothesis samples
  where
    --[gradient] = grad (\[th] -> sum [log $ probabilityFlip th datum | datum <- samples]) [hypothesis]
    loss = sum $ [probabilityFlip hypothesis datum | datum <- samples]
    gradient = sum $ map sum [grad (\[th] -> log $ probabilityFlip th datum) [hypothesis]| datum <- samples]
    newHypothesis = hypothesis + 0.0001 * gradient

asdf = do
  let theta = 0.5
  alpha <- randomIO :: IO Float
  let sample = Lib.flip theta alpha
  print (test_ad_2 theta sample)
--  print test_nn
--}