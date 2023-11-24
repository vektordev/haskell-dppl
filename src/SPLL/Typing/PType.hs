module SPLL.Typing.PType where

import Data.Bifunctor (second)

newtype TVar = TV String
  deriving (Show, Eq, Ord)
  
data PType = Deterministic
           | Integrate
           | Prob
           | Bottom
           | PArr PType PType
           | TVar TVar
           | NotSetYet
           deriving (Show, Eq, Ord)
           
infixr `PArr`

basicPTypes :: [PType] 
basicPTypes =  [Deterministic, Integrate, Prob, Bottom]

isBasicType :: PType -> Bool
isBasicType ty = ty `elem` basicPTypes

partialOrd :: PType -> PType -> Maybe Ordering
partialOrd ty1 ty2 
  | not $ isBasicType ty1 = Nothing
  | not $ isBasicType ty2 = Nothing
  | ty1 == ty2 = Just EQ
  | ty1 == Deterministic = Just GT
  | ty2 == Deterministic = Just LT
  | ty1 == Integrate = Just GT
  | ty2 == Integrate = Just LT
  | ty1 == Prob = Just GT
  | ty2 == Prob = Just LT
    

downgrade :: PType -> PType -> PType
downgrade ty1 ty2 = if ty1 <= ty2 then ty1 else ty2
{-downgrade Bottom _ = Bottom
downgrade _ Bottom = Bottom
downgrade Prob _ = Prob
downgrade _ Prob = Prob
downgrade Integrate _ = Integrate
downgrade _ Integrate = Integrate
downgrade Deterministic Deterministic = Deterministic-}

downgrade2 :: PType -> PType -> PType
downgrade2 leftP rightP = if upgrade leftP rightP == Deterministic
              then downgrade leftP rightP
              else Bottom

upgrade :: PType -> PType -> PType
upgrade ty1 ty2
  | ty1 >= ty2 = ty1
  | otherwise = ty2
{-upgrade _ Deterministic = Deterministic
upgrade Deterministic _ = Deterministic
upgrade Chaos _ = Chaos
upgrade _ Chaos = Chaos
upgrade Integrate Integrate = Integrate-}

mostChaotic :: [PType] -> PType
mostChaotic = foldl1 downgrade

mostStructured :: [PType] -> PType
mostStructured = foldl1 upgrade
