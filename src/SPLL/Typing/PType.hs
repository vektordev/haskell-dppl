module SPLL.Typing.PType where

import Data.Bifunctor (second)

newtype TVar = TV String
  deriving (Show, Eq, Ord)
  
data PType = Deterministic
           | Integrate
           | Prob
           | Bottom
           | Chaos
           | PIdent String [(PType, PType)]
           | PArr PType PType
           | TVar TVar
           | NotSetYet
           deriving (Show, Eq, Ord)
basicPTypes :: [PType] 
basicPTypes =  [Deterministic, Integrate, Chaos, Prob, Bottom]
isBasicType :: PType -> Bool
isBasicType ty = ty `elem` basicPTypes
--TODO: Remove Chaos
downgrade :: PType -> PType -> PType
downgrade (PIdent name assigns) right = reduce
  (PIdent name $ map (Data.Bifunctor.second (downgrade right)) assigns)
downgrade left p@(PIdent _ _) = downgrade p left
downgrade Chaos _ = Chaos
downgrade _ Chaos = Chaos
downgrade Bottom _ = Bottom
downgrade _ Bottom = Bottom
downgrade Prob _ = Prob
downgrade _ Prob = Prob
downgrade Integrate _ = Integrate
downgrade _ Integrate = Integrate
downgrade Deterministic Deterministic = Deterministic

downgrade2 :: PType -> PType -> PType
downgrade2 leftP rightP = if upgrade leftP rightP == Deterministic
              then downgrade leftP rightP
              else Chaos
reduce :: PType -> PType
reduce p@(PIdent _ [(_, x), (_,y), (_,z)]) = if x == y && y == z then x else p
reduce x = x


infixr `PArr`

upgrade :: PType -> PType -> PType
upgrade (PIdent name assigns) right = reduce
  (PIdent name $ map (Data.Bifunctor.second (upgrade right)) assigns)
upgrade left p@(PIdent _ _) = downgrade p left
upgrade _ Deterministic = Deterministic
upgrade Deterministic _ = Deterministic
upgrade Chaos _ = Chaos
upgrade _ Chaos = Chaos
upgrade Integrate Integrate = Integrate
