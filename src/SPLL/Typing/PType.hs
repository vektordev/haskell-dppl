module SPLL.Typing.PType where

import Data.Bifunctor (second)

newtype TVar = TV String
  deriving (Show, Eq, Ord)
  
data PType = Deterministic
           | Integrate
           | Chaos
           | PIdent String [(PType, PType)]
           | PComb PType PType
           | TVar TVar
           deriving (Show, Eq)

--TODO: Assert that downgrade Chaos Deterministic = Chaos
downgrade :: PType -> PType -> PType
downgrade (PIdent name assigns) right = reduce
  (PIdent name $ map (Data.Bifunctor.second (downgrade right)) assigns)
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
  (PIdent name $ map (Data.Bifunctor.second (upgrade right)) assigns)
upgrade left p@(PIdent _ _) = downgrade p left
upgrade _ Deterministic = Deterministic
upgrade Deterministic _ = Deterministic
upgrade Chaos _ = Chaos
upgrade _ Chaos = Chaos
upgrade Integrate Integrate = Integrate
