module SPLL.Typing.PType
  ( TVar(..)
  , PType(..)
  , isBasicType
  , downgrade
  , downgrade2
  , upgrade
  , mostChaotic
  , mostStructured
  ) where

newtype TVar = TV String
  deriving (Show, Eq, Ord)
  
data PType = Deterministic
           | PNormal     -- Gaussian in linear space; carries runtime-computable (mu, sigma)
           | PLogNormal  -- Gaussian in log space; carries runtime-computable (mu_log, sigma_log)
           | Integrate
           | Prob
           | Bottom
           | PArr PType PType
           | TVar TVar
           | NotSetYet
           deriving (Show, Eq, Ord)
-- only use ord instance for algorithmic convenience, not for up/downgrades / lattice work.
-- Lattice (partial order):
--   Deterministic > PNormal, PLogNormal > Integrate > Prob > Bottom
--   PNormal and PLogNormal are incomparable (different distribution families)

infixr `PArr`

basicPTypes :: [PType]
basicPTypes = [Deterministic, PNormal, PLogNormal, Integrate, Prob, Bottom]

isBasicType :: PType -> Bool
isBasicType ty = ty `elem` basicPTypes

-- | Elements strictly below a given PType in the lattice.
strictlyBelow :: PType -> [PType]
strictlyBelow Deterministic = [PNormal, PLogNormal, Integrate, Prob, Bottom]
strictlyBelow PNormal       = [Integrate, Prob, Bottom]
strictlyBelow PLogNormal    = [Integrate, Prob, Bottom]
strictlyBelow Integrate     = [Prob, Bottom]
strictlyBelow Prob          = [Bottom]
strictlyBelow _             = []

partialOrd :: PType -> PType -> Maybe Ordering
partialOrd ty1 ty2
  | not (isBasicType ty1)         = Nothing
  | not (isBasicType ty2)         = Nothing
  | ty1 == ty2                    = Just EQ
  | ty2 `elem` strictlyBelow ty1 = Just GT
  | ty1 `elem` strictlyBelow ty2 = Just LT
  | otherwise                     = Nothing
    

downgrade :: PType -> PType -> PType
-- Incomparable siblings: meet is their greatest lower bound = Integrate
downgrade PNormal    PLogNormal = Integrate
downgrade PLogNormal PNormal    = Integrate
downgrade ty1 ty2 = maybe Bottom (\ord -> if ord == LT then ty1 else ty2) order
  where order = partialOrd ty1 ty2
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
-- Incomparable siblings: join is their least upper bound = Deterministic
upgrade PNormal    PLogNormal = Deterministic
upgrade PLogNormal PNormal    = Deterministic
upgrade ty1 ty2 = maybe Bottom (\ord -> if ord == GT then ty1 else ty2) order
  where order = partialOrd ty1 ty2
{-upgrade _ Deterministic = Deterministic
upgrade Deterministic _ = Deterministic
upgrade Chaos _ = Chaos
upgrade _ Chaos = Chaos
upgrade Integrate Integrate = Integrate-}

mostChaotic :: [PType] -> PType
mostChaotic = foldl1 downgrade

mostStructured :: [PType] -> PType
mostStructured = foldl1 upgrade
