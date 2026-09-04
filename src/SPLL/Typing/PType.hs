module SPLL.Typing.PType
  ( TVar(..)
  , PType(..)
  ) where

newtype TVar = TV String
  deriving (Show, Eq, Ord)
  
data PType = Deterministic
           | PNormal     -- Gaussian in linear space; carries runtime-computable (mu, sigma)
           | PLogNormal  -- Gaussian in log space; carries runtime-computable (mu_log, sigma_log)
           | Integrate
           | Bottom
           | PArr PType PType
           | TVar TVar
           | NotSetYet
           deriving (Show, Eq, Ord)
-- only use ord instance for algorithmic convenience, not for up/downgrades / lattice work.
-- Lattice (partial order):
--   Deterministic > PNormal, PLogNormal > Integrate > Bottom
--   PNormal and PLogNormal are incomparable (different distribution families)
-- Note: "Integrate" means the CDF is evaluable via a trusted, O(1) special-function
-- (e.g. erf for the Gaussian) -- not necessarily closed-form. The old density-only
-- rung (density known, CDF only via in-house quadrature) was provably uninhabited
-- under the no-Class-B-quadrature policy and has been removed.
--
-- This module deliberately carries no lattice *operations*. 'PType' is the flat,
-- lossy projection of the real capability lattice, which lives in
-- 'SPLL.Typing.Modality' -- 'leqGround'/'joinGround'/'meetGround' over
-- (capability set x support-finiteness x distribution family), flattened onto the
-- rungs above by 'projectGround'. The meet of the two incomparable siblings, for
-- instance, is not a special case there but a consequence: 'meetFamily' of two
-- distinct families is 'FamNone', which 'projectGround' reads as 'Integrate'.
--
-- A superseded set of combinators (isBasicType, strictlyBelow, partialOrd,
-- downgrade, downgrade2, upgrade, and the foldl1 wrappers mostChaotic /
-- mostStructured) used to live here. Their last callers went away with
-- 48c0543, which simplified 'InferenceRule' to a return-type rule and dropped its
-- resultingPType field; they survived only because the explicit export list hides
-- dead code from -Wunused-top-binds. Deleted by task
-- ptype-mostchaotic-foldl1-empty-input.

infixr `PArr`
