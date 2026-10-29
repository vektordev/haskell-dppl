-- | The pure part of the affine-Gaussian and joint-Gaussian machinery: the
-- 'AffineForm' record and its collapse to a scalar Normal, the tuple-field
-- path helpers, the Cholesky-based multivariate density and its positivity
-- test. The engines that build forms from expressions ('affineFormOf',
-- 'jointAffineApply', ...) read 'CompilerMetadata' and call back into
-- 'toIRInference', so they stay in @SPLL.IRCompiler@ until the knot is cut
-- (task ircompiler-knot-tied-split). Moved out of @SPLL.IRCompiler@ (task
-- ircompiler-leaf-extractions).
module SPLL.IRCompiler.Affine
  ( AffineForm(..)
  , collapseAffine
  , readsAffine
  , tupleFieldPaths
  , fieldSampleAt
  , anyOutsideField
  , stepInto
  , jointGaussianDensity
  , choleskyPositive
  , irConstFloat
  ) where

import SPLL.IntermediateRepresentation
import SPLL.IRUtil (irSqrt)
import SPLL.Lang.Lang
import SPLL.Lang.Types
import SPLL.Semiring
import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | A value's law as an affine combination of independent standard-normal
-- latents, @c + Σᵢ aᵢ·εᵢ@. The latents are keyed by the chain name of the
-- env-free Gaussian leaf that introduced them, so two reads of one
-- marginalised variable ('affineVars') share their latents (@x + x@ is @2ε@, not
-- @ε₁ + ε₂@), while every other leaf is a fresh draw.
data AffineForm = AffineForm
  { afConst  :: IRExpr
  , afCoeffs :: Map.Map ChainName IRExpr
  } deriving (Show)

-- | Collapse a form to a scalar Normal's @(mu, sigma)@: the constant, and the
-- Euclidean norm of the coefficient vector (the latents are independent).
collapseAffine :: AffineForm -> (IRExpr, IRExpr)
collapseAffine (AffineForm c coeffs) = case Map.elems coeffs of
  [a] -> (c, IRUnaryOp OpAbs a)
  as  -> (c, irSqrt (foldr1 (IROp OpPlus) [IROp OpMult a a | a <- as]))

-- | Does an expression read one of these variables?
readsAffine :: Set.Set String -> Expr -> Bool
readsAffine names e = not (Set.null (freeVarsExpr e `Set.intersection` names))

-- | The fields of a tree of tuple constructors, each with its access path.
tupleFieldPaths :: Expr -> [([Bool], Expr)]
tupleFieldPaths (Expr _ (InjF (Named "TCons") [a, b])) =
  [ (False : p, e) | (p, e) <- tupleFieldPaths a ] ++ [ (True : p, e) | (p, e) <- tupleFieldPaths b ]
tupleFieldPaths e = [([], e)]

-- | The sample of a tuple field, and whether it is @ANY@: the field's own
-- sample or any tuple around it. The test reads each enclosing sample only
-- once the one outside it is known not to be @ANY@, since an accessor on
-- @ANY@ fails.
fieldSampleAt :: IRExpr -> [Bool] -> (IRExpr, IRExpr)
fieldSampleAt sample path = (foldl stepInto sample path, anyAlong sample path)
  where
    anyAlong s [] = IRUnaryOp OpIsAny s
    anyAlong s (b : bs) = IRIf (IRUnaryOp OpIsAny s) constTrueIR (anyAlong (stepInto s b) bs)

-- | Whether a tuple enclosing the field at this path is @ANY@ (the field's
-- own sample excluded).
anyOutsideField :: IRExpr -> [Bool] -> IRExpr
anyOutsideField _ [] = constFalseIR
anyOutsideField s [_] = IRUnaryOp OpIsAny s
anyOutsideField s (b : bs) = IRIf (IRUnaryOp OpIsAny s) constTrueIR (anyOutsideField (stepInto s b) bs)

stepInto :: IRExpr -> Bool -> IRExpr
stepInto s b = IRDestruct (if b then AcSnd else AcFst) s

-- | The density of a multivariate Gaussian at residual @r@ (sample minus
-- mean), covariance entries @cov i j@, through its Cholesky factor @L@: with
-- @z = L⁻¹ r@ the density is @∏ φ(zᵢ) / Lᵢᵢ@, a product of standard normal
-- leaves the semiring multiplies, so log space keeps a deep tail's precision
-- as the scalar leaf does. Unrolled into let-bindings local to the density,
-- which is selected on which fields are ANY and must not be evaluated
-- outside its arm. With @guarded@, a pivot that is not positive at run time
-- (a covariance singular for these inputs) is an error rather than a NaN.
jointGaussianDensity :: Semiring -> Bool -> [IRExpr] -> (Int -> Int -> IRExpr) -> CompilerMonad IRExpr
jointGaussianDensity sr guarded resid cov = go 0 Map.empty Map.empty []
  where
    n = length resid
    go i ls zs factors
      | i == n = return (foldr1 (srTimes sr) (reverse factors))
      | otherwise = do
          -- The off-diagonal entries of row i of L, then its pivot.
          (binds, ls') <- foldM (\(bs, m) j -> do
                v <- mkVariable "chol"
                let e = IROp OpDiv (IROp OpSub (cov i j) (sumOf [ IROp OpMult (m Map.! (i, k)) (m Map.! (j, k)) | k <- [0 .. j - 1] ]))
                                   (m Map.! (j, j))
                return (bs ++ [(v, e)], Map.insert (i, j) (IRVar v) m)) ([], ls) [0 .. i - 1]
          pv <- mkVariable "pivot"
          lv <- mkVariable "chol"
          zv <- mkVariable "z"
          let pivot = IROp OpSub (cov i i) (sumOf [ IROp OpMult (ls' Map.! (i, k)) (ls' Map.! (i, k)) | k <- [0 .. i - 1] ])
              ls'' = Map.insert (i, i) (IRVar lv) ls'
              z = IROp OpDiv (IROp OpSub (resid !! i) (sumOf [ IROp OpMult (ls'' Map.! (i, k)) (zs Map.! k) | k <- [0 .. i - 1] ])) (IRVar lv)
              factor = scaledNormalDensity sr (IRVar zv) [IRVar lv]
          rest <- go (i + 1) ls'' (Map.insert i (IRVar zv) zs) (factor : factors)
          let pivoted = IRLetIn lv (irSqrt (IRVar pv)) (IRLetIn zv z rest)
              checked
                | guarded = IRIf (IROp OpGreaterThan (IRVar pv) const0) pivoted
                    (IRError "joint Gaussian density: the covariance of the correlated tuple fields is singular for these inputs (design affine-gaussian-forms M4)")
                | otherwise = pivoted
          return (foldr (\(v, e) acc -> IRLetIn v e acc) (IRLetIn pv pivot checked) binds)
    sumOf [] = const0
    sumOf xs = foldr1 (IROp OpPlus) xs

-- | Is a constant symmetric matrix positive definite? Its Cholesky pivots
-- stay clear of zero, relative to the diagonal.
choleskyPositive :: [[Double]] -> Bool
choleskyPositive m = go 0 Map.empty
  where
    n = length m
    at i j = m !! i !! j
    go :: Int -> Map.Map (Int, Int) Double -> Bool
    go i ls
      | i == n = True
      | otherwise =
          let ls' = foldl (\acc j -> Map.insert (i, j) ((at i j - sum [ acc Map.! (i, k) * acc Map.! (j, k) | k <- [0 .. j - 1] ]) / acc Map.! (j, j)) acc) ls [0 .. i - 1]
              pivot = at i i - sum [ (ls' Map.! (i, k)) ^ (2 :: Int) | k <- [0 .. i - 1] ]
          in pivot > 1e-12 * max 1 (abs (at i i)) && go (i + 1) (Map.insert (i, i) (sqrt pivot) ls')

-- | The value of an IR expression built from number literals by arithmetic.
irConstFloat :: IRExpr -> Maybe Double
irConstFloat e = case e of
  IRConst (VFloat d) -> Just d
  IRConst (VInt k) -> Just (fromIntegral k)
  IROp OpPlus a b -> (+) <$> irConstFloat a <*> irConstFloat b
  IROp OpSub a b -> (-) <$> irConstFloat a <*> irConstFloat b
  IROp OpMult a b -> (*) <$> irConstFloat a <*> irConstFloat b
  IRUnaryOp OpNeg a -> negate <$> irConstFloat a
  IRUnaryOp OpAbs a -> abs <$> irConstFloat a
  _ -> Nothing
