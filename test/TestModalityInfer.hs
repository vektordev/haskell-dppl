-- | Soundness tests for the milestone-4 modality inference engine
-- ('SPLL.Typing.ModalityInfer'), task @modality-inference-engine@.
--
-- The diff harness ('ModalityDiff') shows the engine never loses a program's
-- typeability and where it diverges from @PInfer2@; it does not by itself prove
-- the more-permissive verdicts are /sound/. These tests pin the intended,
-- hand-verified modality on the design's motivating programs (§6 of
-- @modality-typesystem-port@ / @modality-port-lattice-core@) and on the cases
-- where the engine is deliberately /more conservative/ than @PInfer2@ (let-bound
-- random variables, continuous mixtures), so a regression in either direction is
-- caught.
module TestModalityInfer (modalityInferTests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

import SPLL.Lang.Types (Program(..), Expr, TypeInfo(..))
import SPLL.Lang.Lang (getTypeInfo, getSubExprs)
import SPLL.Typing.PType (PType(..))
import SPLL.Parser (tryParseProgram)
import SPLL.Analysis (annotateEnumsProg)
import SPLL.Typing.ForwardChaining (annotateProg)
import SPLL.Typing.RInfer (addRTypeInfo)
import SPLL.Typing.ModalityInfer (addModalityPTypeInfo)

-- | Run the modality pipeline on a source string and return the typed program.
typeProg :: String -> Program
typeProg src =
  case tryParseProgram "<test>" src of
    Left e  -> error ("parse error: " ++ show e)
    Right p ->
      let pre = annotateProg (annotateEnumsProg p)
      in case addRTypeInfo pre >>= addModalityPTypeInfo of
           Left e2 -> error ("typing error: " ++ show e2)
           Right p2 -> p2

-- | The 'PType' on the root node of the named top-level function.
rootPTypeOf :: String -> String -> PType
rootPTypeOf fname src =
  case lookup fname (functions (typeProg src)) of
    Just body -> pType (getTypeInfo body)
    Nothing   -> error ("no function " ++ fname)

mainPType :: String -> PType
mainPType = rootPTypeOf "main"

-- | The 'PType' at a child path beneath the named function's body
-- (same scheme as the diff harness: a list of child indices).
pTypeAt :: String -> [Int] -> String -> PType
pTypeAt fname path src =
  case lookup fname (functions (typeProg src)) of
    Just body -> pType (getTypeInfo (descend path body))
    Nothing   -> error ("no function " ++ fname)
  where descend []     e = e
        descend (i:is) e = descend is (getSubExprs e !! i)

modalityInferTests :: TestTree
modalityInferTests = testGroup "ModalityInfer"
  [ testGroup "motivating programs (family composes through structured Mod)"
      [ testCase "MProd: tuple round-trip stays PNormal" $
          -- fst/snd recover the per-component family; the affine sum of two
          -- Normals is Normal (design program 1).
          assertEqual "" PNormal $
            mainPType "main = let pair = (Normal + 1.0, 2.0 * Normal) \
                      \in fst pair + snd pair"
      , testCase "MArr/phi: family survives application (β-reduction)" $
          -- g(f(Normal)) with f,g affine: the closure transfer keeps the family
          -- through application, which a flat layer cannot (design program 2).
          assertEqual "" PNormal $
            mainPType "main = let f = \\x -> x + 1.0 \
                      \in let g = \\y -> 2.0 * y in g (f Normal)"
      , testCase "MSum mixture is a deliberate non-goal: stays Integrate" $
          -- a marginalised random-tag mixture of two Gaussians is not Gaussian
          -- (design program 4): the family must be dropped.
          assertEqual "" Integrate $
            mainPType "main = if Uniform < 0.5 then Normal + 1.0 else 2.0 * Normal"
      , testCase "deterministic-tag selection of a Normal keeps the family" $
          -- the honest survivor of program 4: when the condition is known, the
          -- branch selection preserves the family.
          assertEqual "" PNormal $
            mainPType "main = if 0.1 < 0.5 then Normal else Normal + 1.0"
      ]
  , testGroup "soundness: more conservative than PInfer2 (no over-claim)"
      [ testCase "let-bound random variable is Integrate, not Deterministic" $
          -- PInfer2 wrongly types a let-bound random occurrence Deterministic
          -- (binder defaults to det); the modality engine binds it to the
          -- argument's real law.
          assertEqual "" Integrate $
            mainPType "main = let x = Uniform in x + 1.0"
      , testCase "continuous if-mixture is not Deterministic (meet, not join)" $
          -- the prototype's join optimism would type this Deterministic; the
          -- meet of the branches is the sound answer.
          assertEqual "" Integrate $
            mainPType "main = if Uniform < 0.5 then Normal else 1.0"
      , testCase "a continuous result is never claimed Deterministic" $
          assertBool "expected a non-Deterministic continuous result" $
            mainPType "main = Uniform + Normal" /= Deterministic
      ]
  , testGroup "ground rules vs PInfer2 parity"
      [ testCase "Normal is PNormal" $
          assertEqual "" PNormal (mainPType "main = Normal")
      , testCase "Uniform is Integrate" $
          assertEqual "" Integrate (mainPType "main = Uniform")
      , testCase "a constant is Deterministic" $
          assertEqual "" Deterministic (mainPType "main = 1.0")
      , testCase "affine shift of a Normal stays PNormal" $
          assertEqual "" PNormal (mainPType "main = Normal + 1.0")
      , testCase "scale of a Normal stays PNormal" $
          assertEqual "" PNormal (mainPType "main = 2.0 * Normal")
      , testCase "exp of a Normal is LogNormal" $
          assertEqual "" PLogNormal (mainPType "main = exp(Normal)")
      , testCase "sum of two continuous laws has no closed density (Bottom)" $
          -- {S,I} (integral but no density) projects to Bottom, matching
          -- PInfer2's resolvePlusCons.
          assertEqual "" Bottom (mainPType "main = Uniform + Normal")
      , testCase "a syntactic function value is Deterministic (outer modality)" $
          assertEqual "" Deterministic (mainPType "main x = x + Uniform")
      ]
  , testGroup "finiteness (decision C) keeps enumerable combinations tractable"
      [ testCase "sum of two enumerable neural Ints is Integrate, not Bottom" $
          -- main is a 2-arg function, so its root node is the (Deterministic)
          -- closure; the ++ body sits two lambdas deep.
          assertEqual "" Integrate $
            pTypeAt "main" [0,0]
              "neural readMNist :: (Symbol -> Int) of [0,1,2,3,4,5,6,7,8,9]\n\
              \main a b = readMNist(a) ++ readMNist(b)"
      ]
  ]
