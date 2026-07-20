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
import SPLL.Typing.Infer (addTypeInfo)

-- | Run the modality pipeline on a source string and return the typed program.
-- Goes through 'addTypeInfo' (RInfer → FC certificate → ModalityInfer) so the
-- engine sees the same witnessed-binding verdicts as the production pipeline
-- (witnessed-inference milestone 2).
typeProg :: String -> Program
typeProg src =
  case tryParseProgram "<test>" src of
    Left e  -> error ("parse error: " ++ show e)
    Right p ->
      let pre = annotateProg (annotateEnumsProg p)
      in case addTypeInfo pre of
           Left e2 -> error ("typing error: " ++ show e2)
           Right (p2, _) -> p2

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
      , testCase "comparison against a Bottom operand is Bottom, not Integrate" $
          -- Regression (found by TestFuzz's typed generator, 2026-07-20):
          -- 'compareGround's "both integral-ready" branch used to accept the
          -- right operand's degenerate {S,I} ground (the same IntegralOnly
          -- state the previous case shows projects to Bottom) via a
          -- reflexive 'leqCap IntegralOnly IntegralOnly' check that is
          -- trivially true, wrongly promoting the comparison to 'Integrate'
          -- (a claimed-but-nonexistent closed-form CDF) instead of 'Bottom'.
          -- IRCompiler then crashed with "found no way to convert to IR" on
          -- this exact shape trying to honor the bogus 'Integrate' claim.
          assertEqual "" Bottom
            (mainPType "main = 2.0 * Normal > Uniform + Normal")
      , testCase "a function node carries its body pType (IRCompiler contract)" $
          -- Milestone 5: a function-typed node projects to its /body/ pType, not
          -- the lossy outer-closure 'Deterministic'. @IRCompiler@ selects
          -- prob/integrate codegen off this annotation (a top-level function's
          -- root node is its binding), so @main x = x + Uniform@ must read
          -- 'Integrate'. The internal modality is still the closure (application
          -- β-reduces); only the flat annotation changed. See
          -- @modality-cutover-delete-pinfer2@.
          assertEqual "" Integrate (mainPType "main x = x + Uniform")
      ]
  , testGroup "finiteness (decision C) keeps enumerable combinations tractable"
      [ testCase "sum of two enumerable neural Ints is Integrate, not Bottom" $
          -- main is a 2-arg function; the ++ body sits two lambdas deep, so we
          -- read it at path [0,0] rather than the (now body-typed) root node.
          assertEqual "" Integrate $
            pTypeAt "main" [0,0]
              "neural readMNist :: (Symbol -> Int) of [0,1,2,3,4,5,6,7,8,9]\n\
              \main a b = readMNist(a) ++ readMNist(b)"
      ]

  -- Milestone 6 (task @modality-mrec-msum-validation@): the structured-modality
  -- cases — the sum eliminator ('ISum') and the recursive-ADT summary ('IRec') —
  -- have no @PInfer2@ baseline, so the diff harness could not cover them. These
  -- groups pin hand-verified modalities on them. Every expectation here is the
  -- *sound* answer; where the engine is also *imprecise* (a continuous law floored
  -- to 'Integrate' instead of a recovered 'PNormal') the case carries a comment
  -- saying so and points at the resolution. Verified against the engine, not
  -- guessed.
  , testGroup "MSum validation: the sum eliminator (case/if over Either)"
      [ testCase "let-bound Either destructure idiom is Integrate" $
          -- The forward-chaining-either-let regression program. The tag is a
          -- random Bernoulli (Uniform < 0.5), so the eliminator marginalises a
          -- continuous mixture of @Normal@ and @0.0@ → 'Integrate'. This milestone
          -- only confirms the MSum eliminator's modality; the bug's own fix
          -- compiles the idiom in @IRCompiler@ and is not owned here.
          assertEqual "" Integrate $
            mainPType "main = let e = if Uniform < 0.5 then left Normal else right 0.0 \
                      \in if isLeft e then fromLeft e else fromRight e"
      , testCase "both branches continuous: Integrate" $
          assertEqual "" Integrate $
            mainPType "main = if Uniform < 0.5 then left Normal else right Uniform"
      , testCase "Either container drops the scalar family: fromLeft of a Normal is Integrate" $
          -- @left (Normal+1.0)@ builds an 'Either', not a bare 'TFloat', so
          -- 'gateScalarFamily' drops 'FamNormal' (mirrors @PInfer2.degradeNormal@
          -- for containers). The eliminator therefore yields 'Integrate', never
          -- 'PNormal' — the value's outer law is not a scalar Gaussian.
          assertEqual "" Integrate $
            mainPType "main = fromLeft (left (Normal + 1.0))"
      , testCase "deterministic-tag Either selection still drops family (Integrate)" $
          -- Contrast with the scalar det-tag selection two groups up
          -- (@if 0.1 < 0.5 then Normal else Normal + 1.0@ → 'PNormal'): there the
          -- branches are bare Gaussians and the family survives the meet. Here the
          -- same deterministic tag selects between two *Either* values, and the
          -- container gate has already stripped each branch's family, so the meet
          -- is family-free → 'Integrate'. Pins the scalar-vs-container boundary.
          assertEqual "" Integrate $
            mainPType "main = if 0.1 < 0.5 then left Normal else right Normal"
      ]
  , testGroup "MRec validation: the recursive-ADT summary"
      [ testCase "deterministic recursive-ADT access stays Deterministic" $
          -- A 'Cont'/'Empty' list of constants, destructured by @hd . tl@. The
          -- 'IRec' structural summary carries the deterministic content through
          -- without over-degrading — the honest 'Deterministic'.
          assertEqual "" Deterministic $
            mainPType "data Lst = Cont hd::Float, tl::Lst | Empty\n\
                      \main = hd (tl (Cont 0.3 (Cont 0.2 Empty)))"
      , testCase "recursive list of Normals is Integrate (family drops through MRec)" $
          -- @gaussList@: a coin-terminated recursive list each of whose elements is
          -- a 'Normal'. Sound but imprecise: the greatest-fixpoint summary meets
          -- the @[]@ base case ('Deterministic', FamNone) with the @Normal : rest@
          -- case, and the meet drops the family to 'FamNone' → 'Integrate' rather
          -- than a per-element 'PNormal'. This is the deferred MRec family-precision
          -- wrinkle (design §9 / §10): the principled fix is the totality axis
          -- [[modality-totality-axis]], because an unbounded-depth recursion is a
          -- depth-mixture, not a single Gaussian. (The design's @addNoise n@ example
          -- is not even well-typed here — integer @n - 1@ fails RInfer — so this is
          -- the realisable stand-in for the MRec family case.)
          assertEqual "" Integrate $
            mainPType "main = if Uniform > 0.5 then [] else Normal : main"
      , testCase "single-element recursive ADT carrying a Normal is Integrate" $
          -- Even with no actual recursion taken, the recursive *type* forces the
          -- 'IRec' summary, whose fixpoint meets in the @Empty@ base case and drops
          -- the family. Same wrinkle as @gaussList@, isolated to one element.
          assertEqual "" Integrate $
            mainPType "data Lst = Cont hd::Float, tl::Lst | Empty\n\
                      \main = hd (Cont (Normal + 1.0) Empty)"
      ]
  , testGroup "MProd boundary: tuple accessors recover family, user-ADT accessors do not"
      [ testCase "tuple fst recovers the per-component Gaussian (PNormal)" $
          -- The 'IProd' built by a tuple literal keeps each component's family, and
          -- @fst@/@snd@ have dedicated 'projFst'/'projSnd' projections, so the
          -- component's 'PNormal' survives.
          assertEqual "" PNormal $
            mainPType "main = fst (Normal + 1.0, Uniform)"
      , testCase "user-ADT field accessor does NOT recover the field family (Integrate)" $
          -- A user-ADT accessor (@x@ on @data P = P x::Float, y::Float@) is a plain
          -- 'InjF' with no 'projFst'/'projSnd' special-case, so it marginalises the
          -- whole 'IProd' (family already dropped by 'outerI') → 'Integrate'. Pins
          -- the boundary: only the built-in tuple accessors recover a field family
          -- today; user-ADT accessors are the imprecise (but sound) case.
          assertEqual "" Integrate $
            mainPType "data P = P x::Float, y::Float\n\
                      \main = x (P (Normal + 1.0) Uniform)"
      ]

  -- Witnessed inference, milestone 2 (design @modality-witnessed-inference@):
  -- the engine consults FC's observation-seeded witnessed-binding verdict
  -- ('isWitnessedLambda') for every random let binding. A witnessed binding is
  -- Exact FOR MARGINALIZATION in the body (recovering it from the observation is
  -- free) while its standalone law — family, density, counted once at its own
  -- slot — is untouched. These cases were the milestone-1 characterization group
  -- (pinned 'Bottom' as a known limitation); they flipped to the recovered
  -- capability when the type-level rule landed.
  --
  -- Milestone 3 (the conditional-probability fold @p_D(x*)·|J|·p(body|x=x*)@)
  -- landed via the ExpressiveNeurals merge: the IRCompiler's body-factor
  -- folding in the Apply arm is exactly that fold, and the body is re-typed
  -- deterministic-given-the-recovered-variable for dispatch (retypeDetGiven).
  -- Milestone 4's end-to-end pinning lives in @testCases/@:
  -- letWitnessedSharedLatent(Mult), letTwoUniformIndirect. The same-latent
  -- shape @(x, x+x)@ compiles (to p_x·indicator, dim 1, at parity with
  -- ExpressiveNeurals) but is NOT corpus-pinned: its degenerate support makes
  -- the joint-density convention ambiguous — warn-correlated-slots territory.
  , testGroup "witnessed inference (M2): FC-witnessed bindings lift the marginalize floor"
      [ testCase "witness (additive): shared-latent tuple recovers Integrate" $
          -- x recovered from fst, then u2 = y - x from snd (Jacobian 1): the
          -- joint p(x)·p(y-x) is a full density, dim 2.
          assertEqual "" Integrate $
            mainPType "main = let x = Uniform in let y = x + Uniform in (x, y)"
      , testCase "witness (multiplicative): shared-latent tuple recovers Integrate" $
          -- Same shape with @mult@: u2 = y / x (Jacobian 1/|x|) — the recovery
          -- is not specific to @plus@.
          assertEqual "" Integrate $
            mainPType "main = let x = Uniform in let y = x * Uniform in (x, y)"
      , testCase "direct witness without the intermediate let" $
          -- The same recovery with the combination inline in the observed slot.
          assertEqual "" Integrate $
            mainPType "main = let x = Uniform in (x, x + Uniform)"
      , testCase "family preservation: let x = Normal in x stays PNormal" $
          -- The once-counting rule binds x witnessed WITHOUT erasing its
          -- standalone law — the naive Exact binding would regress this to
          -- Deterministic (or, via meet with the rhs, to Integrate).
          assertEqual "" PNormal $
            mainPType "main = let x = Normal in x"
      , testCase "family survives a witnessed affine combination" $
          -- x + 1.0 is a deterministic image of the witnessed x: still
          -- witnessed downstream, and tryNormalClosure keeps the family.
          assertEqual "" PNormal $
            mainPType "main = let x = Normal in x + 1.0"
      ]

  -- Permanent soundness guards. Unlike the characterization group above, these MUST
  -- stay 'Bottom' FOREVER — including after [[modality-witnessed-inference]] lands.
  -- They are genuine convolutions / multi-residual-latent combinations that need
  -- the in-house quadrature the language disclaims (design decision B): no single
  -- sibling is observed that would witness the residual randomness away. They mark
  -- the boundary the witnessed-inference fix must NOT cross. (@Uniform + Normal@ as
  -- a bare sum is already pinned in the "ground rules vs PInfer2 parity" group.)
  , testGroup "continuous convolutions stay Bottom (permanent soundness guards)"
      [ testCase "y-only: x unobserved, so x + Uniform is a real convolution" $
          -- The discriminator vs the additive witness: FC's @isInvertibleLambda@ for
          -- the @x@-binding is False here (x is not observed) but True in the witness.
          assertEqual "" Bottom $
            mainPType "main = let x = Uniform in let y = x + Uniform in y"
      , testCase "let-bound sum of two continuous laws" $
          assertEqual "" Bottom (mainPType "main = let z = Uniform + Normal in z")
      , testCase "product of two unobserved continuous laws" $
          assertEqual "" Bottom (mainPType "main = Uniform * Uniform")
      , testCase "a convolution component floors the whole tuple" $
          assertEqual "" Bottom (mainPType "main = (Uniform + Normal, Uniform)")
      , testCase "two residual latents in one observed slot cannot both be witnessed" $
          -- Adjacent to the recoverable witness but MUST stay Bottom: observing the
          -- second slot gives one equation for two fresh draws (u2, u3). The
          -- @marginalize@ floor self-enforces this even once @x@ is witnessed — the
          -- key guard that the witnessed-inference fix promotes ONLY single-residual
          -- recoveries, never a genuine multi-latent convolution.
          assertEqual "" Bottom $
            mainPType "main = let x = Uniform in (x, x + Uniform + Uniform)"
      ]
  ]
