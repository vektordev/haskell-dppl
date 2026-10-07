-- | Milestone-1 tests for 'SPLL.Typing.Modality': the capability lattice, the
-- marginalization rule, the family axis, the smart constructor, structured
-- combinators, and the family-aware projection onto 'PType'.
--
-- These mirror the algebraic checks from the @nest_typing@ prototype's
-- @test/Spec.hs@ (the lattice + structural ones; the inference-driven cases are
-- milestone 4), and add the milestone-1 acceptance checks: @marg@ always drops
-- the family, the projection round-trips, the smart constructor rejects an
-- ill-formed family, and the four motivating programs from
-- @modality-port-lattice-core@ project as specified (their expected modalities
-- are hand-authored here; full end-to-end inference is milestones 4 and 6).
module TestModality (modalityTests) where

import Control.Exception (try, evaluate, ErrorCall)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, assertFailure, (@?=))

import SPLL.Typing.Modality
import SPLL.Typing.PType (PType(..))
import SPLL.Typing.RType (RType(..))
import SPLL.Typing.ModalityInfer (IMod(..), toMod)

-- Handy ground modalities ------------------------------------------------------

det :: GroundMod
det = topGround                                   -- det/fin

densInf :: GroundMod
densInf = GroundMod DensityOnly Infinite FamNone  -- dens/inf

densIntFin :: GroundMod
densIntFin = GroundMod DensInt Finite FamNone     -- densint/fin

normalG :: GroundMod
normalG = groundMod DensInt Infinite FamNormal    -- densint/inf, Normal family

logNormalG :: GroundMod
logNormalG = groundMod DensInt Infinite FamLogNormal

modalityTests :: TestTree
modalityTests = testGroup "Modality"
  [ latticeTests
  , margTests
  , mixtureTests
  , familyTests
  , smartCtorTests
  , projectionTests
  , combinatorTests
  , applicationTests
  , motivatingProgramTests
  ]

-- The base capability lattice (prototype Spec lines 22-39) ----------------------

latticeTests :: TestTree
latticeTests = testGroup "capability lattice"
  [ testCase "dens join int = densint" $
      joinCap DensityOnly IntegralOnly @?= DensInt
  , testCase "dens meet int = sample" $
      meetCap DensityOnly IntegralOnly @?= SampleOnly
  , testCase "det is top" $
      assertBool "all <= Exact" (all (`leqCap` Exact) allCapabilitySets)
  , testCase "opaque is bottom" $
      assertBool "Opaque <= all" (all (Opaque `leqCap`) allCapabilitySets)
  , testCase "dens, int incomparable" $
      assertBool "neither subtypes the other"
        (not (leqCap DensityOnly IntegralOnly) && not (leqCap IntegralOnly DensityOnly))
  ]

-- The marginalization combinator ----------------------------------------------

margTests :: TestTree
margTests = testGroup "marginalize"
  [ testCase "marg with Dirac is free (left)" $
      marginalize det densInf @?= densInf
  , testCase "marg with Dirac is free (right)" $
      marginalize densInf det @?= densInf
  , testCase "dens(inf) * dens(inf) -> int(inf) (convolution)" $
      marginalize densInf densInf @?= GroundMod IntegralOnly Infinite FamNone
  , testCase "densint(fin) * densint(fin) -> densint(fin) (finite stays computable)" $
      marginalize densIntFin densIntFin @?= GroundMod DensInt Finite FamNone
  , testCase "marg always drops family (generic combination)" $
      gFam (marginalize normalG densInf) @?= FamNone
  , testCase "marg drops family even in the Dirac short-circuit (shiftSem is M4)" $
      gFam (marginalize det normalG) @?= FamNone
  ]

-- The if mixture combinator (task finiteness-single-producer) -----------------

mixtureTests :: TestTree
mixtureTests = testGroup "mixtureGround"
  [ testCase "a Dirac condition is free and keeps the family" $
      mixtureGround det normalG @?= normalG
  , testCase "an analytic condition of infinite support keeps the branches' density" $
      -- No Fin is read from the condition: the equation never enumerates it.
      mixtureGround (GroundMod DensInt Infinite FamNone) normalG
        @?= GroundMod DensInt Infinite FamNone
  , testCase "the support finiteness is the branches'" $
      gFin (mixtureGround (GroundMod DensInt Infinite FamNone) densIntFin) @?= Finite
  , testCase "a sample-only condition leaves sampling only" $
      mixtureGround (GroundMod SampleOnly Finite FamNone) densIntFin
        @?= GroundMod SampleOnly Finite FamNone
  , testCase "a degenerate {S,I} condition has no usable P(cond): sampling only" $
      mixtureGround (GroundMod IntegralOnly Infinite FamNone) densIntFin
        @?= GroundMod SampleOnly Finite FamNone
  , testCase "deterministic branches under a random condition are analytic, not Dirac" $
      mixtureGround (GroundMod DensInt Infinite FamNone) det
        @?= GroundMod DensInt Finite FamNone
  ]

-- The orthogonal family axis ---------------------------------------------------

familyTests :: TestTree
familyTests = testGroup "family axis"
  [ testCase "join of equal families is preserved" $
      joinFamily FamNormal FamNormal @?= FamNormal
  , testCase "join of mismatched families bottoms to None" $
      joinFamily FamNormal FamLogNormal @?= FamNone
  , testCase "meet of equal families is preserved" $
      meetFamily FamNormal FamNormal @?= FamNormal
  , testCase "meet of mismatched families bottoms to None" $
      meetFamily FamNormal FamLogNormal @?= FamNone
  ]

-- The gFam => DensInt smart constructor ----------------------------------------

smartCtorTests :: TestTree
smartCtorTests = testGroup "groundMod smart constructor"
  [ testCase "accepts a family on DensInt" $
      assertBool "valid" (validGroundMod (GroundMod DensInt Infinite FamNormal))
  , testCase "rejects a family on a non-DensInt cap" $
      assertBool "invalid" (not (validGroundMod (GroundMod DensityOnly Finite FamNormal)))
  , testCase "groundMod fails loudly on an ill-formed family" $ do
      r <- try (evaluate (groundMod DensityOnly Finite FamNormal))
             :: IO (Either ErrorCall GroundMod)
      case r of
        Left _  -> return ()
        Right _ -> assertFailure "expected groundMod to reject a family on a non-DensInt cap"
  ]

-- Projection onto the flat PType (design §6) -----------------------------------

projectionTests :: TestTree
projectionTests = testGroup "projection onto PType"
  [ testCase "{S,D,I} x Normal    -> PNormal"      $ projectGround normalG    @?= PNormal
  , testCase "{S,D,I} x LogNormal -> PLogNormal"   $ projectGround logNormalG @?= PLogNormal
  , testCase "{S,D,I} (no family) -> Integrate"    $
      projectGround (GroundMod DensInt Infinite FamNone) @?= Integrate
  , testCase "{S,D,I,T} -> Deterministic"          $ projectGround det @?= Deterministic
  , testCase "{} -> Bottom (opaque)" $
      projectGround (GroundMod Opaque Infinite FamNone) @?= Bottom
  , testCase "{S} -> Bottom (sample-only)" $
      projectGround (GroundMod SampleOnly Infinite FamNone) @?= Bottom
  , testCase "{S,D} partial -> Bottom (held unreachable, would overpromise)" $
      projectGround densInf @?= Bottom
  , testCase "{S,I} partial -> Bottom (held unreachable, would overpromise)" $
      projectGround (GroundMod IntegralOnly Infinite FamNone) @?= Bottom
  ]

-- Structured combinators -------------------------------------------------------

combinatorTests :: TestTree
combinatorTests = testGroup "combinators"
  [ testCase "joinModality of grounds = MGround . joinGround" $
      joinModality (MGround densInf) (MGround det)
        @?= MGround (joinGround densInf det)
  , testCase "applyOuter through a Dirac arg keeps the outer (family dropped)" $
      applyOuter normalG (MGround det) @?= MGround (normalG { gFam = FamNone })
  , testCase "bottomModality of a scalar is ground bottom" $
      bottomModality TFloat @?= MGround bottomGround
  , testCase "bottomModality of a tuple mirrors the product shape" $
      bottomModality (Tuple TFloat TFloat) @?= MProd (MGround bottomGround) (MGround bottomGround)
  , testCase "bottomModality of an arrow has a ground-bottom outer" $
      outerGround (bottomModality (TArrow TFloat TFloat)) @?= bottomGround
  , testCase "bottom <: top, but not conversely" $
      assertBool "bottom <: top"
        (subMod (MGround bottomGround) (MGround topGround)
         && not (subMod (MGround topGround) (MGround bottomGround)))
  , testCase "runTransfer looks an identity transfer up by capability" $
      runTransfer (mkTransfer MGround) (MGround (GroundMod DensInt Infinite FamNone))
        @?= MGround (GroundMod DensInt Infinite FamNone)
  , testCase "function subtyping is covariant in the outer modality" $
      let phi = mkTransfer (const (MGround bottomGround))
          arrLo = MArr bottomGround phi
          arrHi = MArr topGround phi
      in assertBool "arrLo <: arrHi, not conversely"
           (subMod arrLo arrHi && not (subMod arrHi arrLo))
  ]

-- The application rule of the serialisable layer: 'applyMod', 'applyOuter' on
-- a function-valued result, 'joinModality'/'joinTransfer' on arrows, and the
-- 'toMod' tabulation of an 'IArr' closure (investigation
-- modality-function-space-test-coverage, finding F2: none of these had a test).

applicationTests :: TestTree
applicationTests = testGroup "application rule (applyMod / transfers)"
  [ testCase "a Dirac function choice keeps the conditional result, family included" $
      applyMod (MArr det toNormal) (MGround densInf) @?= MGround normalG
  , testCase "a random function choice marginalizes the result and drops the family" $
      let r = applyMod (MArr densIntFin toNormal) (MGround det)
      in do r @?= MGround (marginalize densIntFin normalG)
            assertBool "must not be PNormal" (projectMod r /= PNormal)
  , testCase "the transfer is looked up by the argument's capability" $
      mapM_ (\g -> applyMod (MArr det (mkTransfer MGround)) (MGround g) @?= MGround g) reprInputs
  , testCase "the tabulated transfer cannot carry an argument's family" $
      -- The documented loss of the finite-map form (design §3-A): the closure
      -- 'IArr' of ModalityInfer is what keeps the family through application.
      applyMod (MArr det (mkTransfer MGround)) (MGround normalG)
        @?= MGround normalG { gFam = FamNone }
  , testCase "a random choice of a function-valued result marginalizes only its outer" $
      let psi = mkTransfer (const (MGround normalG))
          r = applyMod (MArr densIntFin (mkTransfer (const (MArr det psi)))) (MGround det)
      in case r of
           MArr rho psi' -> do rho @?= marginalize densIntFin det
                               psi' @?= psi
           other -> assertFailure ("expected a function modality, got " ++ prettyMod other)
  , testCase "applyMod fails loudly on a non-function modality" $ do
      r <- try (evaluate (applyMod (MGround det) (MGround det)))
             :: IO (Either ErrorCall Mod)
      case r of
        Left _  -> return ()
        Right _ -> assertFailure "expected applyMod to reject a non-function head"
  , testCase "joining two functions joins outers and transfers pointwise" $
      let p1 = mkTransfer (const (MGround normalG))
          p2 = mkTransfer MGround
      in case joinModality (MArr det p1) (MArr densIntFin p2) of
           MArr rho p -> do
             rho @?= joinGround det densIntFin
             mapM_ (\g -> runTransfer p (MGround g)
                            @?= joinModality (runTransfer p1 (MGround g)) (runTransfer p2 (MGround g)))
                   reprInputs
           other -> assertFailure ("expected a function modality, got " ++ prettyMod other)
  , testCase "toMod tabulates an IArr closure so applyMod agrees with it on ground inputs" $
      let body (IG g) = IG (joinGround g normalG)
          body _      = IG bottomGround
          f = toMod (IArr det body)
      in mapM_ (\g -> applyMod f (MGround g) @?= toMod (body (IG g))) reprInputs
  ]
  where
    toNormal = mkTransfer (const (MGround normalG))

-- The four motivating programs (modality-port-lattice-core §"Motivating
-- programs"). Expected modalities are hand-authored; this milestone asserts the
-- data/projection only. Full end-to-end inference is milestones 4 and 6.

motivatingProgramTests :: TestTree
motivatingProgramTests = testGroup "motivating programs (hand-authored modalities)"
  [ -- (1) MProd tuple round-trip: pair = (Normal+1.0, 2.0*Normal), both Normal;
    -- fst pair + snd pair wants N(1, sqrt 5) = PNormal.
    testCase "MProd tuple round-trip pair projects PNormal componentwise" $
      let pair = MProd (MGround normalG) (MGround normalG)
      in projectMod pair @?= PNormal
  , testCase "MProd tuple round-trip result projects PNormal" $
      projectMod (MGround normalG) @?= PNormal

    -- (2) MArr/phi application: g(f(Normal)) wants N(2,2) = PNormal. The
    -- composite's transfer is hand-authored; what is asserted is that
    -- 'applyMod' through a Dirac function choice delivers it unchanged.
  , testCase "MArr application result projects PNormal" $
      projectMod (applyMod (MArr det (mkTransfer (const (MGround normalG)))) (MGround normalG))
        @?= PNormal

    -- (3) MRec recursive affine accumulation: addNoise 3 wants N(0, sqrt 3) = PNormal.
  , testCase "MRec recursive accumulation result projects PNormal" $
      projectMod (MGround normalG) @?= PNormal

    -- (4) MSum non-goal: a marginalized random-tag mixture of two Gaussians is
    -- genuinely not Gaussian, so the family must be dropped and it projects
    -- Integrate, NOT PNormal.
  , testCase "MSum random-tag mixture projects Integrate, not PNormal (non-goal pinned)" $
      let mixture = MGround (GroundMod DensInt Infinite FamNone)
      in do projectMod mixture @?= Integrate
            assertBool "must not be PNormal" (projectMod mixture /= PNormal)
  ]
