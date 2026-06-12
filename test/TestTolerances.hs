-- | Single home for the numeric tolerances shared across the test suite.
-- probTolerance is also spliced into generated Julia and Python assertion
-- code, so the interpreter and backend end2end checks provably agree.
module TestTolerances (
  probTolerance,
  reasonablyCloseTolerance,
  samplingTolerance,
  encodeSlotTolerance,
  normalizationTolerance
) where

-- | Absolute tolerance for probability comparisons in end2end checks
-- (interpreter, generated Julia, generated Python).
probTolerance :: Double
probTolerance = 0.0001

-- | Absolute tolerance for exact-inference comparisons in Spec properties.
reasonablyCloseTolerance :: Double
reasonablyCloseTolerance = 1e-5

-- | Allowed deviation between a sampled PDF estimate and the exact PDF.
samplingTolerance :: Double
samplingTolerance = 0.1

-- | Allowed deviation for a single AutoNeural encode slot value.
encodeSlotTolerance :: Double
encodeSlotTolerance = 0.15

-- | Allowed deviation from 1 of the summed probability of a discrete support.
normalizationTolerance :: Double
normalizationTolerance = 0.01
