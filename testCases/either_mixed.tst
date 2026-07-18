backends: interpreter
-- Mixed Either (discrete Left arm, continuous Right arm). encode is refused for a
-- continuous arm inside an Either/ADT (the arm-conditional Gaussian params are not yet
-- generated), so there is no honest encode_len to assert here. Kept as a compile smoke
-- test; see makeEncodeEitherArm / requiredNormalFns in AutoNeural.hs.
