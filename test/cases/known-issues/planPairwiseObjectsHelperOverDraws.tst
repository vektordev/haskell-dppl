-- plan-enumeration/planPairwiseObjectsAcrossTwoReads with the relation moved
-- into a helper over the two draw-bound objects. Inline it answers
-- P(True) = 0.8 * 0.6 * Phi(1/sqrt(5)) = 0.322867 at that file's logits;
-- through `leftOf`, main has no probability function. Same cause as
-- planPairwiseInHelper (one read): ModalityInfer's plan exemption for a
-- comparison of two family-free continuous operands is keyed on a ReadNN in
-- the *declaration*, and `leftOf` contains none, so main types Bottom before
-- the plan engine (which would open both reads) is ever asked.
-- Residue of task plan-pairwise-across-separate-neural-reads.
expect-failure: no-code
