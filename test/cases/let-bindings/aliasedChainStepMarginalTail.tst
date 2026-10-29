-- A four-step Gaussian chain whose third step is re-bound through an alias,
-- queried for the marginal over its last step: phi(0) phi(0.5) phi(0.5) =
-- 0.04944889 at dim 3, as the unaliased chain answers. The mask variant's
-- equality guard on the deterministic application binding the aliased tail
-- read that tuple's last fields as a callee result's bc and flag
-- ('stripBranchCount') and answered 0.0 with the impossibility flag set.
-- Found by the rewrite-invariance sweep over let-bindings/gaussianTrajectory4.
-- Tasks aliased-chain-step-marginal-tail-impossible,
-- trajectory-tail-bound-as-tuple-type-error.
p((0.0, (0.5, (1.0, ANY))))=(0.04944889338563758, 3.0)
p((0.0, (0.5, (1.0, 1.0))))=(1.9727254290593573e-2, 4.0)
