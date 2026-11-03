-- Sibling of consLevelsIntLessThan (task enumerated-int-pair-comparison-no-probability):
-- the plan engine's two-enumerated-leaf coupling with the deeper leaf on the
-- left of a `>`, and a leaf compared with itself, which is never True.
-- Logits as in consLevelsIntLessThan. P(main=1) = 0.06048 as there; the self
-- comparison is only reached when the first is False, so P(main=2) = 0 and
-- P(main=0) = 0.34272.
no-normalization
p(1, (2, [0.2, 0.8, 0.1, 0.9, 0.5, 0.3, 0.2, 0.6, 0.4, 0.1, 0.2, 0.3, 0.4, 0.3, 0.7, 0.2, 0.8, 0.3, 0.3, 0.4, 0.5, 0.5, 0.4, 0.3, 0.2, 0.1, 0.5, 0.5, 0.5, 0.5, 0.3, 0.3, 0.4, 0.5, 0.5, 0.25, 0.25, 0.25, 0.25]))=(0.06048, 0.0)
p(2, (2, [0.2, 0.8, 0.1, 0.9, 0.5, 0.3, 0.2, 0.6, 0.4, 0.1, 0.2, 0.3, 0.4, 0.3, 0.7, 0.2, 0.8, 0.3, 0.3, 0.4, 0.5, 0.5, 0.4, 0.3, 0.2, 0.1, 0.5, 0.5, 0.5, 0.5, 0.3, 0.3, 0.4, 0.5, 0.5, 0.25, 0.25, 0.25, 0.25]))=(0.0, 0.0)
p(0, (2, [0.2, 0.8, 0.1, 0.9, 0.5, 0.3, 0.2, 0.6, 0.4, 0.1, 0.2, 0.3, 0.4, 0.3, 0.7, 0.2, 0.8, 0.3, 0.3, 0.4, 0.5, 0.5, 0.4, 0.3, 0.2, 0.1, 0.5, 0.5, 0.5, 0.5, 0.3, 0.3, 0.4, 0.5, 0.5, 0.25, 0.25, 0.25, 0.25]))=(0.34272, 0.0)
