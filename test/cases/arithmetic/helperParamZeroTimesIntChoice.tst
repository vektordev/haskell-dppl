-- An Int parameter zero times an enumerable factor: the point mass at 0 (task
-- helper-parameter-zero-factor-answers-nan). Not `batched`: the batched
-- backend has no OpIntDiv, so the multI inverse crashes its codegen even for
-- a literal factor (task batched-int-mult-inverse-no-intdiv).
p(0)=(1.0, 0.0)
p(1) is impossible
cdf(0)=(1.0, 0.0)
cdf(-1)=(0.0, 0.0)
