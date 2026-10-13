-- either-maybe/observeChainedDiscrete with main's observe binder renamed
-- from u to m, observeIsOne's parameter name. The query then dies at run
-- time: "Type error: Equals can only evaluate on two values: (VInt 1, VEither
-- (Right (VInt 1)))", i.e. `w == 1` reads the Maybe where it should read its
-- payload. Under any other name (`\v -> v > 0`) it answers 0.3. Verified at
-- 3b72682 on dev, interpreter. Found by the rewrite-invariance net's
-- alpha-rename family. Docs task callee-body-name-sensitive-across-call.
backends: interpreter
expect-failure: broken
p(Right 1)=(0.3, 0.0)
p(Left ())=(0.7, 0.0)
