-- A shared scene: a list of draw-bound neural reads, then a fold over it.
-- main is generate only and -v's engine applicability is empty, so no
-- reason is recorded; readAll and ex each compile all three variants. The
-- same shape over Bernoullis with a literal length (readAll 2) is refused
-- with a reason (set-valued witness construction failed). Found by the
-- publication-exploration C1 pilot (W4). Verified at b16b4d9 on dev. Docs
-- task bottom-verdict-records-no-refusal-reason.
expect-failure: no-code
