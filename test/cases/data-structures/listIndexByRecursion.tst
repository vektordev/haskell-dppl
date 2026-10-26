p(True)=(0.7, 0.0)
p(False)=(0.3, 0.0)
-- The list index every board-of-symbols program uses. The batched module used
-- to emit nth's evaluator as a torch.where over both arms, so the recursion ran
-- past the end of the list and its head raised "InferenceList index out of
-- range" at every point. The branch is now split per element, each half
-- running only the arm it takes (task batched-conditional-evaluates-a-partial-arm).
