-- A per-cell neural read on a structural walk down a list of Symbols, split
-- over two mutually recursive functions (wantA reads a 1, then wantB reads a
-- 2, alternating). Every call on the cycle passes `tail xs`, so the walk
-- decreases, but the fix for decreasing-recursion-refused-as-generate-fallback
-- (0de5663) admits only a *direct* self-call that changes an argument; this
-- shape is still refused by requireDeterministicUnderEnum and `compile`
-- silently emits generate-only code. It is how a recursive-descent parser
-- (one function per nonterminal) reads glyphs lazily; the workaround is to
-- fold the parser into one self-recursive shift-reduce walk. Found by
-- experiments_nest handwritten-arithmetic-roundtrip (docs task
-- exp-handwritten-arithmetic-roundtrip), verified at e003f66 on dev. Ticket
-- neural-read-mutual-recursion-refused.
-- Idealized: p(True) = glyph(x0)[1] * glyph(x1)[2] = 0.5 * 0.3 = 0.15.
expect-failure: refused "which is on a recursive call cycle"
no-normalization
p(True, [(2, [0.2, 0.5, 0.3]), (2, [0.1, 0.6, 0.3])])=(0.15, 0.0)
p(True, [])=(1.0, 0.0)
