expect-failure: diagnostic "Comparison not implemented for type: TSymbol"
p((0, True), (0, [0.25, 0.75]), [(0, [0.9, 0.1]), (1, [0.2, 0.8])])=(0.225, 0.0)
p((1, True), (0, [0.25, 0.75]), [(0, [0.9, 0.1]), (1, [0.2, 0.8])])=(0.15, 0.0)
p((ANY, True), (0, [0.25, 0.75]), [(0, [0.9, 0.1]), (1, [0.2, 0.8])])=(0.375, 0.0)
-- Idealized: P(s, t) = pick(s) * see(board[s])(t). Found by experiments_nest
-- exact-eig-question-asking. Task symbol-selected-by-helper-crashes-cdf-compile.
