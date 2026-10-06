expect-failure: no-code
p((0, True), (2, [0.25, 0.75]), [(2, [0.9, 0.1]), (2, [0.2, 0.8])])=(0.225, 0.0)
p((1, True), (2, [0.25, 0.75]), [(2, [0.9, 0.1]), (2, [0.2, 0.8])])=(0.15, 0.0)
p((ANY, True), (2, [0.25, 0.75]), [(2, [0.9, 0.1]), (2, [0.2, 0.8])])=(0.375, 0.0)
-- Idealized: P(s, t) = pick(s) * see(board[s])(t). Found by experiments_nest
-- exact-eig-question-asking. The mock inputs are MockNN's literal (2, [...])
-- form; the original pin's (0, [...]) is not a form MockNN accepts.
