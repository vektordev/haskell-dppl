no-normalization
p((0, True), (2, [0.25, 0.75]), [(2, [0.9, 0.1]), (2, [0.2, 0.8])])=(0.225, 0.0)
p((1, True), (2, [0.25, 0.75]), [(2, [0.9, 0.1]), (2, [0.2, 0.8])])=(0.15, 0.0)
p((0, False), (2, [0.25, 0.75]), [(2, [0.9, 0.1]), (2, [0.2, 0.8])])=(0.025, 0.0)
p((1, False), (2, [0.25, 0.75]), [(2, [0.9, 0.1]), (2, [0.2, 0.8])])=(0.6, 0.0)
p((0, ANY), (2, [0.25, 0.75]), [(2, [0.9, 0.1]), (2, [0.2, 0.8])])=(0.25, 0.0)
p((ANY, ANY), (2, [0.25, 0.75]), [(2, [0.9, 0.1]), (2, [0.2, 0.8])])=(1.0, 0.0)
-- P(s, t) = pick(s) * see(board[s])(t), the mock inputs in MockNN's literal
-- (2, [...]) form. Found by experiments_nest exact-eig-question-asking.
-- The four concrete rows sum to one. Kept out of End2End's Normalization sweep
-- (no-normalization), which draws one scalar Symbol envelope per parameter
-- and cannot draw the list-of-Symbols board.
