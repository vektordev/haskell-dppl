-- Three define-bound sums of two neural reads each, compared in a chain, by
-- the readers' domain size D. Each define is inlined into one joint
-- enumeration of all six reads, so answering one query costs D^6, where
-- binding the sums like draws (each sum's law enumerated once, then the three
-- sums) costs about D^3. Interpreter allocation per query at 20bc478:
--   define: 2.7 / 13.8 / 151 / 866 MB at D = 3 / 4 / 6 / 8 (slopes 5.6, 5.9, 6.1)
--   draw:   0.5 / 1.2 / 4.7 / 12.8 MB                    (slopes 3.1, 3.3, 3.5)
-- The emitted Python grows alike (define 2 / 19 / 88 ms at D = 4 / 6 / 8).
-- The knob is the domain, not the tiles per sum: each sum's own law is a
-- joint enumeration of its tiles, exponential in their number for either
-- spelling. Docs task define-bound-sums-compared-enumerate-jointly.
expect-failure: growth above polynomial 4
knob: D = 3, 4, 6, 8
metric: eval-alloc
query: p(True{{for t in 1..6}}, (2, [{{for i in 1..D sep ", "}}1.0{{end}}]){{end}})
