-- Three neural reads enumerated as nested loops, under nested ifs. The decodes
-- of y and z sit inside the loops of the draws before them, so the batched
-- backend used to evaluate each once per enumerated world; the batched-only
-- leaf-table pass (SPLL.IRLeafTablePass) now tabulates them once ahead of the
-- outer loop (task batched-enumeration-rereads-neural-leaf-per-world). The
-- domain starts at 1, so the table index is the loop value minus an offset.
-- Only (1, 2, 3) is ascending: 0.5 * 0.5 * 0.6 = 0.15.
p(True, (2, [0.5, 0.3, 0.2]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.3, 0.6]))=(0.15, 0.0)
p(False, (2, [0.5, 0.3, 0.2]), (2, [0.2, 0.5, 0.3]), (2, [0.1, 0.3, 0.6]))=(0.85, 0.0)
p(True, (2, [1.0, 0.0, 0.0]), (2, [0.0, 1.0, 0.0]), (2, [0.0, 0.0, 1.0]))=(1.0, 0.0)
p(True, (2, [0.0, 1.0, 0.0]), (2, [0.0, 1.0, 0.0]), (2, [0.0, 0.0, 1.0]))=(0.0, 0.0)
