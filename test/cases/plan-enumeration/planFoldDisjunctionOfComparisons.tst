p(1, (2, [0.1818,0.8182,0.1356,0.1525,0.0678,0.0508,0.1525,0.1356,0.0508,0.0339,0.1356,0.0849,0.1429,0.8571,0.2143,0.0238,0.1667,0.1905,0.0714,0.0238,0.2143,0.0476,0.0238,0.0238,0.125,0.875,0.0185,0.1481,0.1111,0.1481,0.0741,0.1667,0.0741,0.0926,0.1481,0.0186,0.3333,0.6667,0.1333,0.0833,0.1167,0.15,0.0333,0.0833,0.1,0.0667,0.15,0.0834]))=(0.2098190445, 0.0)
p(0, (2, [0.1818,0.8182,0.1356,0.1525,0.0678,0.0508,0.1525,0.1356,0.0508,0.0339,0.1356,0.0849,0.1429,0.8571,0.2143,0.0238,0.1667,0.1905,0.0714,0.0238,0.2143,0.0476,0.0238,0.0238,0.125,0.875,0.0185,0.1481,0.1111,0.1481,0.0741,0.1667,0.0741,0.0926,0.1481,0.0186,0.3333,0.6667,0.1333,0.0833,0.1167,0.15,0.0333,0.0833,0.1,0.0667,0.15,0.0834]))=(0.7901809555, 0.0)
-- Task plan-fold-disjunction-of-comparisons-blowup: the barcode checksum
-- predicate spelled inline, the fold written out once per comparison. Both
-- copies are one value; the plan path enumerates it once and evaluates the
-- disjunction per value ('planShareSplit'), where it used to enumerate each
-- copy, clash on the baked digit leaves, and rerun ungrouped (killed at 2 GB).
-- Same program as planHelperOnFoldResultBool with the helper inlined, so the
-- expected values are that case's (independent exact oracle over every list).
