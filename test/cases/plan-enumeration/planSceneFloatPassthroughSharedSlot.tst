-- Both outputs carry o1's px, so a query whose two px values differ is
-- impossible: the point-point case of 'intersectLeafCon' keeps the first point
-- under a guard that the second agrees with it. It answered 0.7 phi(0.5), the
-- first field's mass alone (task plan-point-point-intersection-ignores-mismatch,
-- was the known-issues pin planSharedSlotPointMismatchNotImpossible).
p(Scene Nil Nil, (2, [0.3, 0.7, 0.4, 0.6, 0.0, 1.0, 0.6, 0.4, 0.9, 0.1, 1.0, 2.0]))=(0.3, 0.0)
p(Scene (Obj Green 0.5) (Obj Green 0.5), (2, [0.3, 0.7, 0.4, 0.6, 0.0, 1.0, 0.6, 0.4, 0.9, 0.1, 1.0, 2.0]))=(0.24644572873500964, 1.0)
p(Scene (Obj Green 0.5) (Obj Green 0.7), (2, [0.3, 0.7, 0.4, 0.6, 0.0, 1.0, 0.6, 0.4, 0.9, 0.1, 1.0, 2.0])) is impossible
p(Scene (Obj Green 0.5) (Obj Green 1.0), (2, [0.3, 0.7, 0.4, 0.6, 0.0, 1.0, 0.6, 0.4, 0.9, 0.1, 1.0, 2.0])) is impossible
