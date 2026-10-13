backends: interpreter, julia, python
p(Any)=(0.3, 0.0, False)
p(Possible)=(0.35, 0.0, False)
p(Nil)=(0.35, 0.0, False)
p(ANY)=(1.0, 0.0, False)
-- Constructors whose derived tests, isAny and isPossible, are runtime names
-- (the wildcard test and the possibility test). Unescaped, the emitted isAny
-- refused a hole by calling isAny, i.e. itself: Python raised RecursionError
-- and Julia overflowed its stack. Both backends now escape a constructor whose
-- derived test is reserved (Any_, isAny_). Oracle: 0.3, then 0.7 * 0.5 each.
-- Task adt-constructor-name-shadows-runtime.
