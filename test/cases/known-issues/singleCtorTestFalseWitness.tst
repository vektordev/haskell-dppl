expect-failure: broken
backends: interpreter, python
p(False) is impossible
-- Docs task single-ctor-test-false-witness-crashes. Face has one constructor,
-- so `isFace heard` is True for every heard and p(False) is impossible. The
-- constructor-test inverse's False outcome witnesses heard as the VAnyExcept
-- placeholder "anything but Face ANY ANY", and that placeholder reaches
-- `isFace` as a value: the interpreter dies with "Parameter is not an ADT:
-- VAnyExcept [...]" (verified on dev at compiler 0959022). Found by the
-- per-mask marginalisation-consistency sweep (task per-mask-variants-by-pruning),
-- where tupleCtorTestOfSharedDraw's (isFace heard, heard) masked at its second
-- slot is exactly this program.
