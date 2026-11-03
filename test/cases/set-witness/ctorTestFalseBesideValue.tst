-- Task point-inversion-vanyexcept-witness-crashes: the constructor test of a
-- field observed False beside the bound value itself.
p((False, [Obj Green]))=(0.7, 0.0)
p((True, [Obj Red]))=(0.3, 0.0)
p((False, [Obj Red])) is impossible
p((True, [Obj Green])) is impossible
p((False, ANY))=(0.7, 0.0)
p((True, ANY))=(0.3, 0.0)
