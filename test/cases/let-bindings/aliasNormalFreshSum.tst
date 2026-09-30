p((0.3, 0.5))=(0.14913891880709737, 2.0, False)
p((-1.0, 0.0))=(5.854983152431917e-2, 2.0, False)
p((0.3, ANY))=(0.38138781546052414, 1.0, False)
-- Row 8 of design law-carrying-modality's evidence table, the rewritten half
-- of `main = draw x = Normal in (x, x + Normal)`: phi(a) * phi(b - a).
-- Crashed with "cannot extract Normal params" (the alias y kept x's
-- standalone PNormal after x was recovered) until task
-- reinfer-body-under-recovered-bindings.
