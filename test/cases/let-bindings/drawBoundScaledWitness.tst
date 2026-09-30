p((0.3, 1.0))=(0.36827014030332333, 2.0, False)
p((0.75, 1.0))=(0.3520653267642995, 2.0, False)
p((1.5, 1.0)) is impossible
p((0.3, ANY))=(1.0, 1.0, False)
-- Row 9 of design law-carrying-modality's evidence table, the rewritten half
-- of `main = draw x = Uniform in (x, x * 2.0 + Normal)`: phi(b - 2a) on
-- a in [0, 1]. Crashed with "found no way to convert to IR" until task
-- reinfer-body-under-recovered-bindings: y = x * 2.0 stayed Integrate after x
-- was recovered.
