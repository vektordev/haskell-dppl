-- Task single-ctor-test-false-witness-crashes: a constructor test of a
-- one-constructor ADT. Face is the only constructor, so `isFace heard` is
-- True for every heard and p(False) is impossible. Observed False, the test's
-- inverse witnesses heard as "anything but Face ANY ANY", an empty set; it
-- crashed with "Parameter is not an ADT: VAnyExcept [...]" at 0959022, and
-- after that was fixed answered a plain zero rather than impossible.
-- IRCompiler.Monad.exceptMeasure measures that complement as impossible.
p(False) is impossible
p(True)=(1.0, 0.0)
cdf(False) is impossible
cdf(True)=(1.0, 0.0)
