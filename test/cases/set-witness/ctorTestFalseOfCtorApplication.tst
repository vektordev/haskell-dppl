-- Task multi-ctor-test-of-ctor-application-false-crashes: a constructor test
-- of a constructor application of a multi-constructor ADT. Observed False,
-- its witness "anything but Stop" has to be inverted through Link; the False
-- query crashed with "Parameter is not an ADT: VAnyExcept [IRVar "Stop"]"
-- (AlgebraicDataTypes.isImpl) at b9c2c96. Link x is never Stop.
p(False)=(1.0, 0.0)
p(True) is impossible
cdf(False)=(1.0, 0.0)
cdf(True)=(1.0, 0.0)
