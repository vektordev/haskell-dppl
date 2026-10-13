-- An `==` observed False under an inverse step (sq), in an if arm (docs ticket
-- eq-false-witness-through-sq-in-if-arm-reaches-codegen). Python/Julia codegen
-- failed with "cannot render a VAnyExcept placeholder" and the interpreter
-- crashed, until the set-witness point transport declined a VAnyExcept witness
-- it cannot turn into an exclusion set (task
-- binding-resolver-one-application-rule). p(False) is left out: it is the
-- density through sq, which known-issues/sqInverseDropsNonpositivePreimages
-- pins as halved.
batched
p(True)=(1.0, 0.0, False)
