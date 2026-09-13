-- Cons is a field constructor too: the transport through head dropped the
-- tail, so [0.7, 0.0] and even [0.7] answered 1.0.
p([0.7, 1.0])=(1.0, 1.0)
p([0.3, 0.0])=(1.0, 1.0)
p([0.7, 0.0]) is impossible
p([0.3, 1.0]) is impossible
p([0.7]) is impossible
