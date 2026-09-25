p((2.5, 1.7), ThetaTree [0.45, 0.2] [])=(2.5617104199392124, 2.0, False)
p((2.7, 1.4), ThetaTree [0.45, 0.2] [])=(0.781277536509029, 2.0, False)
p((2.5, ANY), ThetaTree [0.45, 0.2] [])=(1.9333405840142468, 1.0, False)
-- Task affine-gaussian-closure-lost-across-let-bindings. Partial observation
-- of the chain: s1 is witnessed, s2 is not and is integrated out inside s3's
-- density. Closed form N(s1; 2.55, sigma) * N(s3; s1 - 0.9, sigma*sqrt 2) at
-- a = 0.45, sigma = 0.2. The ANY row is s1's marginal, N(2.55, sigma).
-- Not pinned: (ANY, s3), whose answer N(1.65, sigma*sqrt 3) exists but needs
-- s1 integrated out although it is witnessed by the tuple's first slot; the
-- point-witness engine refuses that at run time ("binding 's1' is
-- unobserved"). That is a per-query variant (design
-- witnessed-per-query-capability), not an affine-form question.
