p(1.5, ThetaTree [0.45, 0.2] [])=(1.0485866762994442, 1.0, False)
p(1.65, ThetaTree [0.45, 0.2] [])=(1.1516471649044517, 1.0, False)
p(2.1, ThetaTree [0.45, 0.2] [])=(0.49531727353372634, 1.0, False)
cdf(1.5, ThetaTree [0.45, 0.2] [])=(0.33250277105101467, 0.0)
cdf(1.65, ThetaTree [0.45, 0.2] [])=(0.5, 0.0)
cdf(2.1, ThetaTree [0.45, 0.2] [])=(0.9030345738587947, 0.0)
-- Task affine-gaussian-closure-lost-across-let-bindings. An ungated
-- linear-Gaussian chain observed at its endpoint only: s1 and s2 are never
-- witnessed, and are integrated out analytically as affine Gaussian forms.
-- Closed form N(3 - 3a, sigma*sqrt 3) at a = 0.45, sigma = 0.2, i.e.
-- N(1.65, 0.34641); the same distribution the flat-sum spelling
-- 3.0 - 3a + N*sigma + N*sigma + N*sigma already answered.
