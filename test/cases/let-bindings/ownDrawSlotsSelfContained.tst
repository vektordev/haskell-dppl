p([True, False, True])=(0.05879999999999999, 0.0)
p([False, True, False])=(0.22619999999999998, 0.0)
p([ANY, True, True])=(0.063, 0.0)
p([True, ANY, False])=(0.036, 0.0)
p([False, ANY, ANY])=(0.8799999999999998, 0.0)
p([ANY, ANY, True])=(0.21, 0.0)
p([ANY, ANY, ANY])=(1.0, 0.0)
-- Brute force over a, b, c, d, e; an ANY answer contributes no constraint.
