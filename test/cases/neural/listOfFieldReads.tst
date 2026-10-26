no-normalization
p([True, False, True, True, False, False, True, True, False, True, False, True, False, True], (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6, 0.9, 0.1, 0.6, 0.4, 0.3, 0.7, 0.8, 0.2, 0.5, 0.5, 0.1, 0.9, 0.75, 0.25, 0.35, 0.65, 0.65, 0.35, 0.45, 0.55, 0.55, 0.45]))=(0.001947889944, 0.0)
p([False, False, False, False, False, False, False, False, False, False, False, False, False, False], (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6, 0.9, 0.1, 0.6, 0.4, 0.3, 0.7, 0.8, 0.2, 0.5, 0.5, 0.1, 0.9, 0.75, 0.25, 0.35, 0.65, 0.65, 0.35, 0.45, 0.55, 0.55, 0.45]))=(5.108102999999998e-06, 0.0)
p([ANY, True, ANY, False, ANY, True, ANY, False, ANY, True, ANY, False, ANY, True], (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6, 0.9, 0.1, 0.6, 0.4, 0.3, 0.7, 0.8, 0.2, 0.5, 0.5, 0.1, 0.9, 0.75, 0.25, 0.35, 0.65, 0.65, 0.35, 0.45, 0.55, 0.55, 0.45]))=(0.00043312499999999997, 0.0)
p([True, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY], (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6, 0.9, 0.1, 0.6, 0.4, 0.3, 0.7, 0.8, 0.2, 0.5, 0.5, 0.1, 0.9, 0.75, 0.25, 0.35, 0.65, 0.65, 0.35, 0.45, 0.55, 0.55, 0.45]))=(0.7, 0.0)
p([ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, False], (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6, 0.9, 0.1, 0.6, 0.4, 0.3, 0.7, 0.8, 0.2, 0.5, 0.5, 0.1, 0.9, 0.75, 0.25, 0.35, 0.65, 0.65, 0.35, 0.45, 0.55, 0.55, 0.45]))=(0.44999999999999996, 0.0)
p([ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY, ANY], (2, [0.7, 0.3, 0.2, 0.8, 0.4, 0.6, 0.9, 0.1, 0.6, 0.4, 0.3, 0.7, 0.8, 0.2, 0.5, 0.5, 0.1, 0.9, 0.75, 0.25, 0.35, 0.65, 0.65, 0.35, 0.45, 0.55, 0.55, 0.45]))=(1.0, 0.0)
-- Product of the per-field P(x_i = b) over the observed slots; ANY adds no
-- constraint. Task list-of-field-reads-compile-exponential.
