p(Left (0.5, 1.2))=(1.0, 2.0)
p(Left (0.5, ANY))=(1.0, 1.0)
p(Left ANY)=(1.0, 0.0)
p(Left (0.5, 0.2)) is impossible
-- Design witnessed-per-query-capability, program S (Either payload). An ANY
-- under the `left` tag masks both payload slots: the tag is observed (mass
-- one, dim 0) and the latents integrate out. This crashed at
-- `Fst is not a tuple: VAny` until task fc-inverse-refuses-on-any-input.
-- Left (ANY, 1.2) is the convolution x + u and is refused by the dispatcher.
