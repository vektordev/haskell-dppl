-- The rewrite-invariance net's draw introduction on probe row 9 of design
-- law-carrying-modality (`draw x = Uniform in (x, x * 2.0 + Normal)`): the
-- fresh Normal bound in the second field, after x is recovered from the
-- first. The modality engine certifies n's binding affine, but the compiler
-- read the binding's body with x still typed random, so the collapse declined
-- and the set-witness engine refused. Binding bodies are now re-inferred under
-- the recovered variables (task dispatch-on-law-certificates). Rows: x at the
-- first slot (density 1), the second slot Normal(2x, 1).
slow
batched
p((0.3, 1.0))=(0.36827014030332333, 2.0)
p((0.7, -0.2))=(0.11092083467945558, 2.0)
