-- adtMixedArityCtors with its fields named `a`/`b` -- the spelling the derived
-- per-field FDecls used for their own sample variables, so renaming the sample
-- also rewrote the accessor reference and the program applied the sample to
-- itself (task adt-field-name-collides-with-fdecl-var). Same values as the
-- p/q twin.
p(Dot 0.5)=(0.3, 1.0, False)
p(Pair 0.5 0.25)=(0.7, 2.0, False)
p(Dot 0.9)=(0.3, 1.0, False)
p(Pair 0.1 0.9)=(0.7, 2.0, False)
p(Dot ANY)=(0.3, 0.0, False)
p(Pair ANY 0.25)=(0.7, 1.0, False)
p(Pair ANY ANY)=(0.7, 0.0, False)
