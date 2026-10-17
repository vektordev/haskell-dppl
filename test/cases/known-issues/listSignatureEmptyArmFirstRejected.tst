-- A [Float] signature over an if whose then-arm is [] and whose else-arm is
-- a nested if: "the signature of 'main' declares the type [Float], but its
-- definition has the type []". Swapping the arms compiles, so does a
-- non-nested else-arm (Normal : f), and so does the program without the
-- signature. Blocks Enumerated signatures on recursive list programs. Found
-- by the publication-exploration queries explorer. Verified at b16b4d9 on
-- dev. Docs task list-signature-rejected-when-empty-arm-first.
-- Idealized: p([1.0]) = 0.25.
expect-failure: broken
p([1.0])=(0.25, 0.0)
