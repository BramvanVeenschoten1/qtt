# qtt
implementation of quantitative type theory with an impredicative sort and non-indexed inductive types

A work in progress, this repository contains mostly reused source files from the authors earlier projects, interjected with notes.

The core language is now defined and features:
- dependent products with multiplicity annotations based on quantitative type theory
- non-mutual, non-indexed inductive types that allow nested recursion, with multiplicity annotations on the arguments
- non-mutual recursive functions that allow nested recursion
- simple dependent case distinction expressions

A prototype elaborator for a higher level language is intended to expand:
- mutual recursive inductive types
- mutual recursive function definitions at both top level and expression level
- type driven disambiguation of imported names

Note that this elaborator makes no use of unification whatsoever.

Future extensions may include:
- implicit function arguments (inferred by unification)
- universes
- indexed inductive types
- idris-style do-notation

code generation and libraries are well beyond the authors short term goals.

