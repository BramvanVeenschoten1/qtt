# qtt
implementation of quantitative type theory with an impredicative sort and non-indexed inductive types

A work in progress, this repository contains mostly reused source files from the authors earlier projects, interjected with notes.

The core language features:
- dependent products with multiplicity annotations based on quantitative type theory
- non-nested, non-indexed, mutual inductive types, with multiplicity annotations on the arguments
- non-nested, mutual recursive functions
- simple dependent case distinction expressions, with multiplicity annotations on the discriminee

The elaborator features
- type-driven disambiguation of names from different modules
- no modules
- a bidirectional type checking algorithm

Notes on future features can be found in lamcvii/Main.hs

