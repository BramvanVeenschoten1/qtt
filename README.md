# qtt
implementation of quantitative type theory with an impredicative sort and non-indexed inductive types

The core language features:
- dependent products with multiplicity annotations based on quantitative type theory
- nested, non-indexed, mutual inductive types, with multiplicity annotations on the arguments
- nested, mutual recursive functions
- simple dependent case distinction expressions, with multiplicity annotations on the discriminee

The high-level language features:
- a simple module system
- type-driven disambiguation of names from different modules
- a bidirectional type checking algorithm
- match expressions with default cases

This is a finished product now, meaning it will get no new features.
Examples can be found in test, along with an xml file for syntax highlighting in notepad++ deep black style.
