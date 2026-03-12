---
name: performant-isabelle-ml
description: Use performant Isabelle/ML data structures
---

# Performant Isabelle/ML

`Performant_Isabelle_ML` provides the following high-performance Isabelle/ML data structures.

- **Hash table** (`Inthashtab`, `Strhashtab`) instead of `Inttab`/`Symtab` for mutable, performant lookups: `library/hash_table.ML`
  - Warning: these are mutable. Do not use them when a stateless functional structure is needed — use `Inttab`/`Symtab` in that case.
- **Improved discrimination net** (`iNet`) instead of `Net` for term indexing with lambda abstraction support: `library/improved_net.ML`
