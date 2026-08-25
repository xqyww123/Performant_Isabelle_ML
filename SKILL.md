---
name: performant-isabelle-ml
description: Use performant Isabelle/ML data structures and concurrency utilities
---

# Performant Isabelle/ML

`Performant_Isabelle_ML` provides the following high-performance Isabelle/ML data structures and concurrency utilities.

- **Hash table** (`Inthashtab`, `Strhashtab`) instead of `Inttab`/`Symtab` for mutable, performant lookups: `library/hash_table.ML`
  - Warning: these are mutable. Do not use them when a stateless functional structure is needed — use `Inttab`/`Symtab` in that case.
- **Improved discrimination net** (`iNet`) instead of `Net` for term indexing with lambda abstraction support: `library/improved_net.ML`
- **Race engine** (`Race`) instead of `Par_List.get_some` for racing alternative computations — the winner is the lowest-indexed racer that recorded a claim, the first claim to arrive ends the race, losers are cancelled promptly, every racer gets a truthful exit, and all racers have terminated before the race returns: `library/race.ML`
  - Warning: racer bodies must be self-bounded (wrap each in its own `Timeout.apply`) — on the no-winner path the race joins every racer, so one unbounded racer blocks the whole call.
