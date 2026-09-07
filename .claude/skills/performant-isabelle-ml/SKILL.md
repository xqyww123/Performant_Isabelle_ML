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
- **Accounted timeout** — below this theory, `Timeout.apply`/`Timeout.apply_physical` are rebound (`structure Timeout` is shadowed) to a version that claims the `Exn.Interrupt_Breakdown` its own timer caused as `Timeout.TIMEOUT`; `Accounted_Timeout.raw_apply`/`raw_apply_physical` are the originals. Also home of `Interrupt_Family`, the interrupt test that looks one level into a `Par_Exn` container: `library/accounted_timeout.ML`
- **Thread CPU clock** (`Thread_CPU`): one thread's own CPU time; `Thread_CPU.timing`/`cpu_timing`, a measurement in it (beside `Timing.timing`'s process figures); and `Thread_CPU.apply {thread_cpu, wall}`, a timeout charged in it with an optional wall-clock limit for liveness. Without a clock (no native library, or the OS refusing one) the thread CPU reads as NONE and `apply` enforces only its wall-clock limit, with a warning, or errors when given none: `library/thread_cpu.ML`
- **Poly/ML FFI** (`Foreign`): Poly/ML's FFI structure, hidden by Pure, is bound again for this theory and every session built on it: `library/rescue_foreign.ML`
