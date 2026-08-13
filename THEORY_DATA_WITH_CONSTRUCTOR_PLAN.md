# Plan: `Theory_Data_With_Constructor`

A `Theory_Data` variant whose value is, at every `Theory.begin_theory`, computed
from the parents' values by a user-supplied `construct` function — instead of
being inherited by the shortcuts built into stock theory data.

Status: implemented (2026-08-13). Reviewed before implementation
(two-reviewer adversarial debate, 2 turns; all surviving findings were
documentation/contract/test-coverage fixes, applied below — no design
change). Code: `library/theory_data_with_constructor.ML`; tests:
`Test/Theory_Data_With_Constructor_Test.thy`, all 13 §5 items pass under
`ML_process -l Pure` via `Thy_Info.use_thy_legacy`, and a
deliberately-wrong negative control (asserting verbatim inheritance) was
run once and failed as required, then deleted.

## 1. Why stock `Theory_Data` is not enough

`Context.begin_thy` obtains the new theory's data via `merge_data parents`
(`Isabelle2025-2/src/Pure/context.ML:549`, `:447-456`), which has two shortcuts:

- **One parent: the whole data table is taken verbatim.** `merge_data [thy] =
  data_of thy` — no `merge` function of any data kind runs. This is the common
  case: most theories have exactly one import.
- **Two or more parents, but only one carries the kind: entry kept verbatim**
  (`Datatab.default`). `merge` runs only when at least two parents carry the
  kind.

There is no way to force `merge` to run: `declare_data` stores only a position,
`empty` and `merge` — no flag — and the shortcut logic is fixed in `merge_data`.

Consequently a data kind whose value must describe *the theory it sits in*
(rather than accumulate monotonically) silently carries a stale description
across theory boundaries. Pure itself patches around this a dozen times with
hand-written `Theory.at_begin` hooks (`more_thm.ML:728` resets forked proofs,
`Isar/code.ML:497` re-creates a per-theory dataref, `zterm.ML:717` re-creates
caches, `thm.ML:2716` re-closes classrel/arity tables, ...). Every one of those
hooks re-implements the same three-part pattern: a change detector so the
wrapper loop terminates, a rebuild step, a registration. This functor packages
that pattern once — for the sub-class of hooks whose rebuild depends only on
the parents and their values. Of the four precedents, `more_thm.ML`'s proof
reset and `code.ML`'s dataref rebuild are in that sub-class; `zterm.ML`'s is
not (its `Theory.at_end` half, which drops the caches from finished theories,
has no counterpart here), nor is `thm.ML`'s (its completion reads the theory
under construction, which §2.4 forbids). Those stay hand-written.

## 2. Interface

File: `library/theory_data_with_constructor.ML`, loaded from
`Performant_Isabelle_ML.thy` (which imports Pure; `Theory.at_begin` is Pure).

```sml
signature THEORY_DATA_WITH_CONSTRUCTOR_ARGS =
sig
  type T
  val empty : T                             (*value outside the functor's scope*)
  val construct : (theory * T) list -> T    (*parents with their values -> value*)
end

functor Theory_Data_With_Constructor(Data: THEORY_DATA_WITH_CONSTRUCTOR_ARGS):
  THEORY_DATA   (*the stock result signature: get / put / map*)
```

Semantic contract:

1. **At every `Theory.begin_theory` of a theory in scope (§4), `construct` is
   called exactly once**, with all parents and their values — also when there
   is only one parent. Its result becomes the new theory's value.
   "Parents" means `Theory.parents_of`: the import list after `make_parents`
   (`context.ML:531-533`) deduplicates it and drops any import that is an
   ancestor of another — `theory D imports A B` where B imports A hands
   `construct` the pair for B only. The pairs come in `Theory.parents_of`
   order. A parent out of scope contributes the pair `(parent, empty)`; in
   particular the declaring theory's own construction (§3.3) receives *only*
   such pairs, since its imports predate the declaration — `construct` must
   not assume its input values were themselves produced by `construct`.
2. `put`/`map` behave as in stock `Theory_Data`: they modify the current
   theory's value in place. Mid-theory modifications are visible to the
   children's `construct` (as the parent's value), not re-derived away.
3. Theories out of scope read `empty`. `empty` is a separate field, NOT
   `construct []`: `construct` is never invoked with `[]` (`begin_thy`
   rejects empty imports, `context.ML:536-537`, and `make_parents` cannot
   empty a non-empty list), so `construct []` would be a reserved encoding
   with no natural meaning — a user who gives `[]` a meaning has written dead
   code, and a `construct` that cannot handle `[]` would raise at functor
   application. The separate field makes the out-of-scope value an explicit
   choice. It is evaluated once and shared by every out-of-scope theory,
   mutable content included, so it must be safe to share.
4. `construct` sees the parents only. It cannot see the theory under
   construction — deliberately: at hook time that theory is a half-initialized
   draft, and another instance's data on it may not be constructed yet. A
   client that needs the new theory itself (its name, its ancestors) cannot
   use this functor and must write its own `at_begin` hook
   (e.g. `Universal_Key.claim_cache_scope` stays hand-written).

## 3. Implementation

```sml
functor Theory_Data_With_Constructor(Data: THEORY_DATA_WITH_CONSTRUCTOR_ARGS): THEORY_DATA =
struct

type T = Data.T

structure Store = Theory_Data'(
  type T = int list option * Data.T
  (*NONE = not constructed for this node; the int list is the stamp, §3.1*)
  val empty = (NONE, Data.empty)
  fun merge args = (NONE, #2 (#2 (hd args)))   (*force reconstruction, §3.2*)
)

val get = #2 o Store.get
fun put x = Store.map (fn (stamp, _) => (stamp, x))
fun map f = Store.map (fn (stamp, x) => (stamp, f x))

fun rebuild thy =
  let
    val parents = Theory.parents_of thy
    val stamp = SOME (List.map Context.theory_identifier parents)
  in
    if #1 (Store.get thy) = stamp then NONE
    else SOME (Store.put (stamp, Data.construct
                 (List.map (fn p => (p, get p)) parents)) thy)
  end

val _ = Theory.setup (Theory.at_begin rebuild #> perhaps rebuild)

end
```

### 3.1 The stamp, and why the wrapper loop terminates

`Theory.begin_theory` applies the begin wrappers as
`perhaps (perhaps_loop (perhaps_apply ...))` (`theory.ML:83-84`): the whole
wrapper list is re-run until every wrapper returns `NONE`. So `rebuild` must
answer "already constructed for this node?" — and `Context.theory_identifier`
of the theory itself cannot be that marker, because every `Theory_Data.put`
mints a fresh id (`change_thy` -> `create_thy` -> `new_id ()`,
`context.ML:484,466`): a hook that stamps with the theory's own id never sees
its own stamp again and loops forever.

The stamp is instead **the list of the parents' identifiers**. It works
because:

- The parent values captured in the child's ancestry at `begin_thy`
  (`context.ML:544`) are immutable ML values, so their ids never change and
  the stamp is stable. Finality is NOT needed and not guaranteed: `begin_thy`
  never checks it, and the tests in §5 pass `\<^theory>` — a draft — as
  parent. A later `put` on a draft parent builds a new theory value with a
  fresh id (`change_thy` -> `create_thy`), leaving the captured value
  untouched.
- `change_thy` keeps a draft's ancestry unchanged (`context.ML:487-491`), so
  `Theory.parents_of thy` gives the same list in every loop iteration. Second
  iteration: stamp matches, `rebuild` returns `NONE`. Terminates.
- A value inherited verbatim from a single parent carries the stamp of the
  *grandparents*. A theory is never its own parent, so the inherited stamp
  never matches and reconstruction always fires.
- Two same-name theories: the stamp compares parent ids, not names, so
  sibling theories with equal names (built by hand via `Theory.begin_theory`)
  are still told apart.

Cross-check with Pure's precedents: `code.ML:490` uses the theory's long name
as its stamp, which breaks on hand-built same-name theories; the parents' ids
do not.

### 3.2 The host `merge` forces reconstruction

The host `Store.merge` returns `(NONE, payload of the first parent that
carries the kind)` — `merge_data` filters non-carriers out before calling
`merge` (`context.ML:452`) — instead of attempting a real merge. Rationale:
whenever `merge` runs during `begin_theory`, the `at_begin` hook runs
immediately after and overwrites the result — a real merge would be dead
code. Keeping it degenerate means the value has exactly one producer
(`construct`), which is the invariant the whole functor exists to provide.
The payload is kept (not `Data.empty`) only so that the rare
non-`begin_theory` path (§4, `join_thys`) keeps at least the first carrier's
value rather than nothing.

### 3.3 `#> perhaps rebuild`: the declaring theory itself

`Theory.at_begin` registers a wrapper in the theory whose body runs the
functor application, and wrappers apply only to that theory's *descendants*
(`theory.ML:186-205`). Without the extra `perhaps rebuild`, the declaring
theory itself would keep `(NONE, Data.empty)` and the invariant "value =
construct(parents)" would start one generation late.

### 3.4 Ordering across instances

Wrappers run in registration order within each `perhaps_apply` pass
(`at_begin` conses; `begin_wrappers` reverses, `theory.ML:183`) — but only
along a linear import chain. When two instances are declared in incomparable
theories that meet in a diamond, the child's wrapper list comes from
`Thy.merge`'s `Library.merge (eq_snd op =)` (`theory.ML:108-113`), and the
resulting order is decided by the child's import order, not by ML load order.
Cross-instance execution order is therefore unspecified in general — one more
reason for contract §2.4: no instance may read another instance's data of the
theory under construction; the signature enforces this by not passing that
theory.

## 4. Scope and boundaries (to be stated in the source comment)

- **Scope** = descendants of any theory that ran the functor application,
  plus that theory itself (§3.3). Theories that do not import the declaring
  theory read `empty` — for a library shipped as
  `Performant_Isabelle_ML`, that means all of HOL/AFP built below it.
- **Heap-restored theories do not re-run construction.** Loading a heap image
  deserializes theory values; no `begin_theory` runs. Their values are
  whatever the *building* process constructed. A `T` holding process-local
  resources (mutable cells, `Synchronized.var`, sockets) is therefore still
  shared across processes and needs its own process-identity check; this
  functor gives per-*theory-begin* freshness, not per-*process* freshness.
- **`Context.join_thys` bypasses the hook** (it calls `merge_data` but not the
  wrappers). `join_thys` serves the fork/`put`/join pattern
  (`HOL/ex/Join_Theory.thy:35-39`, its sole in-distribution user): every fork
  carries the kind, so the degenerate `Store.merge` keeps the FIRST fork's
  payload and silently discards the other forks' `put`s — where a stock
  `Theory_Data` with a real `merge` would combine them. The joined node's
  stamp is `NONE`, so any child begun from it reconstructs. Accepted as out
  of scope; do not `put` instance data inside `join_thys` forks.
- **`put` on an out-of-scope theory is unsupported.** It creates a Store
  entry there, and that theory's descendants carry no wrapper, so they
  inherit the value verbatim forever — the exact leak class this functor
  exists to remove.
- **Apply the functor only in an `ML`/`ML_file` block at theory level.**
  Without a thread context, or in a proof/local-theory context,
  `Theory.setup` fails loudly at application time (`context.ML:687,712-715`).
  One silent trap: in a diagnostic command (`ML_val`, `ML_command`) the setup
  succeeds and is then discarded together with the command's result — no
  error, no registration.
- **`construct` must be cheap and total.** It runs inside every
  `begin_theory` of every downstream theory; an exception there aborts theory
  loading for every session built on this library. Measured baseline
  (2026-08-13, this machine, HOL-Library heap): a bare `begin_theory` from a
  Main-sized parent costs ~18 ms; ten instances' hooks together added ~0.4 ms,
  within the ±2 ms noise. The baseline already includes double-pass wrapper
  behavior: an in-scope `rebuild` returns `SOME` on the first pass, so
  `perhaps_loop` always runs a second all-`NONE` pass — as stock Isabelle
  already does at every begin via `code.ML`'s `init_dataref`.
  Budget guidance: keep `construct` at or below
  ~1 ms; never O(size of accumulated table) unless the table is expected to
  stay small.

## 5. Tests

`Test/Theory_Data_With_Constructor_Test.thy`, imports
`"../Performant_Isabelle_ML"`, following `Hash_Table_Test.thy`'s
assert-in-ML style. All theories built by hand with `Theory.begin_theory` /
`Theory.end_theory` against `\<^theory>`; no extra session, no RPC.

1. **Single parent reconstructs**: instance with `construct = combine`;
   parent value v; child's value = `combine [(parent, v)]`, not v.
   (Negative control for the verbatim-inheritance shortcut.)
2. **Mid-theory `put` reaches the child**: parent `put`s v'; child sees
   `construct [(parent, v')]`.
3. **Two parents**: child of A and B sees both pairs, in `parents_of` order.
4. **Diamond**: D imports B and C (both importing A); `construct` at D
   receives B and C only (parents, not ancestors).
5. **Exactly one construction per begin**: count calls with a counter ref;
   one `begin_theory` increments it by exactly 1 (loop termination +
   no double construction).
6. **Declaring theory constructed**: in the declaring theory itself,
   `get \<^theory>` reflects `construct`, not `empty` (§3.3). The functor
   application and this assertion MUST sit in separate `ML` blocks (or the
   assertion must read `Context.the_global_context ()` at run time):
   `\<^theory>` is the static compile-time context of its block and does not
   see the same block's `Theory.setup`.
7. **Out-of-scope theory reads `empty`**: `get` on a pre-existing loaded
   theory (e.g. Pure) = `empty`.
8. **Same-base-name siblings are told apart**: two hand-built theories with
   the same name, different parents; each sees its own `construct` result
   (stamp is ids, not names).
9. **Mixed-scope parents take the one-carrier shortcut**: child of one
   in-scope parent and one out-of-scope parent; `construct` receives the
   in-scope pair plus `(out_of_scope_parent, empty)`. This is the only test
   reaching the `Datatab.default` path (`context.ML:454`) — the second §1
   shortcut; tests 3-4 take `invoke_merge`, tests 1/2/8 the single-parent
   path. The out-of-scope parent must be hand-built directly over Pure: a
   pre-existing ancestor of the in-scope parent would be dropped by
   `make_parents` as subsumed.
10. **Two instances, one begin**: both constructed, each exactly once
    (per-instance counters; pins §3.4's per-instance independence).
11. **`put` does not trigger reconstruction**: `put v'` in a theory, `get`
    still `v'` afterwards — the stamp survives `put`.
12. **Value survives `Theory.end_theory` unchanged** (the functor registers
    no end wrapper — contrast `zterm.ML`, which deliberately clears at end).
13. **`make_parents` reduction**: D imports A and B where B imports A;
    `construct` at D receives only the B pair (§2.1).

Deliberately untested: heap-restore staleness (§4) — not observable within
one process.

## 6. Non-goals

- Migrating `Universal_Key.claim_cache_scope` onto this functor (needs the
  theory under construction; contract §2.4 excludes it).
- Migrating any existing phi-system/contrib data kind. Candidates may come
  out of the pending Theory_Data audit; each migration is its own decision.
- A `Generic_Data` counterpart (proof contexts already have per-context
  `init` via `Proof_Data`).
