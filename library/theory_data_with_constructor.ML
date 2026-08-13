(*
  Theory_Data_With_Constructor: a Theory_Data variant whose value is, at every
  Theory.begin_theory of a theory in scope, computed from the parents' values
  by `construct` -- instead of inherited through the shortcuts of stock theory
  data (single parent: whole table verbatim; several parents, one carrier:
  entry verbatim; see Pure/context.ML merge_data).

  Contract (details in THEORY_DATA_WITH_CONSTRUCTOR_PLAN.md):
  - `construct` is called exactly once per begin, with Theory.parents_of and
    their values, in that order; an out-of-scope parent contributes `empty`.
    It is never called with []; out-of-scope theories read `empty`.
    The declaring theory's own construction receives ONLY (parent, empty)
    pairs -- its imports predate the declaration -- so `construct` must not
    assume its inputs were themselves produced by `construct`.
  - Scope = the declaring theory (the theory whose ML block applies the
    functor) and its descendants.  Heap-restored theories
    do NOT re-run construction: values holding process-local resources still
    need their own process-identity check.
  - Context.join_thys bypasses the hook and keeps only the first fork's
    payload -- do not `put` instance data inside join_thys forks.
  - `put` on an out-of-scope theory is unsupported (descendants would inherit
    it verbatim, with no reconstruction).
  - Apply the functor only in an ML/ML_file block at theory level.  In
    ML_val/ML_command the registration is silently discarded with the
    command's result.
  - `construct` must be cheap (<= ~1 ms) and total: it runs inside every
    downstream begin_theory, and an exception there aborts theory loading.
*)

signature THEORY_DATA_WITH_CONSTRUCTOR_ARGS =
sig
  type T
  val empty : T   (*value outside the functor's scope; evaluated once and shared
                    by ALL out-of-scope theories, mutable content included --
                    must be safe to share*)
  val construct : (theory * T) list -> T    (*parents with their values -> value*)
end

functor Theory_Data_With_Constructor(Data: THEORY_DATA_WITH_CONSTRUCTOR_ARGS): THEORY_DATA =
struct

type T = Data.T

structure Store = Theory_Data'(
  type T = int list option * Data.T
  (*The int list is the stamp: the parents' theory identifiers the payload was
    constructed from.  NONE = not constructed for this node.*)
  val empty = (NONE, Data.empty)
  (*Degenerate on purpose: on the begin_theory path the at_begin hook runs
    right after merge_data and overwrites the result, so a real merge would be
    dead code; keeping construct the sole producer is the point.  hd args is
    the first parent that carries the kind (merge_data filters).*)
  fun merge args = (NONE, #2 (#2 (hd args)))
)

val get = #2 o Store.get
fun put x = Store.map (fn (stamp, _) => (stamp, x))
fun map f = Store.map (fn (stamp, x) => (stamp, f x))

(*Terminates under perhaps_loop: the parent values captured in the draft's
  ancestry are immutable, so the stamp is identical in every pass and the
  second pass returns NONE.  A verbatim-inherited entry carries the
  grandparents' stamp, which can never equal the parents' -- a theory is
  never its own parent -- so reconstruction always fires.  The theory's own
  identifier cannot serve as the stamp: every put mints a fresh id.*)
fun rebuild thy =
  let
    val parents = Theory.parents_of thy
    val stamp = SOME (List.map Context.theory_identifier parents)
  in
    if #1 (Store.get thy) = stamp then NONE
    else SOME (Store.put (stamp, Data.construct
                 (List.map (fn p => (p, get p)) parents)) thy)
  end

(*at_begin reaches only descendants; the extra `perhaps rebuild` constructs
  the declaring theory itself.*)
val _ = Theory.setup (Theory.at_begin rebuild #> perhaps rebuild)

end
