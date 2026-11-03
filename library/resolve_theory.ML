(*  Title:  library/resolve_theory.ML
    Author: Qiyuan Xu (with AI assistance)

Theory.resolve_theory: a theory named in a context, the context's own theory
included even while it is unfinished.

Below this file Isabelle's Theory is reopened with this one addition (as
library/accounted_timeout.ML reopens Timeout).  Pure binds Theory only in the
global name space, so at a merge of parents this theory-level binding meets no
other (ml_env.ML:78-86).

Theory.check finds the context's theory and its ancestors but refuses the
context's own theory while it is unfinished (Context.get_theory,
context.ML:353-359) -- the theory being edited, or one of a theories section
still being built.  resolve_theory is Theory.check with that one case let
through, built on the same hook Theory.check uses (Theory.check_theory), so the
error with completion and the markup report at the position are Theory.check's,
for the own theory too.
*)

structure Theory:
sig
  include THEORY
  (*Theory.check, except that the context's own theory is found even while
    unfinished; a long name iff the name contains "."*)
  val resolve_theory: Proof.context -> string * Position.T -> theory
end =
struct

open Theory

fun resolve_theory ctxt (name, pos) =
  let
    val thy = Proof_Context.theory_of ctxt
    val long = {long = String.isSubstring "." name}
    val self = Context.theory_name long thy
    fun get a = if a = self then thy else Context.get_theory long thy a
    fun all () = map (Context.theory_name long) (thy :: Theory.ancestors_of thy)
  in Theory.check_theory {get = get, all = all} ctxt (name, pos) end

end
