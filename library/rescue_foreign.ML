(*  Title:  library/rescue_foreign.ML
    Author: Qiyuan Xu (with AI assistance)

Re-enter Poly/ML's Foreign structure into the global ML name space.

Pure hides Foreign: ML_Name_Space.hidden_structures (ml_name_space.ML:67) is
forgotten from the global name space by ML_Bootstrap.thy:23-25.  But that same
theory first copies every hidden structure into its own ML environment
(ML_Bootstrap.thy:11-15), which is theory data, so the VALUE survives in every
heap containing theory ML_Bootstrap -- Pure itself included -- and only the
name binding is gone.  This file reads the value back and binds the name again.
Design, evidence and limits: contrib/Semantic_Embedding/archive/plans/FOREIGN_RESCUE.md.

Only Foreign is rescued.  RunCall and Signal would come back by the same
recipe and are deliberately left hidden.

What this changes.  A name-space entry of the running ML process; nothing on
disk, no distribution file, no Pure heap.  The entry IS saved into any heap
built after this file, so every session above Performant_Isabelle_ML compiles
Foreign.* without repeating this (measured: a child session on such a heap sees
Foreign without loading this file).

This file must be its own compilation unit, loaded before the first ML that
names Foreign: name resolution happens when a unit is compiled.
*)

local
  val isabelle_ns = ML_Env.make_name_space ML_Env.Isabelle
  val bootstrap_thy = Thy_Info.get_theory "ML_Bootstrap"
  fun from_bootstrap name =
    Context.setmp_generic_context (SOME (Context.Theory bootstrap_thy))
      (fn () => #lookupStruct isabelle_ns name) ()
in
  val _ =
    (case from_bootstrap "Foreign" of
      SOME v => #enterStruct ML_Name_Space.global ("Foreign", v)
    | NONE => error "rescue_foreign.ML: structure Foreign not found in theory ML_Bootstrap")
end
