theory Performant_Isabelle_ML
  imports Pure
begin

(* From here on, Timeout.apply is the accounted version (see the file). *)
ML_file \<open>library/accounted_timeout.ML\<close>

(* Per-thread CPU clocks, a measurement in them, and Thread_CPU.apply, a
   timeout charged in them; needs Interrupt_Family (accounted_timeout.ML).
   The native library (library/native/build <platform>, once per machine) is
   loaded lazily: without it there is no clock -- and no persistent theory hash
   (xxhash.ML below), which needs it. *)
ML_file \<open>library/thread_cpu.ML\<close>

(* improved_net.ML takes no ML antiquotations: the fast_abbrev_printing feature loads
   a copy of it inside Pure, before antiquotations exist.  So its "Pure.type" literals
   stay plain strings. *)
context notes [[ML_check_strings = false]]
begin
ML_file \<open>library/improved_net.ML\<close>
end

ML_file \<open>library/inet_collection.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>
ML_file \<open>library/hash_table.ML\<close>
(* FNV-1a structural digests (Term_Digest), relocated here from Isabelle_RPC so that
   any session based on Performant_Isabelle_ML can hash terms the way Isabelle_RPC's
   universal keys do; needs the hash tables above. *)
ML_file \<open>library/term_digest.ML\<close>
(* Streaming XXH3 128-bit through the native library (no fallback without it). *)
ML_file \<open>library/xxhash.ML\<close>
(* Theory.resolve_theory: Theory.check, the context's own unfinished theory included. *)
ML_file \<open>library/resolve_theory.ML\<close>
(* Theory_Hash: the 16-byte theory identities that prefix every universal key,
   moved here from Isabelle_RPC; needs the three files above. *)
ML_file \<open>library/theory_hash.ML\<close>
ML_file \<open>library/dynamic_array.ML\<close>
ML_file \<open>library/term_size.ML\<close>
ML_file \<open>library/theory_data_with_constructor.ML\<close>
ML_file \<open>library/event_log.ML\<close>
ML_file \<open>library/exception_log.ML\<close>
ML_file \<open>library/race.ML\<close>

(* Runtime symbols (Phi_Tool_Symbol): the ML half of HOL/SSymb.thy, here so that
   serializers in Pure-based sessions (Isabelle_RPC) can carry a symbol by its
   identifier instead of its per-process numeral. *)
ML_file \<open>library/ssymb.ML\<close>

(* MessagePack serialization library (mlmsgpack), relocated here from Isabelle_RPC
   so it is reachable by any session based on Performant_Isabelle_ML
   (e.g. Auto_Sledgehammer's proof cache). Load order matters:
   aux \<rightarrow> realprinter \<rightarrow> mlmsgpack. *)
ML_file \<open>contrib/mlmsgpack/mlmsgpack-aux.sml\<close>
ML_file \<open>contrib/mlmsgpack/realprinter-packreal.sml\<close>
ML_file \<open>contrib/mlmsgpack/mlmsgpack.sml\<close>

end
