theory Performant_Isabelle_ML
  imports Pure
begin

(* First: Poly/ML's Foreign is bound again in the global ML name space (see the file).
   Its own compilation unit, ahead of every ML that names Foreign. *)
ML_file \<open>library/rescue_foreign.ML\<close>

(* From here on, Timeout.apply is the accounted version (see the file). *)
ML_file \<open>library/accounted_timeout.ML\<close>

(* Per-thread CPU clocks, a measurement in them, and Thread_CPU.apply, a
   timeout charged in them; needs Foreign (above) and Interrupt_Family
   (accounted_timeout.ML).  The native library (library/native/build
   <platform>, once per machine) is loaded lazily and optional: without it
   there is no clock. *)
ML_file \<open>library/thread_cpu.ML\<close>

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/inet_collection.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>
ML_file \<open>library/hash_table.ML\<close>
ML_file \<open>library/dynamic_array.ML\<close>
ML_file \<open>library/term_size.ML\<close>
ML_file \<open>library/theory_data_with_constructor.ML\<close>
ML_file \<open>library/event_log.ML\<close>
ML_file \<open>library/exception_log.ML\<close>
ML_file \<open>library/race.ML\<close>

(* MessagePack serialization library (mlmsgpack), relocated here from Isabelle_RPC
   so it is reachable by any session based on Performant_Isabelle_ML
   (e.g. Auto_Sledgehammer's proof cache). Load order matters:
   aux \<rightarrow> realprinter \<rightarrow> mlmsgpack. *)
ML_file \<open>contrib/mlmsgpack/mlmsgpack-aux.sml\<close>
ML_file \<open>contrib/mlmsgpack/realprinter-packreal.sml\<close>
ML_file \<open>contrib/mlmsgpack/mlmsgpack.sml\<close>

end
