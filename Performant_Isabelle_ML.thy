theory Performant_Isabelle_ML
  imports Pure
begin

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/hash_table.ML\<close>
ML_file \<open>library/term_size.ML\<close>
ML_file \<open>library/pattern.ML\<close>

(* MessagePack serialization library (mlmsgpack), relocated here from Isabelle_RPC
   so it is reachable by any session based on Performant_Isabelle_ML
   (e.g. Auto_Sledgehammer's proof cache). Load order matters:
   aux \<rightarrow> realprinter \<rightarrow> mlmsgpack. *)
ML_file \<open>contrib/mlmsgpack/mlmsgpack-aux.sml\<close>
ML_file \<open>contrib/mlmsgpack/realprinter-packreal.sml\<close>
ML_file \<open>contrib/mlmsgpack/mlmsgpack.sml\<close>

end
