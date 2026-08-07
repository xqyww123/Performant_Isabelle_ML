theory Skel_Probe2
  imports Main
begin
ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>
axiomatization ff :: "nat \<Rightarrow> nat" and gg :: "nat \<Rightarrow> nat"
ML \<open>
val ctxt0 = \<^context>; val thy0 = Proof_Context.theory_of ctxt0;
val natT = \<^typ>\<open>nat\<close>;
val x = Var (("x",0), natT);
val ff = \<^term>\<open>ff\<close>; val gg = \<^term>\<open>gg\<close>;
val r = Skip_Proof.make_thm thy0 (Logic.mk_equals (ff $ x, gg $ x));
val net = Merely_Rewrite.make_rules [r];
fun probe t =
  writeln (Syntax.string_of_term ctxt0 t ^ "  -> candidates " ^
    string_of_int (length (iNet.match_term net t)) ^
    "  match_rew " ^
    (case Exn.capture (fn () => Pattern.match_rew thy0 t (ff $ x, gg $ x)) () of
       Exn.Res NONE => "NONE"
     | Exn.Res (SOME (u,_)) => Syntax.string_of_term ctxt0 u
     | Exn.Exn e => "EXN " ^ Runtime.exn_message e));
val _ = probe (ff $ \<^term>\<open>0::nat\<close>);
val _ = probe (ff $ Bound 0);
val _ = probe (ff $ (ff $ Bound 0));
val _ = writeln ("fastype_of (Bound 0): " ^
  (case Exn.capture (fn () => fastype_of (Bound 0)) () of Exn.Res T => "ok" | Exn.Exn e => Runtime.exn_message e));
\<close>
end
