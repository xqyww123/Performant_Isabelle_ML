theory Skel_X
  imports Main
begin
ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>
axiomatization aa :: nat and ff :: "nat \<Rightarrow> nat" and gg :: "nat \<Rightarrow> nat"
ML \<open>
val ctxt0 = \<^context>; val thy0 = Proof_Context.theory_of ctxt0;
val natT = \<^typ>\<open>nat\<close>;
fun rule l r = Skip_Proof.make_thm thy0 (Logic.mk_equals (l, r));
val x = Var (("x",0),natT); val y = Var (("y",0),natT);
val aa = \<^term>\<open>aa\<close>; val ff = \<^term>\<open>ff\<close>; val gg = \<^term>\<open>gg\<close>;
fun dump (Const (c,_)) = c
  | dump (Free (v,_)) = "F"^v
  | dump (Var ((v,i),_)) = "?"^v^string_of_int i
  | dump (Bound i) = "B"^string_of_int i
  | dump (Abs (v,_,t)) = "%"^v^"."^dump t
  | dump (t $ u) = "("^dump t^" "^dump u^")";
val net = Merely_Rewrite.make_rules [rule (ff $ x) (gg $ y)];
val t = ff $ aa;
val c = Thm.term_of (Thm.rhs_of (Merely_Rewrite.rewrite_conv net ctxt0 (Thm.cterm_of ctxt0 t)));
val m = Merely_Rewrite.rewrite_term net ctxt0 t;
val _ = writeln ("CROSS conv=" ^ dump c ^ "  term=" ^ dump m ^
                 (if dump c = dump m then "  SAME" else "  DIFFER"));

(*same, but the INPUT already carries a schematic: now Thm.incr_indexes has
  something to do and the two layers can be told apart*)
val t2 = ff $ Var (("y",0), natT);
val c2 = Thm.term_of (Thm.rhs_of (Merely_Rewrite.rewrite_conv net ctxt0 (Thm.cterm_of ctxt0 t2)));
val m2 = Merely_Rewrite.rewrite_term net ctxt0 t2;
val _ = writeln ("CROSS2 conv=" ^ dump c2 ^ "  term=" ^ dump m2 ^
                 (if dump c2 = dump m2 then "  SAME" else "  DIFFER"));
\<close>
end
