(* Self-contained checks for library/inet_collection.ML (both functor layers).

   Run it by hand -- like every other test here, it is deliberately NOT in ROOT.
   Failure is an `error'; success is silence plus the final summary line.

   The corpus is axiomatized locally (this session sits on Pure, so no HOL
   theorems are available): `r_gg'/`r_hh' share the left-hand side `ff x',
   `r_bind' carries a binder for the alpha-variant checks, `nn' is the
   non-equation a left-hand-side-keyed instance must reject. *)
theory Test_iNet_Collection
  imports "../Performant_Isabelle_ML"
begin

typedecl i

axiomatization ff gg hh :: "i \<Rightarrow> i" and cc :: i
  where r_gg: "ff x \<equiv> gg x"
    and r_hh: "ff x \<equiv> hh x"

axiomatization bind :: "(i \<Rightarrow> i) \<Rightarrow> i" and dd :: i
  where r_bind: "bind (\<lambda>x. ff (ff x)) \<equiv> dd"

axiomatization pp :: "prop"
  where nn: "PROP pp"

ML \<open>
fun check msg b = if b then () else error ("FAIL: " ^ msg);
\<close>

(* ==== P1: generic layer with a NON-thm element type (C1; also the transparent
   half of C3: T values are built OUTSIDE the instance and fed to add) ==== *)
ML \<open>
structure P = iNet_Collection(
  type T = term * string
  val eq = fn ((t, _): term * string, (u, _): term * string) => t aconv u
  val key_of = fst);

local
  val t1 = @{term "ff cc"};
  val t2 = @{term "gg cc"};
  val ctx1 = Context.Theory @{theory} |> P.add (t1, "one") |> P.add (t2, "two");
in
val _ = check "P1 content length 2" (length (P.content ctx1) = 2)
val _ = check "P1 match_term by key t1" (map #2 (iNet.match_term (P.get_net ctx1) t1) = ["one"])
val _ = check "P1 match_term by key t2" (map #2 (iNet.match_term (P.get_net ctx1) t2) = ["two"])
end
\<close>

(* ==== P2: thm layer, one lhs-keyed and one full-prop-keyed instance (C2),
   then instance isolation (C5) after the theory-level seed below ==== *)
ML \<open>
structure Rules = iNet_Thm_Collection(
  val name = \<^binding>\<open>probe_rules\<close>
  val description = "probe collection keyed by meta-equation lhs"
  val key_of = #1 o Logic.dest_equals o Thm.prop_of);

structure FooFull = iNet_Thm_Collection(
  val name = \<^binding>\<open>probe_foo\<close>
  val description = "probe collection keyed by full prop"
  val key_of = Thm.full_prop_of);
\<close>

setup \<open>Rules.setup #> FooFull.setup\<close>

declare r_gg [probe_rules]

thm probe_rules  \<comment> \<open>dynamic fact name resolves\<close>

ML \<open>
local
  val gctx = Context.Theory @{theory};
in
val _ = check "P2/C5 seeded instance holds the declaration" (length (Rules.content gctx) = 1)
val _ = check "P2/C5 other instance content stays empty" (length (FooFull.content gctx) = 0)
val _ = check "P2/C5 other instance net matches nothing"
          (null (iNet.match_term (FooFull.get_net (Context.proof_of gctx))
                   (Thm.full_prop_of @{thm r_gg})))
end
\<close>

(* ==== P3: stored entries are context-free (B1 first line), content/get
   transfers (B7), and the Merely_Rewrite consumer chain rewrites (5.3) ==== *)
ML \<open>
local
  val thy = @{theory};
  val ctxt = @{context};
  val net = Rules.get_net ctxt;
  val entries = iNet.content net;
  fun context_free th = (Thm.theory_of_thm th; false) handle Thm.CONTEXT _ => true;
  val via_theory = Rules.content (Context.Theory thy);
  val via_proof = Rules.get (Proof_Context.init_global thy);
  fun thy_of th = SOME (Thm.theory_of_thm th) handle Thm.CONTEXT _ => NONE;
  fun same_thy (SOME a, SOME b) = Context.eq_thy_id (Context.theory_id a, Context.theory_id b)
    | same_thy _ = false;
  val input = @{term "ff cc"};
  val expected = @{term "gg cc"};
in
val _ = check "P3/B1 net entries are context-free" (forall context_free entries)
val _ = check "P3/B7 content (Context.Theory) is transferred" (forall (is_some o thy_of) via_theory)
val _ = check "P3/B7 get (init_global) is transferred" (forall (is_some o thy_of) via_proof)
val _ = check "P3/B7 both outlets agree" (forall Thm.eq_thm_prop (via_theory ~~ via_proof))
val _ = check "P3/B7 certificate is the query theory itself"
          (same_thy (thy_of (hd via_theory), SOME thy))
val _ = check "P3/5.3 rewrite_term through the collection-built net"
          (Merely_Rewrite.rewrite_term net ctxt input aconv expected)
val _ = check "P3/5.3 rewrite_conv through the collection-built net"
          (Thm.prop_of (Merely_Rewrite.rewrite_conv net ctxt (Thm.cterm_of ctxt input))
           aconv Logic.mk_equals (input, expected))
end
\<close>

(* ==== P4: declaration-layer semantics, expectations written out (B3) ==== *)
ML \<open>
local
  val gctx = Context.Theory @{theory};       (*holds r_gg from the declare above*)
  val n0 = length (Rules.content gctx);
  val g_dup = Rules.add_thm @{thm r_gg} gctx;
  val g_bind = Rules.add_thm @{thm r_bind} gctx;
  val alpha = Thm.renamed_prop
                (Term.map_abs_vars (fn s => s ^ "zz") (Thm.prop_of @{thm r_bind}))
                @{thm r_bind};
  val g_alpha = g_bind |> Rules.add_thm alpha;
  val bind_key = (#1 o Logic.dest_equals o Thm.prop_of) @{thm r_bind};
  val stored_bind = hd (iNet.match_term (Rules.get_net (Context.proof_of g_alpha)) bind_key);
  val bumped = Thm.incr_indexes 7 @{thm r_gg};
  val g_idx = Rules.add_thm bumped gctx;
  val g_delmiss = Rules.del_thm @{thm r_hh} gctx;
  val g_delempty = FooFull.del_thm @{thm r_gg} gctx;
  val g_ada = gctx |> Rules.del_thm @{thm r_gg} |> Rules.add_thm @{thm r_gg};
in
val _ = check "P4/B3 baseline count 1" (n0 = 1)
val _ = check "P4/B3 duplicate add silently ignored" (length (Rules.content g_dup) = n0)
val _ = check "P4/B3 alpha-variant add silently ignored (eq_thm_prop is aconv)"
          (length (Rules.content g_alpha) = n0 + 1)
val _ = check "P4/B3 alpha-variant did NOT replace the stored rule (binder names intact)"
          (Thm.prop_of stored_bind = Thm.prop_of @{thm r_bind})
val _ = check "P4/B3 index-only variant IS inserted (count +1)"
          (length (Rules.content g_idx) = n0 + 1)
val _ = check "P4/B3 index-only variant lands in the same leaf (2 candidates)"
          (length (iNet.match_term (Rules.get_net (Context.proof_of g_idx)) @{term "ff cc"}) = 2)
val _ = check "P4/B3 del of absent rule is a silent no-op" (length (Rules.content g_delmiss) = n0)
val _ = check "P4/B3 del on empty collection is a silent no-op"
          (length (FooFull.content g_delempty) = 0)
val _ = check "P4/B3 add-del-add gives the count back" (length (Rules.content g_ada) = n0)
end
\<close>

(* ==== P5: malformed input rejected at declaration, add and del paths, with the
   instance name in the payload (B4) ==== *)
ML \<open>
local
  fun msg_of f = (f (); "NO ERROR") handle TERM (msg, _) => msg | THM (msg, _, _) => msg;
  val gctx = Context.Theory @{theory};
  val add_msg = msg_of (fn () => Rules.add_thm @{thm nn} gctx);
  val del_msg = msg_of (fn () => Rules.del_thm @{thm nn} gctx);
in
val _ = check "P5/B4 add-path payload has the instance-name prefix"
          (String.isPrefix "probe_rules: " add_msg)
val _ = check "P5/B4 del-path payload has the instance-name prefix"
          (String.isPrefix "probe_rules: " del_msg)
end
\<close>

(* ==== P6: same key, later addition first; re-add does not promote (B5;
   single-theory scope on purpose -- cross-theory order follows imports) ==== *)
ML \<open>
local
  val gctx0 = Context.Theory @{theory};
  val query = @{term "ff cc"};
  fun candidates g = iNet.match_term (Rules.get_net (Context.proof_of g)) query;
  val g1 = gctx0 |> Rules.add_thm @{thm r_hh};          (*r_gg was declared first*)
  val g2 = g1 |> Rules.add_thm @{thm r_gg};             (*duplicate re-add after r_hh*)
in
val _ = check "P6/B5 both same-key rules stored" (length (candidates g1) = 2)
val _ = check "P6/B5 later declaration comes first" (Thm.eq_thm_prop (hd (candidates g1), @{thm r_hh}))
val _ = check "P6/B5 duplicate re-add does NOT promote" (Thm.eq_thm_prop (hd (candidates g2), @{thm r_hh}))
end
\<close>

(* ==== P7: the key-semantics warning made observable -- a full-prop-keyed net
   type-checks against Merely_Rewrite and silently rewrites nothing (5.3) ==== *)
ML \<open>
local
  val ctxt = @{context};
  val ctxtF = Context.proof_map (FooFull.add_thm @{thm r_gg}) ctxt;
  val netF = FooFull.get_net ctxtF;
  val input = @{term "ff cc"};
  val res = Merely_Rewrite.rewrite_conv netF ctxtF (Thm.cterm_of ctxtF input);
  (*even when the query IS the stored equation, so the net does return 1
    candidate, the rewriter discards it*)
  val eq_term = Thm.prop_of @{thm r_gg};
  val res_eq = Merely_Rewrite.rewrite_conv netF ctxtF (Thm.cterm_of ctxtF eq_term);
in
val _ = check "P7/5.3-neg full-prop net rewrites nothing"
          (Thm.prop_of res aconv Logic.mk_equals (input, input))
val _ = check "P7/5.3-neg nothing even on the equation term itself"
          (Thm.prop_of res_eq aconv Logic.mk_equals (eq_term, eq_term))
val _ = check "P7/5.3-neg the candidate WAS retrieved (1), then discarded"
          (length (iNet.match_term netF eq_term) = 1)
end
\<close>

(* ==== P8: ML-level Proof.context-local declarations stay local (B8) ==== *)
ML \<open>
local
  val ctxt = @{context};
  val ctxt' = Context.proof_map (Rules.add_thm @{thm r_hh}) ctxt;
in
val _ = check "P8/B8 local add visible through get" (length (Rules.get ctxt') = 2)
val _ = check "P8/B8 local add visible through get_net"
          (length (iNet.match_term (Rules.get_net ctxt') @{term "ff cc"}) = 2)
val _ = check "P8/B8 local add does not leak to the original context"
          (length (Rules.get ctxt) = 1)
end
\<close>

ML \<open>writeln "Test_iNet_Collection: all checks passed"\<close>

end
