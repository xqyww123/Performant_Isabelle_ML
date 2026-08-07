theory Skel_Boundary
  imports Main
begin

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>

text \<open>Deliberate attempts to break the skeleton.\<close>

axiomatization
  aa :: nat and bb :: nat and cc :: nat and
  ff :: "nat \<Rightarrow> nat" and gg :: "nat \<Rightarrow> nat" and hh :: "nat \<Rightarrow> nat" and
  pp :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
  qq :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" and
  rr :: "(nat \<Rightarrow> nat) \<Rightarrow> nat"

ML \<open>
val ctxt0 = \<^context>;
val thy0 = Proof_Context.theory_of ctxt0;
val natT = \<^typ>\<open>nat\<close>;
fun mk_thm t = Skip_Proof.make_thm thy0 t;
fun rule l r = mk_thm (Logic.mk_equals (l, r));
fun var s = Var ((s, 0), natT);
val x = var "x"; val y = var "y"; val z = var "z";
val aa = \<^term>\<open>aa\<close>; val bb = \<^term>\<open>bb\<close>; val cc = \<^term>\<open>cc\<close>;
val ff = \<^term>\<open>ff\<close>; val gg = \<^term>\<open>gg\<close>; val hh = \<^term>\<open>hh\<close>;
val pp = \<^term>\<open>pp\<close>; val qq = \<^term>\<open>qq\<close>; val rr = \<^term>\<open>rr\<close>;
val pctxt = ctxt0 |> Config.put Syntax_Trans.eta_contract false |> Config.put show_types true;
fun show t = Syntax.string_of_term pctxt t;

fun result mode net ct =
  (case Exn.capture (fn () =>
      Merely_Rewrite.rewrite_conv_mode mode Merely_Rewrite.default_options net ctxt0 ct) () of
    Exn.Res th => show (Thm.term_of (Thm.rhs_of th))
  | Exn.Exn e => "EXN " ^ Runtime.exn_message e);

fun compare label rules input =
  let
    val net = Merely_Rewrite.make_rules rules;
    val ct = Thm.cterm_of ctxt0 input;
    val a = result Merely_Rewrite.Reference net ct;
    val b = result Merely_Rewrite.Skeleton net ct;
  in
    writeln (label ^ "\n    input      " ^ show input ^
             "\n    reference  " ^ a ^ "\n    skeleton   " ^ b ^
             (if a = b then "\n    AGREE" else "\n    *** DIFFER ***"))
  end;
\<close>

section \<open>B1: a rule with a schematic on the right that is not on the left\<close>

text \<open>
  `ff ?x == gg ?y' leaves `?y' uninstantiated, so the result carries a schematic
  variable that came from the RULE, not from the term.  The skeleton says that
  position is a hole, i.e. "material out of the already-normal term" -- which it is
  not.  If the rule set also contains a rule that matches a bare schematic, the
  pruned traversal skips a redex the unpruned one rewrites.

  `Raw_Simplifier' refuses such rules outright (rewrite_rule_extra_vars,
  raw_simplifier.ML:172); this module accepts them, and the module's own header
  already lists them as a divergence family that nothing catches.
\<close>

ML \<open>
(*A schematic-headed rule of type nat matches EVERY node of type nat, so it flattens
  the term before the rule with the extra variable can ever fire.  The way to reach
  the case is to make the extra variable FUNCTION-valued: `?P == hh' is then a
  candidate only at function positions, of which the leftover schematic is one.*)
val fT = natT --> natT;
fun fvar s = Var ((s, 0), fT);

compare "B1a extra variable on the right, plus a schematic-headed rule (first try)"
  [rule (ff $ x) (gg $ y), rule z cc] (ff $ aa);

compare "B1b extra variable on the right, no schematic-headed rule"
  [rule (ff $ x) (gg $ y), rule (hh $ x) cc] (ff $ aa);

compare "B1c extra FUNCTION variable on the right, plus a schematic-headed rule"
  [rule (qq $ fvar "p") (rr $ fvar "q"), rule (fvar "P") hh] (qq $ gg);
\<close>

section \<open>B2: matching that eta-contracts the instance\<close>

ML \<open>
val eta_body = Abs ("u", natT, hh $ Bound 0);
compare "B2a rule copies a function-valued hole"
  [rule (qq $ Var (("p", 0), natT --> natT)) (rr $ Var (("p", 0), natT --> natT))]
  (qq $ eta_body);
compare "B2b same, plus a rule on the eta-contracted head"
  [rule (qq $ Var (("p", 0), natT --> natT)) (rr $ Var (("p", 0), natT --> natT)),
   rule (hh $ x) (gg $ x)]
  (qq $ eta_body);
\<close>

section \<open>B3: a caller-supplied skeleton that is a lie\<close>

text \<open>
  `bottom_fixpoint_skel_conv' takes the skeleton on trust.  A caller that hands back
  a skeleton with a hole where the material is new gets a silently incomplete
  rewrite -- no exception, no warning.  This is the API's sharpest edge and the
  reason `rewrs_net_skel_conv' should be the only supported way to produce one.
\<close>

ML \<open>
let
  val rules = [rule (ff $ x) (gg $ (hh $ x)), rule (gg $ (hh $ y)) (pp $ y $ y)];
  val net = Merely_Rewrite.make_rules rules;
  val ct = Thm.cterm_of ctxt0 (ff $ aa);
  (*a liar: claims the whole result is a hole*)
  val liar =
    Merely_Rewrite.single_step_rewrite_skel_conv
      (fn ctxt => fn th => fn ct' => (Conv.rewr_conv (Thm.transfer' ctxt th) ct', Var (("h", 0), natT)))
      net;
  val honest = Merely_Rewrite.rewrs_net_skel_conv net;
  fun run step =
    show (Thm.term_of (Thm.rhs_of
      (Merely_Rewrite.bottom_fixpoint_skel_conv Merely_Rewrite.default_options step ctxt0 ct)));
in
  writeln ("B3 honest skeleton   " ^ run honest ^
           "\n   lying  skeleton   " ^ run liar)
end;
\<close>

section \<open>B4: how far the beta guard gives up\<close>

text \<open>
  The guard is all-or-nothing per step: one beta contraction anywhere in the
  right-hand side, including inside material that came out of the term, and the
  whole step's skeleton degrades to the wildcard.  The rewrite is still correct;
  only the pruning is lost.  This row measures how often that costs something.
\<close>

ML \<open>
(*B5: the same lie, at the term level, and the cross-layer difference that the
  extra-variable family causes for a reason that has nothing to do with skeletons.*)
let
  val rules = [rule (ff $ x) (gg $ (hh $ x)), rule (gg $ (hh $ y)) (pp $ y $ y)];
  val net = Merely_Rewrite.make_rules rules;
  val t = ff $ aa;
  val liar =
    Merely_Rewrite.single_step_rewrite_skel_term
      (fn ctxt => fn th => fn _ => fn t' =>
        Option.map (fn (u, _) => (u, Var (("h", 0), natT)))
          (Pattern.match_rew (Proof_Context.theory_of ctxt) t'
            (Logic.dest_equals (Thm.prop_of th))))
      net;
  fun run step =
    show (Merely_Rewrite.bottom_fixpoint_skel_term Merely_Rewrite.default_options step ctxt0 [] t);
in
  writeln ("B5 term layer, honest skeleton   " ^ run (Merely_Rewrite.rewrs_net_skel_term net) ^
           "\n   term layer, lying  skeleton   " ^ run liar)
end;

let
  val rules = [rule (ff $ x) (gg $ y)];
  val net = Merely_Rewrite.make_rules rules;
  val t = ff $ aa;
  val by_conv =
    show (Thm.term_of (Thm.rhs_of (Merely_Rewrite.rewrite_conv net ctxt0 (Thm.cterm_of ctxt0 t))));
  val by_term = show (Merely_Rewrite.rewrite_term net ctxt0 t);
in
  writeln ("B6 extra variable on the right -- the ONE known cross-layer difference" ^
           "\n   conv layer  " ^ by_conv ^ "   (Conv.rewr_conv does Thm.incr_indexes)" ^
           "\n   term layer  " ^ by_term ^ "   (Pattern.match_rew does not)")
end;
\<close>

ML \<open>
let
  val PV = Var (("P", 0), natT --> natT);
  val rules = [rule (qq $ Abs ("u", natT, PV $ Bound 0)) (ff $ (PV $ aa)), rule (ff $ x) (gg $ x)];
  val net = Merely_Rewrite.make_rules rules;
  val big = funpow 6 (fn t => pp $ t $ t) cc;
  val ct = Thm.cterm_of ctxt0 (qq $ Abs ("u", natT, pp $ Bound 0 $ big));
  fun count mode =
    let
      val n = Unsynchronized.ref 0;
      fun bump f c t = (n := ! n + 1; f c t);
      val cv =
        (case mode of
          Merely_Rewrite.Skeleton =>
            Merely_Rewrite.bottom_fixpoint_skel_conv Merely_Rewrite.default_options
              (bump (Merely_Rewrite.rewrs_net_skel_conv net)) ctxt0
        | _ =>
            Merely_Rewrite.bottom_fixpoint_conv_mode mode Merely_Rewrite.default_options
              (bump (Merely_Rewrite.rewrs_net_conv net)) ctxt0);
    in (cv ct; ! n) end;
in
  writeln ("B4 visits without skeleton " ^ string_of_int (count Merely_Rewrite.No_Skeleton) ^
           ", with skeleton " ^ string_of_int (count Merely_Rewrite.Skeleton) ^
           "  (a rule whose right-hand side beta-reduces gives up all pruning at that step)")
end;
\<close>

ML \<open>
(*DC8 (MERELY_REWRITE_EAGER_BETA_PLAN.md section 8.4b): the default step limit is a
  decision, not an accident.  The value is not exported, so pin the source text.*)
let
  val src = File.read (Path.append (Resources.master_directory \<^theory>)
                        (Path.explode "library/merely_rewrite.ML"));
in
  if String.isSubstring "val default_step_limit = SOME 4000000;" src then ()
  else error "DC8: default_step_limit is not SOME 4000000"
end
\<close>

end
