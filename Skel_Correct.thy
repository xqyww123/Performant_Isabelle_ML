theory Skel_Correct
  imports Main
begin

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>

axiomatization
  aa :: nat and bb :: nat and cc :: nat and dd :: nat and
  ff :: "nat \<Rightarrow> nat" and gg :: "nat \<Rightarrow> nat" and
  hh :: "nat \<Rightarrow> nat" and kk :: "nat \<Rightarrow> nat" and
  pp :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
  qq :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" and
  rr :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" and
  ss :: "nat \<Rightarrow> nat \<Rightarrow> bool" and
  AA :: bool and BB :: bool

section \<open>Harness\<close>

ML \<open>
val ctxt0 = \<^context>;
val thy0 = Proof_Context.theory_of ctxt0;

(*printing context: eta-contraction OFF, so that an eta-expandable subterm that no
  rule touched is visible as such.  Without this the printer hides exactly the kind
  of damage this module exists to avoid.*)
val pctxt =
  ctxt0
  |> Config.put Syntax_Trans.eta_contract false
  |> Config.put show_types true;

(*EXACT structural text: binder names, bound indices, types and all.  `aconv' alone
  is not enough -- it is alpha-equality, so it says "same" when the binder names
  have changed, and binder names are half of what this module promises to preserve.
  `Syntax.string_of_term' alone is not enough either, since the printer normalises.
  Everything below compares BOTH this and the printed string.*)
fun dumpT (Type (n, Ts)) = "T" ^ n ^ "[" ^ implode_space (map dumpT Ts) ^ "]"
  | dumpT (TFree (n, S)) = "F" ^ n ^ "{" ^ implode_space S ^ "}"
  | dumpT (TVar ((n, i), S)) = "V" ^ n ^ string_of_int i ^ "{" ^ implode_space S ^ "}";

fun dump (Const (c, T)) = "c<" ^ c ^ ":" ^ dumpT T ^ ">"
  | dump (Free (x, T)) = "f<" ^ x ^ ":" ^ dumpT T ^ ">"
  | dump (Var ((x, i), T)) = "v<" ^ x ^ string_of_int i ^ ":" ^ dumpT T ^ ">"
  | dump (Bound i) = "b<" ^ string_of_int i ^ ">"
  | dump (Abs (x, T, t)) = "A<" ^ x ^ ":" ^ dumpT T ^ ">(" ^ dump t ^ ")"
  | dump (t $ u) = "(" ^ dump t ^ " . " ^ dump u ^ ")";

fun mk_thm t = Skip_Proof.make_thm thy0 t;
fun rule l r = mk_thm (Logic.mk_equals (l, r));

val natT = \<^typ>\<open>nat\<close>;
fun var s = Var ((s, 0), natT);
val x = var "x"; val y = var "y"; val z = var "z";
val PV = Var (("P", 0), natT --> natT);

val aa = \<^term>\<open>aa\<close>; val bb = \<^term>\<open>bb\<close>;
val cc = \<^term>\<open>cc\<close>; val dd = \<^term>\<open>dd\<close>;
val ff = \<^term>\<open>ff\<close>; val gg = \<^term>\<open>gg\<close>;
val hh = \<^term>\<open>hh\<close>; val kk = \<^term>\<open>kk\<close>;
val pp = \<^term>\<open>pp\<close>; val qq = \<^term>\<open>qq\<close>;
val ss = \<^term>\<open>ss\<close>;
val AA = \<^term>\<open>AA\<close>; val BB = \<^term>\<open>BB\<close>;
fun lam t = Abs ("x", natT, t);   (*body uses Bound 0*)
val B0 = Bound 0;
\<close>

ML \<open>
(*THE VARIANTS UNDER TEST.

  CONV LAYER
    Reference     the traversal exactly as it was before skeletons: Conv.sub_conv.
    No_Skeleton   the forked traversal fed nothing but skel0 -- pruning disabled.
    Skeleton      the forked traversal with the real skeletons.
    Unguarded     Skeleton with the two guards of `rewr_skel_conv' REMOVED: the
                  skeleton is always the rule's right-hand side.  This one is here
                  to be WRONG, and to show that the guards are what makes the
                  difference rather than a precaution against something that never
                  happens.
  TERM LAYER
    Reference / No_Skeleton / Skeleton, the same three.

  FIVE COMPARISONS per case, each on the exact structural dump AND the printed
  string: conv fork, conv pruning, term fork, term pruning, and conv against term.*)

fun rewr_skel_unguarded rule ct = (Conv.rewr_conv rule ct, Thm.term_of (Thm.rhs_of rule));

fun conv_unguarded opts net ctxt =
  Merely_Rewrite.bottom_fixpoint_skel_conv opts
    (Merely_Rewrite.single_step_rewrite_skel_conv
      (fn ctxt' => rewr_skel_unguarded o Thm.transfer' ctxt') net) ctxt;

(*node visits: how often a step was ATTEMPTED.  This is the quantity skeleton
  pruning is supposed to cut down, and printing it is what keeps a "the results
  agree" table from being vacuous -- if the columns are equal, the case did not
  exercise pruning at all.*)
fun counted_conv opts mode net ctxt =
  let
    val n = Unsynchronized.ref 0;
    fun bump f ctxt' ct = (n := ! n + 1; f ctxt' ct);
    val cv =
      (case mode of
        Merely_Rewrite.Skeleton =>
          Merely_Rewrite.bottom_fixpoint_skel_conv opts
            (bump (Merely_Rewrite.rewrs_net_skel_conv net)) ctxt
      | _ =>
          Merely_Rewrite.bottom_fixpoint_conv_mode mode opts
            (bump (Merely_Rewrite.rewrs_net_conv net)) ctxt);
  in (cv, n) end;

fun counted_term opts mode net ctxt =
  let
    val n = Unsynchronized.ref 0;
    fun bump f ctxt' bvs t = (n := ! n + 1; f ctxt' bvs t);
    val rw =
      (case mode of
        Merely_Rewrite.Skeleton =>
          Merely_Rewrite.bottom_fixpoint_skel_term opts
            (bump (Merely_Rewrite.rewrs_net_skel_term net)) ctxt []
      | _ =>
          Merely_Rewrite.bottom_fixpoint_term_mode mode opts
            (bump (Merely_Rewrite.rewrs_net_term net)) ctxt []);
  in (rw, n) end;

fun show_term t =
  cat_lines ["  trm " ^ dump t, "  str " ^ Syntax.string_of_term pctxt t];

fun outcome res =
  (case res of
    Exn.Res t => cat_lines ["OK", show_term t]
  | Exn.Exn (Merely_Rewrite.DIVERGES (Merely_Rewrite.Step_Limit n, _)) =>
      "DIVERGES Step_Limit " ^ string_of_int n
  | Exn.Exn (Merely_Rewrite.DIVERGES (Merely_Rewrite.Growth _, _)) => "DIVERGES Growth"
  | Exn.Exn e => "EXN " ^ Runtime.exn_message e);

val failures = Unsynchronized.ref ([]: string list);

(*`cross' is false for cases where the two layers are KNOWN to differ and the
  difference is not about skeletons -- see the report; the only such family is a
  rule with a schematic on the right that the left does not bind, where
  `Conv.rewr_conv' renames it apart with `Thm.incr_indexes' and
  `Pattern.match_rew' does not.*)
fun check_gen cross ctxt opts (name, rules, input) =
  let
    val net = Merely_Rewrite.make_rules rules;
    val ct = Thm.cterm_of ctxt input;
    fun run_c cv = outcome (Exn.capture (fn () => Thm.term_of (Thm.rhs_of (cv ct))) ());
    fun run_t rw = outcome (Exn.capture (fn () => rw input) ());

    val (cv_ref, n_ref) = counted_conv opts Merely_Rewrite.Reference net ctxt;
    val (cv_no, n_no) = counted_conv opts Merely_Rewrite.No_Skeleton net ctxt;
    val (cv_sk, n_sk) = counted_conv opts Merely_Rewrite.Skeleton net ctxt;
    val (rw_ref, m_ref) = counted_term opts Merely_Rewrite.Reference net ctxt;
    val (rw_no, m_no) = counted_term opts Merely_Rewrite.No_Skeleton net ctxt;
    val (rw_sk, m_sk) = counted_term opts Merely_Rewrite.Skeleton net ctxt;

    val o_ref = run_c cv_ref;
    val o_no = run_c cv_no;
    val o_sk = run_c cv_sk;
    val o_un = run_c (conv_unguarded opts net ctxt);
    val t_ref = run_t rw_ref;
    val t_no = run_t rw_no;
    val t_sk = run_t rw_sk;

    val agree_fork = (o_ref = o_no);
    val agree_prune = (o_no = o_sk);
    val agree_tfork = (t_ref = t_no);
    val agree_tprune = (t_no = t_sk);
    val agree_cross = not cross orelse (o_sk = t_sk);
    val unguarded_agrees = (o_sk = o_un);
    val changed = not (String.isSubstring ("  trm " ^ dump input) o_sk);
    val broken = String.isPrefix "EXN" o_sk orelse String.isPrefix "EXN" t_sk;
    val ok =
      agree_fork andalso agree_prune andalso agree_tfork andalso agree_tprune
        andalso agree_cross andalso not broken;
    val verdict =
      (if agree_fork then "" else "CONV-FORK-DIFFERS ") ^
      (if agree_prune then "" else "CONV-PRUNE-DIFFERS ") ^
      (if agree_tfork then "" else "TERM-FORK-DIFFERS ") ^
      (if agree_tprune then "" else "TERM-PRUNE-DIFFERS ") ^
      (if agree_cross then "" else "CROSS-LAYER-DIFFERS ") ^
      (if broken then "BROKEN-CASE " else "") ^ (if ok then "pass" else "");
    val _ = if ok then () else failures := name :: ! failures;
  in
    cat_lines
      ([name ^ ": " ^ verdict ^
         "  conv visits " ^ string_of_int (! n_ref) ^ "/" ^ string_of_int (! n_no) ^
         "/" ^ string_of_int (! n_sk) ^
         "  term visits " ^ string_of_int (! m_ref) ^ "/" ^ string_of_int (! m_no) ^
         "/" ^ string_of_int (! m_sk) ^
         (if changed then "  (rewrote)" else "  (IDENTITY)") ^
         (if cross then "" else "  [cross-layer check waived]") ^
         (if unguarded_agrees then "" else "  [unguarded skeleton DISAGREES]"),
       "  = " ^ o_sk] @
       (if agree_fork then [] else ["  CONV REFERENCE = " ^ o_ref]) @
       (if agree_prune then [] else ["  CONV NO-SKELETON = " ^ o_no]) @
       (if agree_tfork then [] else ["  TERM REFERENCE = " ^ t_ref]) @
       (if agree_tprune then [] else ["  TERM NO-SKELETON = " ^ t_no]) @
       (if agree_cross then [] else ["  TERM = " ^ t_sk]) @
       (if unguarded_agrees then [] else ["  CONV UNGUARDED = " ^ o_un]))
  end;

val check = check_gen true;
val check_no_cross = check_gen false;

fun report ctxt opts cases = writeln (cat_lines (map (check ctxt opts) cases));
fun report_no_cross ctxt opts cases =
  writeln (cat_lines (map (check_no_cross ctxt opts) cases));

(*a short step limit for the divergence cases, so the run does not spend minutes
  proving that six traversals all give up in the same way*)
val short: Merely_Rewrite.options =
  SOME {size_check = SOME true, step_limit = SOME (SOME 2000),
        growth_factor = NONE, growth_offset = NONE};
\<close>

section \<open>Corpus\<close>

ML \<open>
(*C1-C4: the shell of a rule's right-hand side is new material and may itself be a
  redex -- the case the skeleton is most likely to get wrong.*)
val shell_rules = [rule (ff $ x) (gg $ (hh $ x)), rule (gg $ (hh $ y)) (kk $ y)];

val corpus_shell =
 [("C1 shell-redex", shell_rules, ff $ aa),
  ("C2 shell-redex nested", shell_rules, pp $ (ff $ aa) $ (ff $ (ff $ bb))),
  ("C3 shell-redex under binder", shell_rules, qq $ lam (ff $ B0)),
  ("C4 shell-redex three deep",
    shell_rules @ [rule (kk $ z) (pp $ z $ z)],
    pp $ (pp $ (ff $ aa) $ bb) $ (qq $ lam (pp $ (ff $ B0) $ (ff $ cc))))];

(*C5-C7: hits at different depths, deep nesting.*)
val corpus_depth =
 [("C5 hit at internal node", [rule (pp $ aa $ y) (ff $ y), rule (ff $ bb) cc],
    pp $ (pp $ aa $ bb) $ (pp $ aa $ (pp $ aa $ bb))),
  ("C6 deep spine",
    [rule (ff $ x) (gg $ x)],
    funpow 8 (fn t => pp $ (ff $ t) $ (gg $ t)) aa),
  ("C7 hit only at the very top", [rule (pp $ x $ y) (pp $ y $ x)] (*fires once? no: permutative*)
     |> K [rule (qq $ Abs ("u", natT, ff $ Bound 0)) dd],
    qq $ lam (ff $ B0))];

(*C8-C9: binders.  C9 is the regression for the extended context that
  `Conv.abs_conv' hands back: two adjacent meta-alls, inner body using the outer
  bound variable.*)
val corpus_binder =
 [("C8 rewrite under lambda", [rule (ff $ x) (gg $ x)], qq $ lam (pp $ (ff $ B0) $ (ff $ aa))),
  ("C9 two adjacent meta-alls, inner uses outer",
    [rule (HOLogic.mk_Trueprop (HOLogic.mk_conj (ss $ x $ y, AA)))
          (HOLogic.mk_Trueprop (HOLogic.mk_conj (ss $ y $ x, BB)))],
    Logic.all (Free ("u", natT))
      (Logic.all (Free ("w", natT))
        (HOLogic.mk_Trueprop
          (HOLogic.mk_conj (ss $ Free ("u", natT) $ Free ("w", natT), AA))))),
  ("C10 meta-alls, rewrite deep inside", [rule (ff $ x) (gg $ x)],
    Logic.all (Free ("u", natT))
      (Logic.all (Free ("w", natT))
        (HOLogic.mk_Trueprop
          (ss $ (ff $ Free ("u", natT)) $ (ff $ (pp $ Free ("w", natT) $ Free ("u", natT)))))))];

(*C11-C14: beta.  These are built in ML on purpose: `Syntax.read_term' would
  contract them on the way in.*)
val beta_redex = Abs ("v", natT, ff $ Bound 0) $ aa;   (*(%v. ff v) aa*)

val corpus_beta =
 [("C11 beta-redex in the input, rule fires inside it",
    [rule (ff $ x) (gg $ x)], pp $ beta_redex $ bb),
  ("C12 beta-redex in the input, rule fires at the node above it",
    [rule (ff $ x) (gg $ x), rule (pp $ x $ bb) (hh $ x)], pp $ beta_redex $ bb),
  ("C13 rule right-hand side has a beta-redex",
    [rule (ff $ x) (Abs ("w", natT, gg $ Bound 0) $ x), rule (gg $ aa) bb], ff $ aa),
  ("C14 rule right-hand side has a beta-redex, hole material reused",
    [rule (ff $ x) (Abs ("w", natT, pp $ Bound 0 $ Bound 0) $ x), rule (pp $ aa $ aa) cc],
    ff $ aa)];

(*C15-C17: higher-order patterns.  C15 is the counterexample that kills an
  unguarded skeleton: the deep beta of `Conv.rewr_conv' moves shell material (the
  constant `aa' from the rule's right-hand side) into the head position, where the
  skeleton says "hole".*)
val corpus_ho =
 [("C15 higher-order pattern, beta moves shell material into a hole position",
    [rule (qq $ Abs ("u", natT, PV $ Bound 0)) (PV $ aa), rule aa bb],
    qq $ Abs ("u", natT, pp $ Bound 0 $ cc)),
  ("C16 higher-order pattern, plain",
    [rule (qq $ Abs ("u", natT, PV $ Bound 0)) (ff $ (PV $ aa)), rule (ff $ (ff $ x)) (gg $ x)],
    qq $ Abs ("u", natT, ff $ Bound 0)),
  ("C17 higher-order pattern, instance is a constant function",
    [rule (qq $ Abs ("u", natT, PV $ Bound 0)) (PV $ aa), rule (hh $ cc) dd],
    qq $ Abs ("u", natT, hh $ cc))];

(*C18-C21: shapes of the right-hand side.*)
val corpus_rhs =
 [("C18 right-hand side is a bare hole", [rule (ff $ x) x, rule (gg $ aa) bb], ff $ (gg $ aa)),
  ("C19 hole used twice", [rule (ff $ x) (pp $ x $ x), rule (pp $ aa $ aa) cc], ff $ aa),
  ("C20 shell introduces a binder around a hole",
    [rule (ff $ x) (qq $ Abs ("w", natT, pp $ x $ (Bound 0))), rule (pp $ aa $ z) (hh $ z)],
    ff $ aa),
  ("C21 long chain at one node",
    [rule (ff $ aa) (gg $ aa), rule (gg $ aa) (hh $ aa), rule (hh $ aa) (kk $ aa),
     rule (kk $ aa) (pp $ bb $ cc), rule (pp $ bb $ cc) dd],
    pp $ (ff $ aa) $ (ff $ aa))];

(*C22-C24: nothing happens; eta must survive.*)
val corpus_idle =
 [("C22 no rule matches", [rule (ff $ x) (gg $ x)], pp $ (hh $ aa) $ (kk $ bb)),
  ("C23 empty rule set", [], qq $ lam (pp $ B0 $ aa)),
  ("C24 eta-expandable subterm no rule touches",
    [rule (ff $ x) (gg $ x)], pp $ (qq $ lam (hh $ B0)) $ (ff $ aa))];

(*C27: a schematic on the right that is not on the left.  The leftover schematic is
  material the traversal has never seen, so the skeleton must NOT call it a hole;
  see `has_extra_var'.  Without that guard this case comes out as `rr ?q'.*)
val fT = natT --> natT;
val corpus_extra =
 [("C27 extra function variable on the right, plus a schematic-headed rule",
    [rule (qq $ Var (("p", 0), fT)) (\<^term>\<open>rr\<close> $ Var (("q", 0), fT)),
     rule (Var (("P", 0), fT)) hh],
    qq $ gg),
  ("C28 extra variable on the right, nothing matches it",
    [rule (ff $ x) (gg $ y)], ff $ aa)];

(*C25-C26: divergence must be reported the same way with and without pruning.*)
val corpus_diverge =
 [("C25 growth divergence", [rule (ff $ x) (gg $ (ff $ x))], ff $ aa),
  ("C26 oscillation", [rule (ff $ aa) (gg $ aa), rule (gg $ aa) (ff $ aa)], ff $ aa)];
\<close>

ML \<open>report ctxt0 Merely_Rewrite.default_options corpus_shell\<close>
ML \<open>report ctxt0 Merely_Rewrite.default_options corpus_depth\<close>
ML \<open>report ctxt0 Merely_Rewrite.default_options corpus_binder\<close>
ML \<open>report ctxt0 Merely_Rewrite.default_options corpus_beta\<close>
ML \<open>report ctxt0 Merely_Rewrite.default_options corpus_ho\<close>
ML \<open>report ctxt0 Merely_Rewrite.default_options corpus_rhs\<close>
ML \<open>report ctxt0 Merely_Rewrite.default_options corpus_idle\<close>
ML \<open>report_no_cross ctxt0 Merely_Rewrite.default_options corpus_extra\<close>
ML \<open>report ctxt0 short corpus_diverge\<close>

section \<open>Real HOL rules\<close>

ML \<open>
val ctxt_hol = \<^context>;   (*NOT ctxt0: the rules below live in a later theory*)
val hol_rules =
  maps (Raw_Simplifier.mksimps ctxt_hol)
    (@{thms append.simps} @ @{thms list.map} @ @{thms list.size} @ @{thms rev.simps});

fun nlist n = HOLogic.mk_list natT (map (fn i => HOLogic.mk_number natT i) (1 upto n));
val appf = \<^term>\<open>(@) :: nat list \<Rightarrow> nat list \<Rightarrow> nat list\<close>;
fun app t u = appf $ t $ u;
val mapf = \<^term>\<open>map :: (nat \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> nat list\<close>;
val lengthf = \<^term>\<open>length :: nat list \<Rightarrow> nat\<close>;
val revf = \<^term>\<open>rev :: nat list \<Rightarrow> nat list\<close>;

val corpus_hol =
 [("H1 append", hol_rules, app (nlist 6) (nlist 6)),
  ("H2 map over append", hol_rules, mapf $ ff $ app (nlist 5) (nlist 5)),
  ("H3 length of append", hol_rules, lengthf $ app (nlist 8) (nlist 4)),
  ("H4 rev of append", hol_rules, revf $ app (nlist 5) (nlist 5)),
  ("H5 nested", hol_rules,
    lengthf $ (mapf $ ff $ app (app (nlist 4) (nlist 4)) (revf $ nlist 4)))];
\<close>

ML \<open>report ctxt_hol Merely_Rewrite.default_options corpus_hol\<close>

ML \<open>
if null (! failures) then writeln "ALL CASES AGREE"
else error ("MISMATCHES: " ^ commas (! failures));
\<close>

end
