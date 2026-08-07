theory Skel_Typed
  imports Main
begin

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>

text \<open>
  Directed corpus with TWO binder base types (nat and bool).  The randomised
  corpus (Skel_Fuzz) is single-typed, so a traversal that mixes up which
  contextual binder is which -- or forgets to lift material moved under a new
  binder -- passes it whenever the confusion is type-preserving.  These samples
  make such mistakes type-visible: they are the floor demanded by the mutation
  gate of MERELY_REWRITE_BVS_THREADING_PLAN.md \<section>7.1 (mutant M3 in particular).

  All expectations are hand-computed and compared with aconv on the structural
  text; nothing is compared through the printer.
\<close>

axiomatization
  n0 :: nat and
  f0 :: "nat \<Rightarrow> nat" and f1 :: "nat \<Rightarrow> nat" and
  g0 :: "nat \<Rightarrow> nat \<Rightarrow> nat" and g1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
  qh :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" and
  qb :: "(bool \<Rightarrow> nat) \<Rightarrow> nat" and
  pb :: "bool \<Rightarrow> nat"

ML \<open>
val ctxt0 = \<^context>;
val thy0 = Proof_Context.theory_of ctxt0;
val natT = \<^typ>\<open>nat\<close>;
val boolT = \<^typ>\<open>bool\<close>;

(*structural dump for failure diagnostics only -- same shape as Skel_Fuzz's;
  never used for comparison*)
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
fun V n T = Var ((n, 0), T);

val opts: Merely_Rewrite.options =
  SOME {size_check = SOME true, step_limit = SOME (SOME 20000),
        growth_factor = NONE, growth_offset = NONE};

fun modes_term net bvs t =
  map (fn m => Merely_Rewrite.rewrite_term_mode m opts net ctxt0 bvs t)
      [Merely_Rewrite.Reference, Merely_Rewrite.No_Skeleton, Merely_Rewrite.Skeleton];

fun conv_skel net t =
  Thm.term_of (Thm.rhs_of
    (Merely_Rewrite.bottom_fixpoint_skel_conv opts
       (Merely_Rewrite.rewrs_net_skel_conv net) ctxt0 (Thm.cterm_of ctxt0 t)));

(*closed input: all three term modes AND the skeleton conv must give `expected'*)
fun check name rules input expected =
  let
    val net = Merely_Rewrite.make_rules rules;
    val outs = modes_term net [] input @ [conv_skel net input];
  in
    if forall (fn t => t aconv expected) outs then writeln (name ^ ": ok")
    else error (cat_lines
      ([name ^ ": MISMATCH", "input    " ^ dump input, "expected " ^ dump expected] @
       map (fn t => "got      " ^ dump t) outs))
  end;

(*loose input: conv layer cannot be handed these; the three term modes, entered
  through the bvs-taking entry, must agree and equal `expected'*)
fun check_loose name rules bvs input expected =
  let
    val net = Merely_Rewrite.make_rules rules;
    val outs = modes_term net bvs input;
  in
    if forall (fn t => t aconv expected) outs then writeln (name ^ ": ok")
    else error (cat_lines
      ([name ^ ": MISMATCH", "input    " ^ dump input, "expected " ^ dump expected] @
       map (fn t => "got      " ^ dump t) outs))
  end;

val qbC = \<^term>\<open>qb\<close>;
val qhC = \<^term>\<open>qh\<close>;
val pbC = \<^term>\<open>pb\<close>;
\<close>

ML \<open>
(*T1: rewriting under a bool binder at all*)
val r1 = rule (pbC $ V "b" boolT) \<^term>\<open>n0\<close>;
val _ =
  check "T1" [r1]
    (qbC $ Abs ("b", boolT, pbC $ Bound 0))
    (qbC $ Abs ("b", boolT, \<^term>\<open>n0\<close>));

(*T2: a match whose bindings take one contextual binder of EACH type.  The
  nat-typed material is Bound 1 seen through the bool binder: any traversal that
  consults the wrong entry of its binder bookkeeping for it -- reversed order,
  wrong type -- loses the rewrite (mutant M3's detector).*)
val r2 = rule (\<^term>\<open>g0\<close> $ V "x" natT $ V "y" natT)
              (\<^term>\<open>g1\<close> $ V "y" natT $ V "x" natT);
val _ =
  check "T2" [r2]
    (qhC $ Abs ("u", natT, qbC $ Abs ("b", boolT,
       \<^term>\<open>g0\<close> $ Bound 1 $ (pbC $ Bound 0))))
    (qhC $ Abs ("u", natT, qbC $ Abs ("b", boolT,
       \<^term>\<open>g1\<close> $ (pbC $ Bound 0) $ Bound 1)));

(*T3: duplication of bool-binder material by the right-hand side*)
val r3 = rule (\<^term>\<open>f0\<close> $ V "x" natT)
              (\<^term>\<open>g0\<close> $ V "x" natT $ V "x" natT);
val _ =
  check "T3" [r3]
    (qbC $ Abs ("b", boolT, \<^term>\<open>f0\<close> $ (pbC $ Bound 0)))
    (qbC $ Abs ("b", boolT, \<^term>\<open>g0\<close> $ (pbC $ Bound 0) $ (pbC $ Bound 0)));

(*T4: the right-hand side moves the binding under a NEW binder; the bool-binder
  reference inside it must come out lifted (Bound 1 through the new nat binder).
  This is the dual-typed detector for mutant M1 (substitution without lifting).*)
val r4 = rule (\<^term>\<open>f1\<close> $ V "x" natT)
              (qhC $ Abs ("w", natT, \<^term>\<open>g0\<close> $ V "x" natT $ Bound 0));
val _ =
  check "T4" [r4]
    (qbC $ Abs ("b", boolT, \<^term>\<open>f1\<close> $ (pbC $ Bound 0)))
    (qbC $ Abs ("b", boolT,
       qhC $ Abs ("w", natT, \<^term>\<open>g0\<close> $ (pbC $ Bound 1) $ Bound 0)));

(*T5: a LOOSE input whose Bound 1 is bool-typed, through the bvs-taking entry.
  BEFORE A3 the term layer silently skipped this rewrite (the defect of
  MERELY_REWRITE_BVS_THREADING_PLAN.md \<section>1(1); reproduced by the pre-A3 version
  of this sample).  With bvs = [("x", nat), ("b", bool)] the position is
  rewritable and the sample flipped to the correct expectation (plan B3(4)).*)
val t5 = \<^term>\<open>g0\<close> $ Bound 0 $ (pbC $ Bound 1);
val e5 = \<^term>\<open>g0\<close> $ Bound 0 $ \<^term>\<open>n0\<close>;
val _ = check_loose "T5(loose, bool-typed Bound)" [r1] [("x", natT), ("b", boolT)] t5 e5;

(*T6: the \<section>1(2) CAPTURE shape, flipped to the correct expectation.  A fully
  higher-order-pattern lhs never captured (the pattern path refuses to bind a
  schematic to loose-Bound material); capture came through the FIRST-ORDER
  FALLBACK, one non-pattern spot on the left (the plan's `pp (?P aa) ?x'
  example).  BEFORE A3 this sample produced the captured
  qh (%w. g0 (f0 (Bound 0)) w); with bvs = [("x", nat)] the binding must come
  out LIFTED through the new binder: Bound 1, not Bound 0.*)
val r6 = rule (\<^term>\<open>g0\<close> $ (V "P" (natT --> natT) $ \<^term>\<open>n0\<close>) $ V "x" natT)
              (qhC $ Abs ("w", natT, \<^term>\<open>g0\<close> $ V "x" natT $ Bound 0));
val t6 = \<^term>\<open>g0\<close> $ (\<^term>\<open>f0\<close> $ \<^term>\<open>n0\<close>) $ (\<^term>\<open>f0\<close> $ Bound 0);
val e6_lifted = qhC $ Abs ("w", natT, \<^term>\<open>g0\<close> $ (\<^term>\<open>f0\<close> $ Bound 1) $ Bound 0);
val _ = check_loose "T6(capture shape, now lifted)" [r6] [("x", natT)] t6 e6_lifted;
\<close>

end
