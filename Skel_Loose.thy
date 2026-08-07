theory Skel_Loose
  imports Main
begin

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>

text \<open>
  The term layer exists so that a term with a loose \<open>Bound\<close> can be rewritten at all.
  Two different questions are asked here.

  1. A binder the traversal itself walks past.  The traversal pushes it onto the
     \<open>bvs\<close> list and leaves the body untouched; the substituter lifts every binding
     by its landing depth, so a binder from a rule's right-hand side cannot capture
     anything.  MEASURED BELOW, and cross-checked against the conv layer.

  2. A \<open>Bound\<close> that was ALREADY loose in the input.  Through the bvs-taking entry
     (\<open>rewrite_term_bvs\<close>) such positions are ordinary rewritable material: the
     matcher types them from \<open>bvs\<close>, and material moved under a rule-supplied
     binder comes out lifted.  Hand-computed expectations below.

  HISTORY.  Before the bvs rework (MERELY_REWRITE_BVS_THREADING_PLAN.md) the
  matcher had no way to type a loose \<open>Bound\<close>: the higher-order path refused the
  binding -- a silently skipped rewrite -- and the first-order fallback could
  CAPTURE one under a rule-supplied binder.  The samples in section 2 asserted
  exactly those behaviours then; they are flipped to the correct expectations
  now (plan B3(4)).
\<close>

axiomatization
  aa :: nat and
  ff :: "nat \<Rightarrow> nat" and gg :: "nat \<Rightarrow> nat" and
  pp :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
  qq :: "(nat \<Rightarrow> nat) \<Rightarrow> nat"

ML \<open>
val ctxt0 = \<^context>;
val thy0 = Proof_Context.theory_of ctxt0;
val natT = \<^typ>\<open>nat\<close>;
fun mk_thm t = Skip_Proof.make_thm thy0 t;
fun rule l r = mk_thm (Logic.mk_equals (l, r));
fun var s = Var ((s, 0), natT);
val x = var "x";
val aa = \<^term>\<open>aa\<close>; val ff = \<^term>\<open>ff\<close>; val gg = \<^term>\<open>gg\<close>;
val pp = \<^term>\<open>pp\<close>; val qq = \<^term>\<open>qq\<close>;

fun dumpT (Type (n, Ts)) = "T" ^ n ^ "[" ^ implode_space (map dumpT Ts) ^ "]"
  | dumpT (TFree (n, S)) = "F" ^ n ^ "{" ^ implode_space S ^ "}"
  | dumpT (TVar ((n, i), S)) = "V" ^ n ^ string_of_int i ^ "{" ^ implode_space S ^ "}";
fun dump (Const (c, T)) = "c<" ^ c ^ ":" ^ dumpT T ^ ">"
  | dump (Free (y, T)) = "f<" ^ y ^ ":" ^ dumpT T ^ ">"
  | dump (Var ((y, i), T)) = "v<" ^ y ^ string_of_int i ^ ":" ^ dumpT T ^ ">"
  | dump (Bound i) = "b<" ^ string_of_int i ^ ">"
  | dump (Abs (y, T, t)) = "A<" ^ y ^ ":" ^ dumpT T ^ ">(" ^ dump t ^ ")"
  | dump (t $ u) = "(" ^ dump t ^ " . " ^ dump u ^ ")";

fun rw rules t =
  Merely_Rewrite.rewrite_term (Merely_Rewrite.make_rules rules) ctxt0 t;

val bvsL = map (fn i => ("z" ^ string_of_int i, natT)) (0 upto 5);
val bvs1 = [("z0", natT)];
\<close>

section \<open>The conv layer cannot even be handed the input\<close>

ML \<open>
val loose = ff $ Bound 0;
val _ =
  writeln ("cterm_of on a term with a loose Bound: " ^
    (case Exn.capture (fn () => Thm.cterm_of ctxt0 loose) () of
      Exn.Res _ => "accepted (?!)"
    | Exn.Exn e => "rejected -- " ^ Runtime.exn_message e));
\<close>

section \<open>1. binders the traversal walks past: no capture\<close>

text \<open>
  The rule moves its hole under a binder the rule itself introduces.  The
  substituter lifts the binding by its landing depth, so the \<open>Bound 0\<close> standing
  for \<open>u\<close> is NOT captured by \<open>w\<close>; a traversal that forgot the lift would return
  \<open>qq (\<lambda>u. qq (\<lambda>w. pp w w))\<close>.
\<close>

ML \<open>
val move_rule = [rule (ff $ x) (qq $ Abs ("w", natT, pp $ x $ Bound 0))];
val nested = qq $ Abs ("u", natT, ff $ Bound 0);

val by_term = rw move_rule nested;
val by_conv =
  Thm.term_of (Thm.rhs_of
    (Merely_Rewrite.rewrite_conv (Merely_Rewrite.make_rules move_rule) ctxt0
      (Thm.cterm_of ctxt0 nested)));
val _ =
  writeln ("term layer  " ^ dump by_term ^ "\n    " ^ Syntax.string_of_term ctxt0 by_term ^
           "\nconv layer  " ^ dump by_conv ^ "\n    " ^ Syntax.string_of_term ctxt0 by_conv ^
           "\n" ^ (if dump by_term = dump by_conv then "AGREE -- no capture"
                   else "*** DIFFER ***"));
val _ = if dump by_term = dump by_conv then () else error "section 1: layers differ";
\<close>

section \<open>2. a Bound that was already loose in the input\<close>

ML \<open>
fun expect label rules bvs t e =
  let
    val got = Merely_Rewrite.rewrite_term_bvs (Merely_Rewrite.make_rules rules) ctxt0 bvs t;
  in
    if got aconv e then writeln (label ^ ": ok")
    else error (cat_lines [label ^ ": MISMATCH",
      "  input    " ^ dump t, "  expected " ^ dump e, "  got      " ^ dump got])
  end;

(*(a) the hole takes the loose Bound, typed from bvs*)
val _ = expect "L2a  ff ?x == gg ?x  on  ff B0" [rule (ff $ x) (gg $ x)]
          bvs1 (ff $ Bound 0) (gg $ Bound 0);

(*(b) the hole is moved under a NEW binder: lifted, not captured*)
val _ = expect "L2b  hole under new binder, lifted" move_rule
          bvs1 (ff $ Bound 0) (qq $ Abs ("w", natT, pp $ Bound 1 $ Bound 0));

(*(c) a ground rule beside a loose Bound, as before*)
val _ = expect "L2c  ground rule beside loose Bound" [rule (ff $ aa) (gg $ aa)]
          bvs1 (pp $ (ff $ aa) $ Bound 0) (pp $ (gg $ aa) $ Bound 0);

(*(d) hole rule, matched material closed, as before*)
val _ = expect "L2d  hole rule, closed material" [rule (ff $ x) (gg $ x)]
          bvs1 (pp $ (ff $ aa) $ Bound 0) (pp $ (gg $ aa) $ Bound 0);

(*(e) a bare schematic rule now fires on the loose Bound as well; every nat
  subterm collapses to aa bottom-up, so the whole term does*)
val _ = expect "L2e  bare schematic rule" [rule x aa]
          bvs1 (pp $ (ff $ aa) $ Bound 0) aa;

(*(f) the loose Bound sits under a binder the traversal walks past*)
val _ = expect "L2f  loose Bound under walked binder" [rule (ff $ x) (gg $ x)]
          bvs1 (qq $ Abs ("u", natT, pp $ (ff $ aa) $ Bound 1))
               (qq $ Abs ("u", natT, pp $ (gg $ aa) $ Bound 1));
\<close>

section \<open>3. skeleton on/off on loose-Bound input\<close>

ML \<open>
fun both label rules t =
  let
    val net = Merely_Rewrite.make_rules rules;
    fun run mode =
      Exn.capture (fn () =>
        Merely_Rewrite.rewrite_term_mode mode Merely_Rewrite.default_options
          net ctxt0 bvsL t) ();
    (*compare on the structural dump only: `Syntax.string_of_term' emits PIDE
      markup whose serial numbers differ from call to call, so it is fine to LOOK at
      but must not be compared*)
    fun sh (Exn.Res u) = dump u
      | sh (Exn.Exn e) = "EXN " ^ Runtime.exn_message e;
    fun pr (Exn.Res u) = Syntax.string_of_term ctxt0 u
      | pr (Exn.Exn _) = "";
    val ra = run Merely_Rewrite.Reference;
    val rb = run Merely_Rewrite.No_Skeleton;
    val rc = run Merely_Rewrite.Skeleton;
    val (a, b, c) = (sh ra, sh rb, sh rc);
  in
    writeln (label ^ "\n    " ^ c ^ "\n    " ^ pr rc ^
      (if a = b andalso b = c then "\n    all three agree"
       else "\n    *** DIFFER ***\n    " ^ a ^ "\n    " ^ b));
    if a = b andalso b = c then () else error (label ^ ": modes differ")
  end;

val shell = [rule (ff $ x) (gg $ (pp $ x $ x)), rule (gg $ (pp $ aa $ aa)) aa];

val _ = both "L3a ground rule, loose Bounds around it"
          [rule (ff $ aa) (gg $ aa)] (pp $ (ff $ aa) $ (ff $ (ff $ Bound 3)));
val _ = both "L3b shell redex, under a binder we walk past, loose Bound alongside"
          shell (qq $ Abs ("u", natT, pp $ (ff $ aa) $ Bound 5));
val _ = both "L3c hole material loose-Bound-free, sibling is not"
          [rule (pp $ x $ aa) (ff $ x)] (pp $ (pp $ (ff $ aa) $ aa) $ (Bound 2));
val _ = both "L3d schematic-headed rule at every node, loose Bound present"
          [rule x aa] (pp $ (ff $ aa) $ Bound 2);
\<close>

end
