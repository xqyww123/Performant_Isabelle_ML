theory Skel_Loose
  imports Main
begin

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>

text \<open>
  The term layer exists so that a term with a loose \<open>Bound\<close> can be rewritten at all.
  Two different questions are asked here and they have different answers.

  1. A binder the traversal itself walks past.  Going under it replaces the bound
     variable by a fresh free, so a pattern variable cannot capture it.  MEASURED
     BELOW, and cross-checked against the conv layer, which is capture-free by
     construction because \<open>Conv.abs_conv\<close> does the same thing.

  2. A \<open>Bound\<close> that was ALREADY loose in the input.  The answer is sharper than
     "it might be captured": \<open>Pattern.match\<close> REFUSES to bind a schematic variable to
     anything containing a loose bound variable (\<open>match_bind\<close>, pattern.ML:320-329),
     so a rule with a hole where the loose \<open>Bound\<close> sits does not fire at all.  No
     capture; a silently skipped rewrite instead.  Everything else in the same term
     is rewritten normally -- it is the MATCHED MATERIAL that must be free of loose
     bounds, not the whole term.  MEASURED BELOW, alongside
     \<open>Pattern.rewrite_term\<close> on the same inputs.
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

(*`Pattern.rewrite_term' has no "did this step change anything" guard, so a rule
  that rewrites a term to itself spins for ever there; measured below in L2e, where
  it exhausts the ML stack.  Hence the timeout.*)
fun rw_pattern rules t =
  Timeout.apply (seconds 5.0)
    (Pattern.rewrite_term thy0 (map (Logic.dest_equals o Thm.prop_of) rules) []) t;
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
  The rule moves its hole under a binder the rule itself introduces.  If the
  traversal had descended by raw de Bruijn indices, the \<open>Bound 0\<close> standing for \<open>u\<close>
  would be captured by \<open>w\<close> and the answer would be \<open>qq (\<lambda>u. qq (\<lambda>w. pp w w))\<close>.
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
\<close>

section \<open>2. a Bound that was already loose in the input\<close>

text \<open>
  The answer turns out to be sharper than "it might get captured": IT CANNOT BE
  MATCHED AT ALL.  \<open>Pattern.match\<close> refuses to bind a schematic variable to anything
  that contains a loose bound variable (\<open>match_bind\<close>, pattern.ML:320-329), so a rule
  with a hole where the loose \<open>Bound\<close> sits simply does not fire.  No capture, but
  also no rewrite, and no warning that one was skipped.

  Rewriting elsewhere in the same term is unaffected: it is the MATCHED MATERIAL
  that has to be free of loose bounds, not the whole term.
\<close>

ML \<open>
fun probe label rules t =
  let
    val a = Exn.capture (fn () => rw rules t) ();
    val b = Exn.capture (fn () => rw_pattern rules t) ();
    fun sh (Exn.Res u) = dump u ^ "   " ^ Syntax.string_of_term ctxt0 u
      | sh (Exn.Exn e) = "EXN " ^ Runtime.exn_message e;
  in
    writeln (label ^
      "\n    input                        " ^ dump t ^
      "\n    Merely_Rewrite.rewrite_term  " ^ sh a ^
      "\n    Pattern.rewrite_term         " ^ sh b)
  end;

(*(a) the hole would have to take the loose Bound: the rule does not fire*)
val _ = probe "L2a  ff ?x == gg ?x   on   ff (Bound 0)"
  [rule (ff $ x) (gg $ x)] (ff $ Bound 0);

(*(b) the same, with a rule whose right-hand side would move the hole under a NEW
  binder -- the shape that WOULD capture, if the match were allowed*)
val _ = probe "L2b  ff ?x == qq (%w. pp ?x w)   on   ff (Bound 0)"
  move_rule (ff $ Bound 0);

(*(c) a GROUND rule: no hole, so nothing to capture, and it fires normally even
  though the term around it has a loose Bound*)
val _ = probe "L2c  ff aa == gg aa   on   pp (ff aa) (Bound 0)"
  [rule (ff $ aa) (gg $ aa)] (pp $ (ff $ aa) $ Bound 0);

(*(d) a rule with a hole, but the matched material is loose-Bound-free: fires*)
val _ = probe "L2d  ff ?x == gg ?x   on   pp (ff aa) (Bound 0)"
  [rule (ff $ x) (gg $ x)] (pp $ (ff $ aa) $ Bound 0);

(*(e) a schematic-headed rule, which the net offers at EVERY node including the bare
  loose Bound.  This is the case that makes `Pattern.match' compute `fastype_of' of
  a bare `Bound' and throw; without the handler in `single_step_rewrite_term' this
  aborts the whole call.*)
val _ = probe "L2e  ?z == aa   on   pp (ff aa) (Bound 0)"
  [rule x aa] (pp $ (ff $ aa) $ Bound 0);

(*(f) the loose Bound sits under a binder the traversal walks past*)
val _ = probe "L2f  ff ?x == gg ?x   on   qq (%u. pp (ff aa) (Bound 1))"
  [rule (ff $ x) (gg $ x)] (qq $ Abs ("u", natT, pp $ (ff $ aa) $ Bound 1));
\<close>

section \<open>3. skeleton on/off on loose-Bound input\<close>

ML \<open>
fun both label rules t =
  let
    val net = Merely_Rewrite.make_rules rules;
    fun run mode =
      Exn.capture (fn () =>
        Merely_Rewrite.rewrite_term_mode mode Merely_Rewrite.default_options net ctxt0 t) ();
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
       else "\n    *** DIFFER ***\n    " ^ a ^ "\n    " ^ b))
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
