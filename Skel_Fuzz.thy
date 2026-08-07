theory Skel_Fuzz
  imports Main
begin

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>

text \<open>
  Randomised differential test.  A hand-written corpus can only cover the cases its
  author thought of; this one generates rule sets and terms by the thousand and
  demands that the three traversals agree literally, on the exact structural text.

  TERMINATION OF THE RANDOM RULE SETS is not left to luck, because a rule set that
  diverges tests nothing.  Every symbol has a LEVEL, a rule whose left-hand side has
  a head of level L may use only symbols of level below L on its right-hand side,
  and no schematic variable may occur more than once on the right-hand side.  Each
  step then replaces one occurrence of a level-L symbol by finitely many
  occurrences of smaller ones and copies the rest, which is a decrease in the
  multiset order on levels, so every generated rule set terminates.
\<close>

axiomatization
  n0 :: nat and n1 :: nat and n2 :: nat and n3 :: nat and
  f0 :: "nat \<Rightarrow> nat" and f1 :: "nat \<Rightarrow> nat" and
  f2 :: "nat \<Rightarrow> nat" and f3 :: "nat \<Rightarrow> nat" and
  g0 :: "nat \<Rightarrow> nat \<Rightarrow> nat" and g1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
  g2 :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
  qh :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" and
  qh2 :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat" and
  f5 :: "nat \<Rightarrow> nat"

ML \<open>
val ctxt0 = \<^context>;
val thy0 = Proof_Context.theory_of ctxt0;
val natT = \<^typ>\<open>nat\<close>;

fun dumpT (Type (n, Ts)) = "T" ^ n ^ "[" ^ implode_space (map dumpT Ts) ^ "]"
  | dumpT (TFree (n, S)) = "F" ^ n ^ "{" ^ implode_space S ^ "}"
  | dumpT (TVar ((n, i), S)) = "V" ^ n ^ string_of_int i ^ "{" ^ implode_space S ^ "}";
fun dump (Const (c, T)) = "c<" ^ c ^ ":" ^ dumpT T ^ ">"
  | dump (Free (x, T)) = "f<" ^ x ^ ":" ^ dumpT T ^ ">"
  | dump (Var ((x, i), T)) = "v<" ^ x ^ string_of_int i ^ ":" ^ dumpT T ^ ">"
  | dump (Bound i) = "b<" ^ string_of_int i ^ ">"
  | dump (Abs (x, T, t)) = "A<" ^ x ^ ":" ^ dumpT T ^ ">(" ^ dump t ^ ")"
  | dump (t $ u) = "(" ^ dump t ^ " . " ^ dump u ^ ")";

val pctxt = ctxt0 |> Config.put Syntax_Trans.eta_contract false |> Config.put show_types true;

(*a linear congruential generator, so that a failure is reproducible from its seed*)
val seed = Unsynchronized.ref 1;
fun srand s = seed := s;
fun rand n = (seed := (! seed * 1103515245 + 12345) mod 2147483648; (! seed div 1024) mod n);
fun pick xs = nth xs (rand (length xs));

(*symbol, arity, level*)
val nullary = [(\<^term>\<open>n0\<close>, 0), (\<^term>\<open>n1\<close>, 1), (\<^term>\<open>n2\<close>, 2), (\<^term>\<open>n3\<close>, 3)];
(*f5 sits ABOVE qh_level, so a rule headed by it may use `qh (%w. _)' -- with a
  hole inside -- on its right-hand side; no other head can (see gen_rhs).*)
val unary = [(\<^term>\<open>f0\<close>, 1), (\<^term>\<open>f1\<close>, 2), (\<^term>\<open>f2\<close>, 3), (\<^term>\<open>f3\<close>, 4),
             (\<^term>\<open>f5\<close>, 6)];
val binary = [(\<^term>\<open>g0\<close>, 2), (\<^term>\<open>g1\<close>, 3), (\<^term>\<open>g2\<close>, 4)];
val qhC = \<^term>\<open>qh\<close>;
val qh2C = \<^term>\<open>qh2\<close>;
val f5C = \<^term>\<open>f5\<close>;
val qh_level = 5;

fun below lvl xs = filter (fn (_, l) => l < lvl) xs;

(*random term.  `bs' is the list of de Bruijn indices in scope, innermost first.
  Bound leaves are biased toward an OUTER binder when one exists: matches whose
  bindings mention a non-innermost contextual binder are what exercise depth
  bookkeeping, and unbiased picks produce them too rarely.*)
fun pick_bound bs =
  if length bs >= 2 andalso rand 2 = 0 then Bound (pick (tl bs)) else Bound (pick bs);
fun gen_term d bs =
  if d <= 0 orelse rand 4 = 0 then
    (if null bs orelse rand 2 = 0 then #1 (pick nullary) else pick_bound bs)
  else
    (case rand 7 of
      0 => #1 (pick unary) $ gen_term (d - 1) bs
    | 1 => #1 (pick unary) $ gen_term (d - 1) bs
    | 2 => #1 (pick binary) $ gen_term (d - 1) bs $ gen_term (d - 1) bs
    | 3 => #1 (pick binary) $ gen_term (d - 1) bs $ gen_term (d - 1) bs
    | 4 => qhC $ Abs ("u", natT, gen_term (d - 1) (0 :: map (fn i => i + 1) bs))
    | 5 => qh2C $ Abs ("u1", natT, Abs ("u2", natT,
             gen_term (d - 1) (0 :: 1 :: map (fn i => i + 2) bs)))
    | _ => (*an explicit beta-redex: the module must contract it eagerly*)
        Abs ("v", natT, gen_term (d - 1) (0 :: map (fn i => i + 1) bs)) $ gen_term (d - 1) bs);

(*random term over symbols of level < lvl, with holes taken from `holes' -- each hole
  used AT MOST ONCE, which is what makes the rule set terminate (see the text above)*)
fun gen_rhs lvl holes d bs =
  let
    val avail = Unsynchronized.ref holes;
    fun take_hole () =
      (case ! avail of
        [] => NONE
      | h :: hs => (avail := hs; SOME h));
    val us = below lvl unary;
    val bins = below lvl binary;
    fun go d bs =
      if d <= 0 orelse rand 3 = 0 then
        (case (if rand 3 > 0 then take_hole () else NONE) of
          SOME h => h
        | NONE => if null bs orelse rand 2 = 0 then #1 (pick nullary) else Bound (pick bs))
      else
        (case rand 4 of
          0 => if null us then go 0 bs else #1 (pick us) $ go (d - 1) bs
        | 1 => if null bins then go 0 bs else #1 (pick bins) $ go (d - 1) bs $ go (d - 1) bs
        | 2 =>
            if qh_level < lvl
            then qhC $ Abs ("w", natT, go (d - 1) (0 :: map (fn i => i + 1) bs))
            else go 0 bs
        | _ => go 0 bs);
  in go d bs end;

fun mk_thm t = Skip_Proof.make_thm thy0 t;

(*a random rule.  Six families: the bare function-type schematic; `qh (%u. ?P u)',
  whose right-hand side applies ?P to new material and therefore goes through the
  deep beta of Conv.rewr_conv; `qh (%u. ?X)', whose binding must IGNORE the binder
  it sits under; `qh2 (%u1 u2. _)' with a true argument subset or a permutation;
  a left-hand side repeating one schematic at two binder depths, so the
  repeated-schematic check compares bindings stored from different depths; and
  first-order -- where an f5 head may put `qh (%w. _)' with a hole inside on its
  right-hand side (see gen_rhs).*)
fun gen_rule i =
  let
    val vname = "x" ^ string_of_int i;
    fun v k = Var ((vname ^ "_" ^ string_of_int k, 0), natT);
    fun arg k = if rand 4 > 0 then v k else gen_term 1 [];
    val fT = natT --> natT;
    (*the only kind of rule that can match a leftover schematic, and therefore the
      only kind that can tell whether the extra-variable guard in `rewr_skel_conv'
      is doing its job.  It rewrites to the lowest level symbol, so it terminates.*)
    fun bare () = mk_thm (Logic.mk_equals (Var ((vname ^ "_F", 0), fT), #1 (hd unary)));
    fun qh_P () =
      let
        val PV = Var ((vname ^ "_P", 0), fT);
        val lhs = qhC $ Abs ("u", natT, PV $ Bound 0);
        val rhs = PV $ gen_rhs qh_level [] 2 [];
      in mk_thm (Logic.mk_equals (lhs, rhs)) end;
    fun qh_X () =
      let
        val XV = Var ((vname ^ "_X", 0), natT);
        val lhs = qhC $ Abs ("u", natT, XV);
        val rhs = gen_rhs qh_level [XV] 2 [];
      in mk_thm (Logic.mk_equals (lhs, rhs)) end;
    fun qh2_fam () =
      let
        val P1 = Var ((vname ^ "_P", 0), fT);
        val P2 = Var ((vname ^ "_P", 0), natT --> fT);
        val (body, rhs) =
          (case rand 3 of
            0 => (P1 $ Bound 1, P1 $ gen_rhs qh_level [] 2 [])
          | 1 => (P1 $ Bound 0, P1 $ gen_rhs qh_level [] 2 [])
          | _ => (P2 $ Bound 0 $ Bound 1,
                  P2 $ gen_rhs qh_level [] 2 [] $ gen_rhs qh_level [] 2 []));
        val lhs = qh2C $ Abs ("u1", natT, Abs ("u2", natT, body));
      in mk_thm (Logic.mk_equals (lhs, rhs)) end;
    (*family-4 proper: the binding is GUARANTEED to land under a new binder on the
      right, so material taken from under contextual binders must come out lifted.
      Termination: head level 6 outranks qh and the binary symbol; XV placed once.*)
    fun fam4 () =
      let
        val XV = Var ((vname ^ "_X", 0), natT);
        val lhs = f5C $ XV;
        val rhs = qhC $ Abs ("w", natT, #1 (pick binary) $ XV $ Bound 0);
      in mk_thm (Logic.mk_equals (lhs, rhs)) end;
    (*termination: the qh consumed from the matched instance outranks everything
      the right-hand side adds, and XV is placed at most once*)
    fun rep2 () =
      let
        val XV = Var ((vname ^ "_X", 0), natT);
        val (bh, lvl) = pick binary;
        val (uh, _) = pick (below qh_level unary);
        val lhs = bh $ XV $ (qhC $ Abs ("u", natT, uh $ XV));
        val rhs = gen_rhs lvl [XV] 2 [];
      in mk_thm (Logic.mk_equals (lhs, rhs)) end;
    fun first_order () =
      let
        val (hd_sym, lvl, args) =
          if rand 2 = 0 then
            let val (s, l) = pick unary in (s, l, [arg 1]) end
          else
            let val (s, l) = pick binary in (s, l, [arg 1, arg 2]) end;
        val lhs = Term.list_comb (hd_sym, args);
        val holes = filter Term.is_Var args;
        (*NO extra-variable rules here: `Conv.rewr_conv' renames schematics apart
          with `Thm.incr_indexes' and `Pattern.match_rew' does not, so the two layers
          legitimately disagree on them and the cross-layer check could not run.
          They are covered by the hand-written corpus (C27, C28) instead.*)
        val rhs = gen_rhs lvl holes 2 [];
      in mk_thm (Logic.mk_equals (lhs, rhs)) end;
  in
    (case rand 16 of
      0 => bare () | 1 => bare ()
    | 2 => qh_P () | 3 => qh_P ()
    | 4 => qh_X ()
    | 5 => qh2_fam () | 6 => qh2_fam ()
    | 7 => rep2 ()
    | 8 => fam4 ()
    | _ => first_order ())
  end;

(*LHS a bare unary symbol (so it can match in function position); RHS an Abs.
  Termination: body uses only symbols of level below the head's, and Bound 0 is
  passed as a hole so gen_rhs places it at most once -- nothing is duplicated.
  Without this family no generated rule has an Abs-headed right-hand side that can
  land in function position, and the reassembly-manufactured redexes the module
  must contract are never exercised.*)
fun gen_rule_beta _ =
  let val (s, lvl) = pick (filter (fn (_, l) => l >= 2) unary)
  in mk_thm (Logic.mk_equals (s, Abs ("x", natT, gen_rhs lvl [Bound 0] 2 []))) end;
fun gen_rule2 i = if rand 4 = 0 then gen_rule_beta i else gen_rule i;
\<close>

ML \<open>
fun rewr_skel_unguarded rule ct = (Conv.rewr_conv rule ct, Thm.term_of (Thm.rhs_of rule));

val opts: Merely_Rewrite.options =
  SOME {size_check = SOME true, step_limit = SOME (SOME 20000),
        growth_factor = NONE, growth_offset = NONE};

fun outcome res =
  (case res of
    Exn.Res t => "OK " ^ dump t
  | Exn.Exn (Merely_Rewrite.DIVERGES (Merely_Rewrite.Step_Limit _, _)) => "DIVERGES Step_Limit"
  | Exn.Exn (Merely_Rewrite.DIVERGES (Merely_Rewrite.Growth _, _)) => "DIVERGES Growth"
  | Exn.Exn e => "EXN " ^ Runtime.exn_message e);

(*O1, the beta-normal-fixpoint invariant: an output the module reports as OK must
  contain no beta redex, and no rule of the net may still fire anywhere in it
  (binders opened as fresh frees).  The only oracle that catches a defect made
  identically in both layers, and the only one usable on loose-Bound terms -- but
  it is dead unless the corpus contains `gen_rule_beta' rules.

  The opener is a plain `subst_bound', which shifts the OTHER loose Bounds down by
  one -- sound for THIS corpus only because no generated rule contains a loose
  Bound at all (`gen_rhs' is called with bs = [] for rules and its binder branch is
  dead), so a uniform shift cannot change what fires.  Re-check before reusing the
  oracle on a rule family with concrete loose Bounds in left-hand sides.*)
fun o1_violation net bvs0 t0 =
  let
    fun has_redex (Abs _ $ _) = true
      | has_redex (t $ u) = has_redex t orelse has_redex u
      | has_redex (Abs (_, _, b)) = has_redex b
      | has_redex _ = false;
    (*binders are THREADED as bvs, exactly as the engine does after A3 -- no
      opening as fresh frees, so the oracle sees the same terms the engine saw*)
    fun still_fires bvs t =
      (case Merely_Rewrite.rewrs_net_term net ctxt0 bvs t of
         NONE => false
       | SOME t' => not (t aconv t'))
      orelse
      (case t of
         u $ v => still_fires bvs u orelse still_fires bvs v
       | Abs (a, T, b) => still_fires ((a, T) :: bvs) b
       | _ => false);
  in has_redex t0 orelse still_fires bvs0 t0 end;

fun counted mk =
  let
    val n = Unsynchronized.ref 0;
    fun bump f ctxt ct = (n := ! n + 1; f ctxt ct);
  in (mk bump, n) end;

fun one_round () =
  let
    val nrules = 3 + rand 6;
    val rules = map gen_rule2 (1 upto nrules);
    val net = Merely_Rewrite.make_rules rules;
    val input = gen_term (4 + rand 3) [];
    val ct = Thm.cterm_of ctxt0 input;

    val (cv_ref, n_ref) = counted (fn bump =>
      Merely_Rewrite.bottom_fixpoint_conv_mode Merely_Rewrite.Reference opts
        (bump (Merely_Rewrite.rewrs_net_conv net)) ctxt0);
    val (cv_no, n_no) = counted (fn bump =>
      Merely_Rewrite.bottom_fixpoint_conv_mode Merely_Rewrite.No_Skeleton opts
        (bump (Merely_Rewrite.rewrs_net_conv net)) ctxt0);
    val (cv_sk, n_sk) = counted (fn bump =>
      Merely_Rewrite.bottom_fixpoint_skel_conv opts
        (bump (Merely_Rewrite.rewrs_net_skel_conv net)) ctxt0);
    val rw_ref =
      Merely_Rewrite.bottom_fixpoint_term_mode Merely_Rewrite.Reference opts
        (Merely_Rewrite.rewrs_net_term net) ctxt0 [];
    val rw_no =
      Merely_Rewrite.bottom_fixpoint_term_mode Merely_Rewrite.No_Skeleton opts
        (Merely_Rewrite.rewrs_net_term net) ctxt0 [];
    val rw_sk =
      Merely_Rewrite.bottom_fixpoint_skel_term opts
        (Merely_Rewrite.rewrs_net_skel_term net) ctxt0 [];
    val cv_un =
      Merely_Rewrite.bottom_fixpoint_skel_conv opts
        (Merely_Rewrite.single_step_rewrite_skel_conv
          (fn ctxt' => rewr_skel_unguarded o Thm.transfer' ctxt') net) ctxt0;

    fun run cv = outcome (Exn.capture (fn () => Thm.term_of (Thm.rhs_of (cv ct))) ());
    fun run_t rw = outcome (Exn.capture (fn () => rw input) ());
    val o_ref = run cv_ref;
    val o_no = run cv_no;
    val o_sk = run cv_sk;
    val o_un = run cv_un;
    val t_ref = run_t rw_ref;
    val t_no = run_t rw_no;
    val sk_res = Exn.capture (fn () => rw_sk input) ();
    val t_sk = outcome sk_res;
  in
    {rules = rules, input = input,
     agree_fork = o_ref = o_no, agree_prune = o_no = o_sk, agree_unguarded = o_sk = o_un,
     agree_tfork = t_ref = t_no, agree_tprune = t_no = t_sk, agree_cross = o_sk = t_sk,
     diverged = String.isPrefix "DIVERGES" o_sk, broken = String.isPrefix "EXN" o_sk,
     pruned = ! n_sk < ! n_no, visits = (! n_ref, ! n_no, ! n_sk),
     rewrote = (o_sk <> "OK " ^ dump input),
     o1 = (case sk_res of Exn.Res t => o1_violation net [] t | _ => false),
     texts = (o_ref, o_no, o_sk, o_un), ttexts = (t_ref, t_no, t_sk)}
  end;

fun fuzz start n =
  let
    val bad = Unsynchronized.ref ([]: (int * string) list);
    val o1bad = Unsynchronized.ref ([]: (int * string) list);
    val stats = Unsynchronized.ref (0, 0, 0, 0, 0);   (*pruned, diverged, broken, unguarded-differs, changed*)
    fun step i =
      let
        val _ = srand (start + i);
        val r = one_round ();
        val (a, b, c, d, e) = ! stats;
        val _ = stats :=
          (a + (if #pruned r then 1 else 0), b + (if #diverged r then 1 else 0),
           c + (if #broken r then 1 else 0), d + (if #agree_unguarded r then 0 else 1),
           e + (if #rewrote r then 1 else 0));
        val (t_ref, t_no, t_sk, _) = #texts r;
        fun record () =
          (start + i,
            cat_lines
              (["seed " ^ string_of_int (start + i),
                "input " ^ Syntax.string_of_term pctxt (#input r)] @
               map (fn th => "rule  " ^ Thm.string_of_thm ctxt0 th) (#rules r) @
               ["conv ref " ^ t_ref, "conv no  " ^ t_no, "conv skl " ^ t_sk,
                "term ref " ^ #1 (#ttexts r), "term no  " ^ #2 (#ttexts r),
                "term skl " ^ #3 (#ttexts r)]));
        val _ = if #o1 r then o1bad := record () :: ! o1bad else ();
      in
        if #agree_fork r andalso #agree_prune r andalso #agree_tfork r
           andalso #agree_tprune r andalso #agree_cross r then ()
        else bad := record () :: ! bad
      end;
    val _ = List.app step (1 upto n);
    val (a, b, c, d, e) = ! stats;
  in
    writeln
      ("fuzz: " ^ string_of_int n ^ " rounds from seed " ^ string_of_int start ^
       "\n  rounds in which the output differs from the input: " ^ string_of_int e ^
       "\n  rounds where pruning actually fired: " ^ string_of_int a ^
       "\n  rounds that hit a divergence guard:  " ^ string_of_int b ^
       "\n  rounds that raised something else:   " ^ string_of_int c ^
       "\n  rounds where the UNGUARDED skeleton disagrees: " ^ string_of_int d ^
       "\n  O1 beta-normal-fixpoint violations:  " ^ string_of_int (length (! o1bad)) ^
       "\n  MISMATCHES: " ^ string_of_int (length (! bad)));
    if null (! bad) andalso null (! o1bad) then ()
    else error (cat_lines (map #2 (take 3 (! bad)) @ map #2 (take 3 (! o1bad))))
  end;
\<close>

ML \<open>
(*Loose-Bound fuzzing: the conv layer cannot be handed these at all, so only the
  three term-layer variants are compared -- entered through the bvs-taking mode
  entry with a six-entry all-nat `bvs' -- and they must still agree literally.
  Loose indices are injected at random nat-typed positions (argument positions
  and nat leaves, never a function position or an `Abs' argument): the inputs
  stay well-typed relative to `bvs', because under the garbage-in contract of
  `rewrite_term_bvs' an ill-typed input is out of corpus scope.*)
val bvs6 = map (fn i => ("z" ^ string_of_int i, natT)) (0 upto 5);
(*`nat_pos' tracks whether the current position is nat-typed: only there may a
  subterm be replaced by a loose `Bound'.  Function positions and `Abs' arguments
  are recursed into but never replaced -- in this grammar every non-`Abs'
  argument position and every binder body is nat, so the flag is exact.*)
fun loosen nat_pos t =
  (case t of
    u $ v =>
      loosen false u $
      (case v of
        Abs _ => loosen false v
      | _ => if rand 4 = 0 then Bound (rand 6) else loosen true v)
  | Abs (a, T, b) => Abs (a, T, loosen true b)
  | _ => if nat_pos andalso rand 5 = 0 then Bound (rand 6) else t);

fun fuzz_loose start n =
  let
    val bad = Unsynchronized.ref ([]: string list);
    val o1bad = Unsynchronized.ref ([]: string list);
    val stats = Unsynchronized.ref (0, 0);
    fun step i =
      let
        val _ = srand (start + i);
        val rules = map gen_rule2 (1 upto (3 + rand 6));
        val net = Merely_Rewrite.make_rules rules;
        val input = loosen true (gen_term (4 + rand 3) []);
        fun run mode =
          Exn.capture (fn () =>
            Merely_Rewrite.rewrite_term_mode mode opts net ctxt0 bvs6 input) ();
        val ra = run Merely_Rewrite.Reference;
        val rb = run Merely_Rewrite.No_Skeleton;
        val rc = run Merely_Rewrite.Skeleton;
        val (a, b, c) = (outcome ra, outcome rb, outcome rc);
        val (p, q) = ! stats;
        val _ = stats := (p + (if c = "OK " ^ dump input then 0 else 1),
                          q + (if String.isPrefix "EXN" c then 1 else 0));
        fun record () =
          cat_lines (["seed " ^ string_of_int (start + i), "in  " ^ dump input] @
            map (fn th => "rule " ^ Thm.string_of_thm ctxt0 th) rules @
            ["ref " ^ a, "no  " ^ b, "skl " ^ c]);
        val _ =
          (case rc of
             Exn.Res t => if o1_violation net bvs6 t then o1bad := record () :: ! o1bad else ()
           | _ => ());
      in
        if a = b andalso b = c then () else bad := record () :: ! bad
      end;
    val _ = List.app step (1 upto n);
    val (p, q) = ! stats;
  in
    writeln ("fuzz_loose: " ^ string_of_int n ^ " rounds from seed " ^ string_of_int start ^
      "\n  rounds in which the output differs from the input: " ^ string_of_int p ^
      "\n  rounds that raised something: " ^ string_of_int q ^
      "\n  O1 beta-normal-fixpoint violations: " ^ string_of_int (length (! o1bad)) ^
      "\n  MISMATCHES: " ^ string_of_int (length (! bad)));
    if null (! bad) andalso null (! o1bad) then ()
    else error (cat_lines (take 3 (! bad) @ take 3 (! o1bad)))
  end;
\<close>

ML \<open>fuzz_loose 31337 3000\<close>
ML \<open>fuzz_loose 424242 3000\<close>

ML \<open>fuzz 1000 3000\<close>
ML \<open>fuzz 500000 3000\<close>
ML \<open>fuzz 90000000 3000\<close>
ML \<open>fuzz 7654321 3000\<close>

end
