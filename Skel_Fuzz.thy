theory Skel_Fuzz
  imports Main
begin

ML_file \<open>library/improved_net.ML\<close>
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
  qh :: "(nat \<Rightarrow> nat) \<Rightarrow> nat"

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
val unary = [(\<^term>\<open>f0\<close>, 1), (\<^term>\<open>f1\<close>, 2), (\<^term>\<open>f2\<close>, 3), (\<^term>\<open>f3\<close>, 4)];
val binary = [(\<^term>\<open>g0\<close>, 2), (\<^term>\<open>g1\<close>, 3), (\<^term>\<open>g2\<close>, 4)];
val qhC = \<^term>\<open>qh\<close>;
val qh_level = 5;

fun below lvl xs = filter (fn (_, l) => l < lvl) xs;

(*random term.  `bs' is the list of de Bruijn indices in scope.*)
fun gen_term d bs =
  if d <= 0 orelse rand 4 = 0 then
    (if null bs orelse rand 2 = 0 then #1 (pick nullary) else Bound (pick bs))
  else
    (case rand 6 of
      0 => #1 (pick unary) $ gen_term (d - 1) bs
    | 1 => #1 (pick unary) $ gen_term (d - 1) bs
    | 2 => #1 (pick binary) $ gen_term (d - 1) bs $ gen_term (d - 1) bs
    | 3 => #1 (pick binary) $ gen_term (d - 1) bs $ gen_term (d - 1) bs
    | 4 => qhC $ Abs ("u", natT, gen_term (d - 1) (0 :: map (fn i => i + 1) bs))
    | _ => (*an explicit beta-redex, which the module must NOT contract on its own*)
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

(*a random rule.  Two families: first-order, and the higher-order pattern
  `qh (%u. ?P u)', whose right-hand side applies ?P to new material and therefore
  goes through the deep beta of Conv.rewr_conv.*)
fun gen_rule i =
  let
    val vname = "x" ^ string_of_int i;
    fun v k = Var ((vname ^ "_" ^ string_of_int k, 0), natT);
    fun arg k = if rand 4 > 0 then v k else gen_term 1 [];
    val fT = natT --> natT;
  in
    if rand 8 = 0 then
      (*a rule whose left-hand side is a bare schematic of FUNCTION type: the only
        kind of rule that can match a leftover schematic, and therefore the only
        kind that can tell whether the extra-variable guard in `rewr_skel_conv' is
        doing its job.  It rewrites to the lowest level symbol, so it terminates.*)
      mk_thm (Logic.mk_equals (Var ((vname ^ "_F", 0), fT), #1 (hd unary)))
    else if rand 5 = 0 then
      let
        val PV = Var ((vname ^ "_P", 0), natT --> natT);
        val lhs = qhC $ Abs ("u", natT, PV $ Bound 0);
        val rhs = PV $ gen_rhs qh_level [] 2 [];
      in mk_thm (Logic.mk_equals (lhs, rhs)) end
    else
      let
        val (hd_sym, lvl, args) =
          if rand 2 = 0 then
            let val (s, l) = pick unary in (s, l, [arg 1]) end
          else
            let val (s, l) = pick binary in (s, l, [arg 1, arg 2]) end;
        val lhs = Term.list_comb (hd_sym, args);
        val holes = filter Term.is_Var args;
        (*with some probability leave a schematic on the right that is not on the
          left -- the family `Raw_Simplifier' rejects and this module accepts*)
        (*NO extra-variable rules here: `Conv.rewr_conv' renames schematics apart
          with `Thm.incr_indexes' and `Pattern.match_rew' does not, so the two layers
          legitimately disagree on them and the cross-layer check could not run.
          They are covered by the hand-written corpus (C27, C28) instead.*)
        val holes' = holes;
        val rhs = gen_rhs lvl holes' 2 [];
      in mk_thm (Logic.mk_equals (lhs, rhs)) end
  end;
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

fun counted mk =
  let
    val n = Unsynchronized.ref 0;
    fun bump f ctxt ct = (n := ! n + 1; f ctxt ct);
  in (mk bump, n) end;

fun one_round () =
  let
    val nrules = 3 + rand 6;
    val rules = map gen_rule (1 upto nrules);
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
        (Merely_Rewrite.rewrs_net_term net) ctxt0;
    val rw_no =
      Merely_Rewrite.bottom_fixpoint_term_mode Merely_Rewrite.No_Skeleton opts
        (Merely_Rewrite.rewrs_net_term net) ctxt0;
    val rw_sk =
      Merely_Rewrite.bottom_fixpoint_skel_term opts
        (Merely_Rewrite.rewrs_net_skel_term net) ctxt0;
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
    val t_sk = run_t rw_sk;
  in
    {rules = rules, input = input,
     agree_fork = o_ref = o_no, agree_prune = o_no = o_sk, agree_unguarded = o_sk = o_un,
     agree_tfork = t_ref = t_no, agree_tprune = t_no = t_sk, agree_cross = o_sk = t_sk,
     diverged = String.isPrefix "DIVERGES" o_sk, broken = String.isPrefix "EXN" o_sk,
     pruned = ! n_sk < ! n_no, visits = (! n_ref, ! n_no, ! n_sk),
     rewrote = (o_sk <> "OK " ^ dump input),
     texts = (o_ref, o_no, o_sk, o_un), ttexts = (t_ref, t_no, t_sk)}
  end;

fun fuzz start n =
  let
    val bad = Unsynchronized.ref ([]: (int * string) list);
    val stats = Unsynchronized.ref (0, 0, 0, 0, 0);   (*pruned, diverged, broken, unguarded-differs, rewrote*)
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
      in
        if #agree_fork r andalso #agree_prune r andalso #agree_tfork r
           andalso #agree_tprune r andalso #agree_cross r then ()
        else
          bad := (start + i,
            cat_lines
              (["seed " ^ string_of_int (start + i),
                "input " ^ Syntax.string_of_term pctxt (#input r)] @
               map (fn th => "rule  " ^ Thm.string_of_thm ctxt0 th) (#rules r) @
               ["conv ref " ^ t_ref, "conv no  " ^ t_no, "conv skl " ^ t_sk,
                "term ref " ^ #1 (#ttexts r), "term no  " ^ #2 (#ttexts r),
                "term skl " ^ #3 (#ttexts r)])) :: ! bad
      end;
    val _ = List.app step (1 upto n);
    val (a, b, c, d, e) = ! stats;
  in
    writeln
      ("fuzz: " ^ string_of_int n ^ " rounds from seed " ^ string_of_int start ^
       "\n  rounds in which at least one rewrite happened: " ^ string_of_int e ^
       "\n  rounds where pruning actually fired: " ^ string_of_int a ^
       "\n  rounds that hit a divergence guard:  " ^ string_of_int b ^
       "\n  rounds that raised something else:   " ^ string_of_int c ^
       "\n  rounds where the UNGUARDED skeleton disagrees: " ^ string_of_int d ^
       "\n  MISMATCHES: " ^ string_of_int (length (! bad)));
    if null (! bad) then ()
    else error (cat_lines (map #2 (take 3 (! bad))))
  end;
\<close>

ML \<open>
(*Loose-Bound fuzzing: the conv layer cannot be handed these at all, so only the
  three term-layer variants are compared -- and they must still agree literally.
  Loose indices are injected at random leaf positions of an otherwise ordinary
  random term.*)
fun loosen d t =
  (case t of
    u $ v => (if rand 4 = 0 then Bound (rand 6) else loosen d u) $ loosen d v
  | Abs (a, T, u) => Abs (a, T, loosen d u)
  | _ => if rand 5 = 0 then Bound (rand 6) else t);

fun fuzz_loose start n =
  let
    val bad = Unsynchronized.ref ([]: string list);
    val stats = Unsynchronized.ref (0, 0);
    fun step i =
      let
        val _ = srand (start + i);
        val rules = map gen_rule (1 upto (3 + rand 6));
        val net = Merely_Rewrite.make_rules rules;
        val input = loosen 0 (gen_term (4 + rand 3) []);
        fun run mode =
          outcome (Exn.capture (fn () =>
            Merely_Rewrite.rewrite_term_mode mode opts net ctxt0 input) ());
        val a = run Merely_Rewrite.Reference;
        val b = run Merely_Rewrite.No_Skeleton;
        val c = run Merely_Rewrite.Skeleton;
        val (p, q) = ! stats;
        val _ = stats := (p + (if c = "OK " ^ dump input then 0 else 1),
                          q + (if String.isPrefix "EXN" c then 1 else 0));
      in
        if a = b andalso b = c then ()
        else bad := cat_lines (["seed " ^ string_of_int (start + i), "in  " ^ dump input] @
               map (fn th => "rule " ^ Thm.string_of_thm ctxt0 th) rules @
               ["ref " ^ a, "no  " ^ b, "skl " ^ c]) :: ! bad
      end;
    val _ = List.app step (1 upto n);
    val (p, q) = ! stats;
  in
    writeln ("fuzz_loose: " ^ string_of_int n ^ " rounds from seed " ^ string_of_int start ^
      "\n  rounds in which at least one rewrite happened: " ^ string_of_int p ^
      "\n  rounds that raised something: " ^ string_of_int q ^
      "\n  MISMATCHES: " ^ string_of_int (length (! bad)));
    if null (! bad) then () else error (cat_lines (take 3 (! bad)))
  end;
\<close>

ML \<open>fuzz_loose 31337 3000\<close>
ML \<open>fuzz_loose 424242 3000\<close>

ML \<open>fuzz 1000 3000\<close>
ML \<open>fuzz 500000 3000\<close>
ML \<open>fuzz 90000000 3000\<close>
ML \<open>fuzz 7654321 3000\<close>

end
