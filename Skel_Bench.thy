theory Skel_Bench
  imports Main
begin

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/pattern.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>

axiomatization
  aa :: nat and
  ff :: "nat \<Rightarrow> nat" and gg :: "nat \<Rightarrow> nat" and hh :: "nat \<Rightarrow> nat" and
  mk :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
  m0 :: "nat \<Rightarrow> nat" and m1 :: "nat \<Rightarrow> nat" and m2 :: "nat \<Rightarrow> nat" and
  m3 :: "nat \<Rightarrow> nat" and m4 :: "nat \<Rightarrow> nat" and m5 :: "nat \<Rightarrow> nat" and
  m6 :: "nat \<Rightarrow> nat" and m7 :: "nat \<Rightarrow> nat" and m8 :: "nat \<Rightarrow> nat"

section \<open>Harness\<close>

ML \<open>
val ctxt0 = \<^context>;
val thy0 = Proof_Context.theory_of ctxt0;
val natT = \<^typ>\<open>nat\<close>;
fun mk_thm t = Skip_Proof.make_thm thy0 t;
fun rule l r = mk_thm (Logic.mk_equals (l, r));
fun var s = Var ((s, 0), natT);

(*guards off: they are not what is being measured, and `Term.size_of_term' on every
  step would be measured instead*)
val opts = Merely_Rewrite.no_check;

fun conv_of ctxt mode net = Merely_Rewrite.rewrite_conv_mode mode opts net ctxt;

fun visits ctxt mode net ct =
  let
    val n = Unsynchronized.ref 0;
    fun bump f ctxt' ct' = (n := ! n + 1; f ctxt' ct');
    val cv =
      (case mode of
        Merely_Rewrite.Skeleton =>
          Merely_Rewrite.bottom_fixpoint_skel_conv opts
            (bump (Merely_Rewrite.rewrs_net_skel_conv net)) ctxt
      | _ =>
          Merely_Rewrite.bottom_fixpoint_conv_mode mode opts
            (bump (Merely_Rewrite.rewrs_net_conv net)) ctxt);
  in (cv ct; ! n) end;

fun ms f x =
  let val ({elapsed, ...}, _) = Timing.timing f x in Time.toReal elapsed * 1000.0 end;

fun fmt r = Real.fmt (StringCvt.FIX (SOME 1)) r;

fun quantiles ts =
  let
    val s = sort Real.compare ts;
    val n = length s;
  in (nth s 0, nth s (n div 2), nth s (n - 1)) end;

(*Time several conversions on the same input.  Everything is warmed up BEFORE any
  measurement, and the order in which the conversions are run is reversed on every
  other round, so that neither of them systematically pays for the other's cache
  effects.  Only the distribution is reported: on this machine the same measurement
  repeated back to back moves by a factor well above any two-decimal precision.*)
fun bench reps convs ct =
  let
    val _ = List.app (fn (_, cv) => (cv ct; cv ct; cv ct; ())) convs;
    val rounds =
      map (fn i =>
        let val order = if i mod 2 = 0 then convs else rev convs
        in map (fn (nm, cv) => (nm, ms cv ct)) order end)
        (1 upto reps);
    val names = map #1 convs;
  in
    map (fn nm =>
      (nm, quantiles (map_filter (fn r => AList.lookup (op =) r nm) rounds))) names
  end;

fun term_of_mode ctxt mode net =
  Merely_Rewrite.rewrite_term_mode mode opts net ctxt [];

fun row ctxt label reps net ct =
  let
    val t0 = Thm.term_of ct;
    val modes =
      [("conv reference", Merely_Rewrite.Reference),
       ("conv no-skel  ", Merely_Rewrite.No_Skeleton),
       ("conv skeleton ", Merely_Rewrite.Skeleton)];
    val tmodes =
      [("term reference", Merely_Rewrite.Reference),
       ("term no-skel  ", Merely_Rewrite.No_Skeleton),
       ("term skeleton ", Merely_Rewrite.Skeleton)];
    val convs =
      map (fn (nm, m) => (nm, fn _ => (conv_of ctxt m net ct; ()))) modes @
      map (fn (nm, m) => (nm, fn _ => (term_of_mode ctxt m net t0; ()))) tmodes;
    val results = bench reps convs ();
    val vs = map (fn (nm, m) => (nm, visits ctxt m net ct)) modes;
    fun med nm = #2 (the (AList.lookup (op =) results nm));
  in
    writeln (cat_lines
      ([label ^ "   (term size " ^ string_of_int (Term.size_of_term t0) ^
        ", " ^ string_of_int reps ^ " rounds)"] @
       map (fn (nm, (lo, md, hi)) =>
         "    " ^ nm ^ "  min " ^ fmt lo ^ "  median " ^ fmt md ^ "  max " ^ fmt hi ^ " ms" ^
         (case AList.lookup (op =) vs nm of
            SOME v => "   visits " ^ string_of_int v
          | NONE => "")) results @
       ["    conv: median no-skel / median skeleton = " ^
          fmt (med "conv no-skel  " / med "conv skeleton ") ^ "x" ^
        "    term: " ^ fmt (med "term no-skel  " / med "term skeleton ") ^ "x" ^
        "    conv skeleton / term skeleton = " ^
          fmt (med "conv skeleton " / med "term skeleton ") ^ "x"]))
  end;
\<close>

section \<open>W1: hits at the leaves -- the load the module was benchmarked on before\<close>

text \<open>
  A balanced binary tree of `mk', with `ff i' at every leaf and one rule per leaf
  value.  Every hit is at a leaf, so the subtree that gets re-scanned after a hit is
  a single node and there is nothing for a skeleton to save.  This row exists to
  show what the machinery COSTS when it cannot help.
\<close>

ML \<open>
fun num i = HOLogic.mk_number natT i;
val ffC = \<^term>\<open>ff\<close>; val ggC = \<^term>\<open>gg\<close>; val hhC = \<^term>\<open>hh\<close>;
val mkC = \<^term>\<open>mk\<close>;
fun tree m d j =
  if d <= 0 then ffC $ num (j mod m)
  else mkC $ tree m (d - 1) (2 * j) $ tree m (d - 1) (2 * j + 1);

val rules1 = map (fn i => rule (ffC $ num i) (ggC $ num i)) (0 upto 63);
val rules2 = rules1 @ map (fn i => rule (ggC $ num i) (hhC $ num i)) (0 upto 63);

val _ = row ctxt0 "W1a leaf hits, one step per leaf   " 11
          (Merely_Rewrite.make_rules rules1) (Thm.cterm_of ctxt0 (tree 64 10 0));
val _ = row ctxt0 "W1b leaf hits, two steps per leaf  " 11
          (Merely_Rewrite.make_rules rules2) (Thm.cterm_of ctxt0 (tree 64 10 0));
\<close>

section \<open>W2: a chain of hits at the root of a large term\<close>

text \<open>
  The same tree, with no redex anywhere in it, wrapped in `m0'; the rules are
  `m0 ?x == m1 ?x', ..., `m7 ?x == m8 ?x'.  Eight hits, all at the root, and after
  each one the whole tree is re-scanned by the traversal that has no skeleton.  The
  skeleton of `m1 ?x' is `m1' plus a hole, so the tree is skipped.
\<close>

ML \<open>
val ms_syms = [\<^term>\<open>m0\<close>, \<^term>\<open>m1\<close>, \<^term>\<open>m2\<close>, \<^term>\<open>m3\<close>, \<^term>\<open>m4\<close>,
               \<^term>\<open>m5\<close>, \<^term>\<open>m6\<close>, \<^term>\<open>m7\<close>, \<^term>\<open>m8\<close>];
val chain_rules =
  map (fn i => rule (nth ms_syms i $ var "x") (nth ms_syms (i + 1) $ var "x")) (0 upto 7);
val chain_net = Merely_Rewrite.make_rules chain_rules;

val _ = map (fn d =>
    row ctxt0 ("W2 root chain, tree depth " ^ string_of_int d ^ "        ") 11 chain_net
      (Thm.cterm_of ctxt0 (nth ms_syms 0 $ tree 64 d 0)))
  [6, 8, 10];
\<close>

section \<open>W3: right-nested long chain -- HOL's @ on a list\<close>

ML \<open>
val ctxt_hol = \<^context>;
val hol_rules =
  maps (Raw_Simplifier.mksimps ctxt_hol)
    (@{thms append.simps} @ @{thms list.map} @ @{thms list.size} @ @{thms rev.simps});
val hol_net = Merely_Rewrite.make_rules hol_rules;

fun nlist n = HOLogic.mk_list natT (map (fn i => HOLogic.mk_number natT i) (1 upto n));
val appf = \<^term>\<open>(@) :: nat list \<Rightarrow> nat list \<Rightarrow> nat list\<close>;
val mapf = \<^term>\<open>map :: (nat \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> nat list\<close>;
val lengthf = \<^term>\<open>length :: nat list \<Rightarrow> nat\<close>;
val revf = \<^term>\<open>rev :: nat list \<Rightarrow> nat list\<close>;

fun row_hol label ct = row ctxt_hol label 11 hol_net ct;

val _ = map (fn n =>
    row_hol ("W3a xs @ ys, n = " ^ string_of_int n ^ "              ")
      (Thm.cterm_of ctxt_hol (appf $ nlist n $ nlist n)))
  [25, 50, 100, 200];

val _ = map (fn n =>
    row_hol ("W3b map ff (xs @ ys), n = " ^ string_of_int n ^ "      ")
      (Thm.cterm_of ctxt_hol (mapf $ \<^term>\<open>ff\<close> $ (appf $ nlist n $ nlist n))))
  [25, 50, 100];

val _ = map (fn n =>
    row_hol ("W3c length (xs @ ys), n = " ^ string_of_int n ^ "      ")
      (Thm.cterm_of ctxt_hol (lengthf $ (appf $ nlist n $ nlist n))))
  [25, 50, 100];

val _ = map (fn n =>
    row_hol ("W3d rev (xs @ ys), n = " ^ string_of_int n ^ "         ")
      (Thm.cterm_of ctxt_hol (revf $ (appf $ nlist n $ nlist n))))
  [25, 50];
\<close>

section \<open>W4: a duplicating beta redex -- the load the eager contraction adds\<close>

text \<open>
  `(%x. mk x x) BIG' with one rule per leaf value of BIG.  The traversal contracts
  the redex first (call-by-name, at the descent position) and then rewrites the
  leaves of BOTH copies -- roughly twice the visits of the tree alone.  W1-W3 have
  no redex anywhere and so cannot see the beta change at all; this row is where its
  cost lives.  The other direction (a redex HIDING work, where contraction makes
  the run cheaper) is measured by the fuzz corpus, not here.
\<close>

ML \<open>
val dup_tree = tree 64 8 0;
val _ = row ctxt0 "W4 duplicating redex over W1 tree  " 11
          (Merely_Rewrite.make_rules rules1)
          (Thm.cterm_of ctxt0 (Abs ("x", natT, mkC $ Bound 0 $ Bound 0) $ dup_tree));
\<close>

(*noise-calibration marker: baseline run 2*)
end
