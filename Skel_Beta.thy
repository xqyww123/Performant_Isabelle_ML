theory Skel_Beta
  imports Main
begin

ML_file \<open>library/improved_net.ML\<close>
ML_file \<open>library/merely_rewrite.ML\<close>

text \<open>
  Positive controls and accounting gates for eager beta contraction
  (MERELY_REWRITE_EAGER_BETA_PLAN.md sections 8.3 and 8.4b).  Every case in this
  file was RED on the module before the change; none of the expectations is
  satisfiable by the old "a beta redex is not a rewrite step" behaviour.

  Comparisons are on structure dumps / `aconv', never on `Syntax.string_of_term'
  output -- the printing chain beta-normalises and cannot be told not to.
\<close>

axiomatization
  aa :: nat and bb :: nat and cc :: nat and
  ff :: "nat \<Rightarrow> nat" and gg :: "nat \<Rightarrow> nat" and
  hh :: "nat \<Rightarrow> nat" and hh2 :: "nat \<Rightarrow> nat" and
  pp :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where ff_2 : "ff 2 \<equiv> 3"
  and hh_def : "hh \<equiv> \<lambda>x. gg (ff x)"
  and hh2_def : "hh2 \<equiv> \<lambda>x. pp x x"
  and pp_ab : "pp aa bb \<equiv> cc"

ML \<open>
val ctxt0 = \<^context>;
val natT = \<^typ>\<open>nat\<close>;
val aa = \<^term>\<open>aa\<close>; val bb = \<^term>\<open>bb\<close>; val cc = \<^term>\<open>cc\<close>;
val ff = \<^term>\<open>ff\<close>; val gg = \<^term>\<open>gg\<close>; val hh = \<^term>\<open>hh\<close>;
val hh2 = \<^term>\<open>hh2\<close>; val pp = \<^term>\<open>pp\<close>;

fun dumpT (Type (n, Ts)) = "T" ^ n ^ "[" ^ implode_space (map dumpT Ts) ^ "]"
  | dumpT (TFree (n, S)) = "F" ^ n ^ "{" ^ implode_space S ^ "}"
  | dumpT (TVar ((n, i), S)) = "V" ^ n ^ string_of_int i ^ "{" ^ implode_space S ^ "}";
fun dump (Const (c, T)) = "c<" ^ c ^ ":" ^ dumpT T ^ ">"
  | dump (Free (x, T)) = "f<" ^ x ^ ":" ^ dumpT T ^ ">"
  | dump (Var ((x, i), T)) = "v<" ^ x ^ string_of_int i ^ ":" ^ dumpT T ^ ">"
  | dump (Bound i) = "b<" ^ string_of_int i ^ ">"
  | dump (Abs (x, T, t)) = "A<" ^ x ^ ":" ^ dumpT T ^ ">(" ^ dump t ^ ")"
  | dump (t $ u) = "(" ^ dump t ^ " . " ^ dump u ^ ")";

val failures = Unsynchronized.ref ([]: string list);
(*failures are printed the moment they happen: on the unmodified module the Omega
  block at the end of this file kills the whole theory (ML stack exhaustion, not a
  catchable exception), and the reds before it must still be visible*)
fun chk name ok =
  if ok then () else (writeln ("FAILED: " ^ name); failures := name :: ! failures);

fun outcome f =
  (case Exn.capture f () of
    Exn.Res t => "OK " ^ dump t
  | Exn.Exn (Merely_Rewrite.DIVERGES (Merely_Rewrite.Step_Limit _, _)) => "DIVERGES Step_Limit"
  | Exn.Exn (Merely_Rewrite.DIVERGES (Merely_Rewrite.Growth _, _)) => "DIVERGES Growth"
  | Exn.Exn e => "EXN " ^ Runtime.exn_message e);

val modes =
  [("ref", Merely_Rewrite.Reference),
   ("no", Merely_Rewrite.No_Skeleton),
   ("skl", Merely_Rewrite.Skeleton)];

(*a case run at the term layer, all three modes*)
fun three label opts net input expect =
  List.app (fn (mn, m) =>
    let val got = outcome (fn () => Merely_Rewrite.rewrite_term_mode m opts net ctxt0 input)
    in chk (label ^ " term/" ^ mn ^ ": got " ^ got ^ ", want " ^ expect) (got = expect) end)
    modes;

(*a case run at both layers, all three modes each: six accounting points, one per
  combination of beta position, layer and mode -- the requirement of section 8.4b*)
fun six label opts net input expect =
  (three label opts net input expect;
   List.app (fn (mn, m) =>
     let
       val got = outcome (fn () =>
         Thm.term_of (Thm.rhs_of
           (Merely_Rewrite.rewrite_conv_mode m opts net ctxt0 (Thm.cterm_of ctxt0 input))))
     in chk (label ^ " conv/" ^ mn ^ ": got " ^ got ^ ", want " ^ expect) (got = expect) end)
     modes);

fun limit n : Merely_Rewrite.options =
  SOME {size_check = SOME true, step_limit = SOME (SOME n),
        growth_factor = NONE, growth_offset = NONE};
fun budget k : Merely_Rewrite.options =
  SOME {size_check = SOME true, step_limit = NONE,
        growth_factor = SOME 0, growth_offset = SOME k};
val dflt = Merely_Rewrite.default_options;

(*all rule sets are built HERE, in the same command context as `ctxt0': a net
  built in a later ML block carries a later theory stage and `Thm.transfer''
  inside the conv layer rejects it ("Cannot transfer: not a super theory")*)
val no_rules = Merely_Rewrite.empty_rules;
val r_ff = Merely_Rewrite.make_rules [@{thm ff_2}];
val r_hh = Merely_Rewrite.make_rules [@{thm ff_2}, @{thm hh_def}];
val r_ppab = Merely_Rewrite.make_rules [@{thm pp_ab}];
val r_hhonly = Merely_Rewrite.make_rules [@{thm hh_def}];
val r_hh2 = Merely_Rewrite.make_rules [@{thm hh2_def}];
\<close>

section \<open>Positive controls (plan section 8.3)\<close>

ML \<open>
val two = \<^term>\<open>2::nat\<close>;
val three_n = \<^term>\<open>3::nat\<close>;

(*1: a redex the input arrives with hides `ff 2' from the traversal*)
val _ = six "P1 (%x. gg (ff x)) 2 + ff2" dflt r_ff
          (Abs ("x", natT, gg $ (ff $ Bound 0)) $ two)
          ("OK " ^ dump (gg $ three_n));

(*2: the traversal manufactures the redex itself -- `hh' rewrites to an Abs that
  lands in function position (the section 2.3 shape)*)
val _ = six "P2 hh 2 + hh_def + ff2" dflt r_hh
          (hh $ two)
          ("OK " ^ dump (gg $ three_n));

(*3: an empty rule set is NOT the identity any more -- consecutive spine redexes
  are contracted recursively*)
val _ = six "P3 (%x y. pp x y) aa bb, empty rules" dflt no_rules
          (Abs ("x", natT, Abs ("y", natT, pp $ Bound 1 $ Bound 0)) $ aa $ bb)
          ("OK " ^ dump (pp $ aa $ bb));

(*4: term layer, loose Bound in the redex body: `subst_bound' must renumber the
  surviving loose Bound down by one -- hand-computed target*)
val _ = three "P4 (%x. pp (ff B1) x) 2 + ff2" dflt r_ff
          (Abs ("x", natT, pp $ (ff $ Bound 1) $ Bound 0) $ two)
          ("OK " ^ dump (pp $ (ff $ Bound 0) $ two));

(*5: order probe: if the `subst_bound' arguments were swapped the output differs*)
val _ = three "P5 (%x. pp x B1) aa + pp_ab" dflt r_ppab
          (Abs ("x", natT, pp $ Bound 0 $ Bound 1) $ aa)
          ("OK " ^ dump (pp $ aa $ Bound 0));

(*6: beta contraction is charged against the growth budget: an argument-duplicating
  tower with NO rules at all must trip the Growth guard, in both layers*)
val bomb = funpow 14 (fn t => Abs ("x", natT, pp $ Bound 0 $ Bound 0) $ t) aa;
val _ = six "P6 duplication tower depth 14, empty rules" dflt no_rules
          bomb "DIVERGES Growth";

\<close>

section \<open>A caller-supplied step returning a non-equation (plan section 5.7.1)\<close>

ML \<open>
(*The step below returns `aa = aa' -- a perfectly valid theorem that is not a
  meta-equation.  Before the change `Thm.rhs_of' raised inside the traversal and
  `else_conv' swallowed it as "no rewrite here"; now it must surface as `Fail'
  (anything in THM/CTERM/TERM/TYPE would be swallowed again).*)
val bad_step = Skip_Proof.make_thm \<^theory> (\<^prop>\<open>aa = aa\<close>);
val r = Exn.capture (fn () =>
  Merely_Rewrite.bottom_fixpoint_conv Merely_Rewrite.default_options
    (fn _ => fn ct =>
      if Thm.term_of ct aconv aa then bad_step else raise CTERM ("no step", [ct]))
    ctxt0 (Thm.cterm_of ctxt0 (ff $ aa))) ();
(*the contract says "with the offending theorem": the payload must name the case
  and carry the theorem's text (checked on a single token -- the printed theorem
  carries PIDE markup between tokens)*)
val _ = chk "P8 non-equation step must raise Fail carrying the theorem"
          (case r of
             Exn.Exn (Fail msg) =>
               String.isSubstring "step returned a non-equation" msg andalso
               String.isSubstring "aa" msg
           | _ => false);
\<close>

section \<open>Accounting gates DC1-DC7 (plan section 8.4b)\<close>

ML \<open>
(*DC1-DC3: a chain of 5000 identity redexes.  Every contraction is charged exactly
  one step on the shared budget: 5000 steps pass a limit of 6000 and the default,
  and trip a limit of 1000.*)
val chain = funpow 5000 (fn t => Abs ("x", natT, Bound 0) $ t) aa;
val _ = six "DC1 identity chain, default options" dflt no_rules chain ("OK " ^ dump aa);
val _ = six "DC2 identity chain, limit 1000" (limit 1000) no_rules chain "DIVERGES Step_Limit";
val _ = six "DC3 identity chain, limit 6000" (limit 6000) no_rules chain ("OK " ^ dump aa);

(*DC4: a discarding contraction SHRINKS the term; with a growth budget of 0/0 the
  negative delta must pass (charging size(residue) instead of the delta would trip)*)
val big = funpow 10 (fn t => ff $ t) aa;
val _ = six "DC4 discarding beta, budget 0/0" (budget 0) no_rules
          (Abs ("z", natT, aa) $ big) ("OK " ^ dump aa);

(*DC5: a duplicating contraction grows the term past a 0/0 budget.  Note
  `Term.size_of_term' counts atoms and binders but NOT application nodes, so the
  delta of `(%x. pp x x) $ t' is size(t) - 3 -- the argument must be big enough*)
val _ = six "DC5 duplicating beta, budget 0/0" (budget 0) no_rules
          (Abs ("x", natT, pp $ Bound 0 $ Bound 0) $ big)
          "DIVERGES Growth";

(*DC6/DC7: the redexes above all arrive with the input and are caught at the
  DESCENT position; a mutant that forgets the guards only at the STEP position
  still passes DC1-DC5.  These two go through rule steps whose Abs right-hand side
  lands in function position, so the contraction happens at the step position.*)

(*DC6: 50 nested `hh', each costing one rule step plus one beta step = 100 steps;
  the unmodified module took 50 and PASSED this limit*)
val hh_tower = funpow 50 (fn t => hh $ t) aa;
val _ = six "DC6 hh tower depth 50, limit 60" (limit 60) r_hhonly
          hh_tower "DIVERGES Step_Limit";

(*DC7: the rule step's own growth (size of the Abs right-hand side minus 1) fits
  the budget exactly; only the duplicating beta at the step position exceeds it*)
val dc7_off = Term.size_of_term (Abs ("x", natT, pp $ Bound 0 $ Bound 0)) - 1;
val _ = chk "DC7 precondition: rule-step delta is 3" (dc7_off = 3);
val _ = six "DC7 hh2 duplication, budget 0/rule-delta" (budget dc7_off) r_hh2
          (hh2 $ big) "DIVERGES Growth";
\<close>

section \<open>Ill-typed pathological inputs (term layer only; plan sections 5.1 and 6.4)\<close>

ML \<open>
(*Kept LAST on purpose: on the module before the change this block did not fail
  cleanly -- it exhausted the ML stack and killed the whole theory.  Now the pure
  beta loop is cut off by the step limit, and a redex that discards its argument
  terminates immediately (contract-before-descend), which is why `Thm.cterm_of'
  never sees these terms: they are not typeable and stay at the term layer.*)
val om = Abs ("x", natT, Bound 0 $ Bound 0);
val _ = three "P7a Omega, empty rules" (limit 20000) no_rules
          (om $ om) "DIVERGES Step_Limit";
val _ = three "P7b (%z. aa) Omega, empty rules" (limit 20000) no_rules
          (Abs ("z", natT, aa) $ (om $ om)) ("OK " ^ dump aa);
\<close>

section \<open>Verdict\<close>

ML \<open>
if null (! failures) then writeln "ALL BETA CONTROLS PASS"
else error (cat_lines ("BETA CONTROL FAILURES:" :: rev (! failures)))
\<close>

end
