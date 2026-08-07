(* Directed corpus for PLPR_Pattern's handling of loose bound variables.

   Run it by hand -- like every other test here, it is deliberately NOT in ROOT:
     isabelle process_theories -l Pure -D <this directory> -O PLPR_Pattern_Test

   Failure is an `error'; success is silence (plus the summary line).  Set
   `report' to true to dump every sample instead of only the failures.

   WHAT IS BEING TESTED.  `PLPR_Pattern' is the upstream `Pure/pattern.ML'
   algorithm with `binders' initialised to `bvs' -- the caller's context binders
   count as already entered -- plus one relaxation: a contextual bound variable
   the caller declares fixed through `fixed_bounds' may stay inside a binding
   stored into `tenv', which plain upstream forbids.  Terms stored into `tenv'
   are numbered from the position where `match' was called: entry k of `bvs' is
   always `Bound k'.

   THE ORACLE.  Two independent checks, because no single Pure encoding has both
   of the properties `PLPR_Pattern' gives a contextual bound variable (it is a
   legal higher-order-pattern argument like a real binder, AND it may survive in
   an instantiation like a Free):

     (1) soundness -- oracle-free and always applicable.  Substitute the stored
         binding back into the pattern and compare literally with the object.
         A binding that points at the wrong variable fails here.
     (2) the kernel -- materialise the contextual bound variables as REAL
         lambdas and rewrite with `Conv.rewr_conv'.  This speaks for the
         structural half.  It cannot speak for the relaxation, so a sample whose
         expected instantiation keeps a contextual bound variable declares
         `Escapes' and is checked by (1) plus its declared outcome only.

   Comparison is literal on the printed structure INCLUDING binder names, never
   `aconv': alpha-equivalence hides a lost binder name.

   The printing and oracle scaffolding is taken from the throwaway probe built
   while diagnosing this (/var/tmp/plpr-probe/F3.thy).

   It loads `pattern.ML' from source rather than importing the session theory,
   for the same reason the Skel_* tests do: the matcher is then rebuilt from the
   edited source on every run, and there is no session directory to drag in. *)
theory PLPR_Pattern_Test
  imports Pure
begin

ML_file \<open>../library/pattern.ML\<close>

ML \<open>
val report = false;   (*true: dump every sample, not only the failures*)
\<close>

subsection \<open>Scaffolding\<close>

ML \<open>
val thy = @{theory};
val ctxt0 = @{context};

val a = TFree ("'a", []);
val aa = Free ("aa", a);
val ff = Free ("ff", a --> a);
val gg = Free ("gg", a --> a);
val ss = Free ("ss", a --> a);
val pp = Free ("pp", a --> a --> a);
val rr = Free ("rr", a --> a --> a --> a);
val qq = Free ("qq", (a --> a) --> a);
val s2 = Free ("s2", (a --> a) --> (a --> a) --> a);
(*a second type: without one, every type-level regression is invisible -- the
  type instantiation stays empty and `typ_match' can never disagree*)
val b = TFree ("'b", []);
val qb = Free ("qb", (b --> a) --> a);
val vx = Var (("x", 0), a);
val vy = Var (("y", 0), a);
val vP = Var (("P", 0), a --> a);
val vQ = Var (("Q", 0), a --> a --> a);

(*structure printer: binder names included, no eta-contraction, no beta-reduction*)
fun sh (Const (n, _)) = n
  | sh (Free (n, _)) = n
  | sh (Var ((n, i), _)) = "?" ^ n ^ string_of_int i
  | sh (Bound i) = "B" ^ string_of_int i
  | sh (Abs (n, _, t)) = "(%" ^ n ^ ". " ^ sh t ^ ")"
  | sh (t $ u) = "(" ^ sh t ^ " " ^ sh u ^ ")";

fun shenv tms =
  Vartab.fold (fn ((n, i), (_, u)) => fn s => s ^ "?" ^ n ^ string_of_int i ^ ":=" ^ sh u ^ " ") tms "";

(*A contextual bound variable becomes a Free of the same name -- the reading in
  which `fixed_bounds k = true' is faithful: rigid, and free to stay inside an
  instantiation.  Used to state expectations and to run the soundness check.*)
fun close bvs t = Term.subst_bounds (map Free bvs, t);

(*...and becomes a real binder -- the reading the correctness criterion is stated
  against.  Used for the kernel oracle.*)
fun wrap bvs t = fold (fn (n, T) => fn b => Abs (n, T, b)) bvs t;
fun unwrap 0 t = t
  | unwrap k (Abs (_, _, t)) = unwrap (k - 1) t
  | unwrap _ t = t;

fun mk_rule lhs rhs = Skip_Proof.make_thm thy (Logic.mk_equals (lhs, rhs));

(*The kernel oracle: does upstream, under real binders, rewrite the object?*)
fun kernel (bvs, pat, rhs, obj) =
  SOME (close bvs (unwrap (length bvs) (Thm.term_of (Thm.rhs_of
    (Conv.rewr_conv (mk_rule (wrap bvs pat) (wrap bvs rhs))
                    (Thm.cterm_of ctxt0 (wrap bvs obj)))))))
  handle CTERM _ => NONE | Pattern.MATCH => NONE | Pattern.Pattern => NONE;

(*CONTROL for the oracle: a materialisation that reads a loose `Bound' at its
  RAW index instead of `k - d', i.e. reproduces the very defect under test on the
  oracle side.  Every sample whose object mentions a contextual bound variable
  underneath a binder must see the two disagree; if they never disagree the
  oracle is not looking at anything.

  It must still close EVERY loose `Bound': leaving one behind makes
  `Thm.cterm_of' raise `TYPE', which aborts the whole run instead of reporting a
  mismatch -- and the shapes that trigger that are exactly the ones the corpus is
  meant to grow towards.  So where the raw index is out of range it falls back to
  the correct one; blindness is expressed wherever it can be.*)
fun close_blind bvs t =
  let val n = length bvs;
      fun go d (t as Bound k) =
            if k < d then t else Free (nth bvs (if k < n then k else k - d))
        | go d (Abs (x, T, b)) = Abs (x, T, go (d + 1) b)
        | go d (u $ v) = go d u $ go d v
        | go _ x = x;
  in go 0 t end;

fun kernel_blind (bvs, pat, rhs, obj) =
  SOME (Thm.term_of (Thm.rhs_of
    (Conv.rewr_conv (mk_rule (close bvs pat) (close bvs rhs))
                    (Thm.cterm_of ctxt0 (close_blind bvs obj)))))
  handle CTERM _ => NONE | Pattern.MATCH => NONE | Pattern.Pattern => NONE;

(*The code under test.  The runner is deliberately more than two-valued and gives
  `Pattern.Unif' a bucket of its own: a `handle _ => false' runner would record a
  leaked Unif as an ordinary "did not match" and the defect would look green.*)
datatype outcome = OK of Type.tyenv * Envir.tenv | NO of string;

fun plpr fb bvs po =
  OK (PLPR_Pattern.match thy fb bvs po (Vartab.empty, Vartab.empty))
  handle Pattern.MATCH => NO "REJECT"
       | Pattern.Unif => NO "!! Pattern.Unif LEAKED"
       | Pattern.Pattern => NO "!! Pattern.Pattern leaked"
       | Subscript => NO "!! Subscript leaked"
       | TERM (m, _) => NO ("!! TERM " ^ m)
       | TYPE (m, _, _) => NO ("!! TYPE " ^ m);

(*The type instantiation is kept and rendered.  Dropping it would make every
  regression that shows only in `tyenv' -- notably the one the comment above
  `first_order_match's `fastype_of1' forbids -- invisible.  It renders empty for
  a sample whose types hold no schematic type variables, so it costs the existing
  expectations nothing.*)
fun shT (Type (n, [])) = n
  | shT (Type (n, Ts)) = n ^ "[" ^ commas (map shT Ts) ^ "]"
  | shT (TFree (n, _)) = n
  | shT (TVar ((n, i), _)) = "?" ^ n ^ string_of_int i;

fun shtyenv tys =
  Vartab.fold (fn ((n, i), (_, T)) => fn s => s ^ "?" ^ n ^ string_of_int i ^ "::=" ^ shT T ^ " ")
    tys "";

fun show_outcome (NO s) = s
  | show_outcome (OK (tys, tms)) = "ACCEPT  " ^ shenv tms ^ shtyenv tys;

(*The substitution the contract prescribes -- a binding dropped into a position
  under n binders is lifted by n -- is `PLPR_Pattern.subst_term', so the check
  below exercises the shipped function rather than a private reimplementation of
  it.  Plain `Envir.subst_term' does NOT lift and would silently capture.*)

(*Soundness, oracle-free and always applicable: put the stored bindings back into
  the pattern and compare literally with the object.  A binding that points at
  the wrong variable fails here without anyone having to say what the right
  answer was.

  Compared in the module's OWN representation -- loose `Bound's, not `Free's.
  Substituting the contextual bound variables away is the operation this fork
  exists to avoid, and doing it here would also hide two things: a binding that
  ran past the end of `bvs' (`Term.subst_bounds' silently decrements those) and a
  collision between a `bvs' name and a `Free' of the same name.

  It hands back what it compared, so the diagnostic cannot drift from the
  judgement -- which is exactly how the two used to disagree.*)
fun sound pat obj (tys, tms) =
  let
    val got = sh (Envir.beta_eta_contract (PLPR_Pattern.subst_term (tys, tms) pat))
    val want = sh (Envir.beta_eta_contract obj)
  in if got = want then NONE else SOME (got, want) end;

(*The stored numbering is defined relative to the position `match' was called at,
  so putting the whole problem one binder deeper must leave `tenv' untouched.
  Oracle-free, applies to every sample including the ones the kernel cannot
  adjudicate, and it is the executable form of the storage convention itself.*)
fun deepen t = qq $ Abs ("d", a, Term.incr_boundvars 1 t);
\<close>

subsection \<open>The corpus\<close>

text \<open>
  Each sample states the outcome it must produce.  \<open>Escapes\<close> marks the samples
  whose expected instantiation keeps a contextual bound variable: there the
  kernel oracle speaks only for plain upstream, which forbids exactly what the
  relaxation permits, so it is not consulted for those.
\<close>

ML \<open>
datatype expect = Accept of string | Reject;
datatype oracle_use = Consult | Escapes;

type sample =
  {name: string, bvs: (string * typ) list, fb: int -> bool,
   pat: term, rhs: term, obj: term, expect: expect, use: oracle_use};

val i_m   = [("i", a), ("m", a)];
val i_m_o = [("i", a), ("m", a), ("o", a)];
val w_v   = [("w", a), ("v", a)];
val c1    = [("c", a)];

fun K_true (_: int) = true;
fun K_false (_: int) = false;
fun not_o k = k <> 2;   (*i and m fixed, o not*)

val corpus : sample list =
 [(*---- family 1: the repeated-schematic comparison, all three directions ----*)
  {name = "1a over-accept: two occurrences, different context variables",
   bvs = i_m, fb = K_true,
   pat = pp $ vx $ (qq $ Abs ("z", a, ss $ vx)),
   rhs = ss $ vx,
   obj = pp $ (ff $ Bound 1) $ (qq $ Abs ("z", a, ss $ (ff $ Bound 1))),
   expect = Reject, use = Consult},

  {name = "1b under-accept: two occurrences, same context variable",
   bvs = i_m, fb = K_true,
   pat = pp $ vx $ (qq $ Abs ("z", a, ss $ vx)),
   rhs = ss $ vx,
   obj = pp $ (ff $ Bound 0) $ (qq $ Abs ("z", a, ss $ (ff $ Bound 1))),
   expect = Accept "?x0:=(ff B0) ", use = Escapes},

  {name = "1c green witness: two occurrences at the SAME depth",
   bvs = c1, fb = K_true,
   pat = qq $ Abs ("y", a, pp $ vx $ vx),
   rhs = qq $ Abs ("y", a, ss $ vx),
   obj = qq $ Abs ("y", a, pp $ (ff $ Bound 1) $ (ff $ Bound 1)),
   expect = Accept "?x0:=(ff B0) ", use = Escapes},

  (*---- family 2: what change (2) really unlocks -- the binding keeps a loose
         index that is NOT in `is'.  Closed pattern, K true: leaks Unif today. ----*)
  {name = "2 closed pattern, binding keeps a context variable outside is",
   bvs = c1, fb = K_true,
   pat = qq $ Abs ("p", a, qq $ Abs ("q", a, vP $ Bound 0)),
   rhs = qq $ Abs ("p", a, qq $ Abs ("q", a, vP $ Bound 0)),
   obj = qq $ Abs ("p", a, qq $ Abs ("q", a, pp $ Bound 0 $ Bound 2)),
   expect = Accept "?P0:=(%q. ((pp B0) B1)) ", use = Escapes},

  (*---- family 3: `is' containing indices >= diff.  GREEN witnesses: today's
         code is right here, the change must leave them literally alone.  3a is
         the shape IDE_CP_Applications1.thy:791 builds. ----*)
  {name = "3a green witness: IDE_CP reconstruct_pattern shape (K false)",
   bvs = w_v, fb = K_false,
   pat = ff $ (vQ $ Bound 0 $ Bound 1),
   rhs = vQ $ Bound 0 $ Bound 1,
   obj = ff $ (pp $ Bound 0 $ Bound 1),
   expect = Accept "?Q0:=(%w. (%v. ((pp B1) B0))) ", use = Consult},

  {name = "3b green witness: is mixes an entered binder and a context variable",
   bvs = i_m_o, fb = not_o,
   pat = qq $ Abs ("z", a, vQ $ Bound 0 $ Bound 2),
   rhs = qq $ Abs ("z", a, vQ $ Bound 0 $ Bound 2),
   obj = qq $ Abs ("z", a, pp $ Bound 2 $ Bound 0),
   expect = Accept "?Q0:=(%z. (%m. ((pp B0) B1))) ", use = Consult},

  (*---- family 3 continued: `is' a PERMUTATION of the entered binders rather
         than a subset of them.  `downto0' fails on any permutation that is not
         descending, so this reaches the slow path with every index bound by
         `mkabs' -- the branch where the membership test and the discarded
         `j < diff' test agree.  3c keeps nothing, 3d additionally keeps a
         contextual bound variable, which is what makes the arithmetic branch
         run beside the `idx' one. ----*)
  {name = "3c green witness: is is a permutation of the entered binders",
   bvs = c1, fb = K_true,
   pat = qq $ Abs ("u1", a, qq $ Abs ("u2", a, vQ $ Bound 0 $ Bound 1)),
   rhs = vQ $ aa $ aa,
   obj = qq $ Abs ("u1", a, qq $ Abs ("u2", a, pp $ Bound 1 $ Bound 0)),
   expect = Accept "?Q0:=(%u2. (%u1. ((pp B0) B1))) ", use = Consult},

  {name = "3d permutation, and the binding also keeps a context variable",
   bvs = c1, fb = K_true,
   pat = qq $ Abs ("u1", a, qq $ Abs ("u2", a, vQ $ Bound 0 $ Bound 1)),
   rhs = vQ $ aa $ aa,
   obj = qq $ Abs ("u1", a, qq $ Abs ("u2", a, pp $ Bound 1 $ (pp $ Bound 0 $ Bound 2))),
   expect = Accept "?Q0:=(%u2. (%u1. ((pp B0) ((pp B1) B2)))) ", use = Escapes},

  (*---- family 4: the first-order fallback.  `?P aa' makes ints_of raise
         Pattern, so the whole match restarts in first_order_match; the repeated
         `?x' then exercises change (4). ----*)
  {name = "4 first-order fallback, repeated schematic at different depths",
   bvs = i_m, fb = K_true,
   pat = rr $ (vP $ aa) $ vx $ (qq $ Abs ("z", a, ss $ vx)),
   rhs = ss $ vx,
   obj = rr $ (gg $ aa) $ (ff $ Bound 0) $ (qq $ Abs ("z", a, ss $ (ff $ Bound 1))),
   expect = Accept "?P0:=gg ?x0:=(ff B0) ", use = Escapes},

  {name = "4b first-order fallback, single occurrence stored below a binder",
   bvs = i_m, fb = K_true,
   pat = rr $ (vP $ aa) $ aa $ (qq $ Abs ("z", a, ss $ vx)),
   rhs = ss $ vx,
   obj = rr $ (gg $ aa) $ aa $ (qq $ Abs ("z", a, ss $ (ff $ Bound 1))),
   expect = Accept "?P0:=gg ?x0:=(ff B0) ", use = Escapes},

  (*---- family 5: the stored value is not an Abs, so `red' peels nothing and
         falls to the `app' branch with `is' non-empty. ----*)
  {name = "5 stored value is not an Abs, second occurrence takes an argument",
   bvs = c1, fb = K_true,
   pat = s2 $ vP $ Abs ("u", a, vP $ Bound 0),
   rhs = qq $ vP,
   obj = s2 $ (pp $ Bound 0) $ Abs ("u", a, pp $ Bound 1 $ Bound 0),
   expect = Accept "?P0:=(pp B0) ", use = Escapes},

  (*---- family 7: the relaxation itself.  7a is the sample the semantics of
         `fixed_bounds' was pinned on; 7b is its control, differing only in that
         the surviving variable is one the caller forbade. ----*)
  {name = "7a relaxation: binding keeps a variable the caller declared fixed",
   bvs = i_m_o, fb = not_o,
   pat = vP $ Bound 1,
   rhs = vP $ Bound 1,
   obj = pp $ Bound 0 $ Bound 1,
   expect = Accept "?P0:=(%m. ((pp B1) B0)) ", use = Escapes},

  (*---- The four below were added after mutation testing showed that reverting
         several of the five changes left the corpus entirely green. ----*)

  (*`red' only ever peels an `Abs' when the stored binding was built by `mkabs',
    i.e. when BOTH occurrences carry arguments.  Without that, `jn' stays empty,
    `nth jn' never succeeds and the `- length jn' term never does any work.  The
    two occurrences also sit at different depths, so `length jn' and `diff' do
    not cancel.  The first occurrence additionally takes the `downto0' fast path,
    which nothing else in the corpus reaches.*)
  {name = "X1 red peels a stored Abs: both occurrences carry arguments, different depths",
   bvs = c1, fb = K_true,
   pat = s2 $ Abs ("u", a, vP $ Bound 0) $ Abs ("u", a, qq $ Abs ("w", a, vP $ Bound 1)),
   rhs = qq $ vP,
   obj = s2 $ Abs ("u", a, pp $ Bound 0 $ Bound 1)
            $ Abs ("u", a, qq $ Abs ("w", a, pp $ Bound 1 $ Bound 2)),
   expect = Accept "?P0:=(%u. ((pp B0) B1)) ", use = Escapes},

  (*The first-order twin of 1a.  `?P aa' makes `ints_of' raise `Pattern', so the
    whole match restarts in `first_order_match'; the two occurrences of `?x' then
    name DIFFERENT contextual bound variables and must be refused.  This is the
    only direction that turns a `true' into a `false', i.e. the only one that can
    make a reasoner set shrink.*)
  {name = "X2 first-order fallback, repeated schematic naming different context variables",
   bvs = i_m, fb = K_true,
   pat = rr $ (vP $ aa) $ vx $ (qq $ Abs ("z", a, ss $ vx)),
   rhs = ss $ vx,
   obj = rr $ (gg $ aa) $ (ff $ Bound 0) $ (qq $ Abs ("z", a, ss $ (ff $ Bound 2))),
   expect = Reject, use = Consult},

  (*The `escaping' gate on the first-order path -- the previous round's fix, which
    had no regression witness at all.  It is also what makes the negative shift in
    that path safe: with the gate defeated, the store produces `Bound (~1)'.*)
  {name = "X3 first-order fallback, the escaping gate must refuse an entered binder",
   bvs = i_m, fb = K_true,
   pat = rr $ (vP $ aa) $ aa $ (qq $ Abs ("z", a, ss $ vx)),
   rhs = ss $ vx,
   obj = rr $ (gg $ aa) $ aa $ (qq $ Abs ("z", a, ss $ (ff $ Bound 0))),
   expect = Reject, use = Consult},

  (*The entered binder has a type of its own, so `fastype_of1' is asked a question
    it can get wrong: reading the SHIFTED term there yields `'b' where `'a' is
    required and the match collapses to a refusal.  Nothing else in the corpus can
    see that -- every other sample is uniformly typed.*)
  {name = "X4 first-order fallback, entered binder of a different type",
   bvs = i_m, fb = K_true,
   pat = rr $ (vP $ aa) $ aa $ (qb $ Abs ("z", b, vy)),
   rhs = vy,
   obj = rr $ (gg $ aa) $ aa $ (qb $ Abs ("z", b, Bound 1)),
   expect = Accept "?P0:=gg ?y0:=B0 ", use = Escapes},

  {name = "7b control: binding would keep a variable the caller forbade",
   bvs = i_m_o, fb = not_o,
   pat = vP $ Bound 1,
   rhs = vP $ Bound 1,
   obj = pp $ Bound 2 $ Bound 1,
   expect = Reject, use = Consult}];
\<close>

subsection \<open>Family 6: the two subterm walkers\<close>

text \<open>
  \<^ML>\<open>PLPR_Pattern.matches_subterm_of\<close> and \<^ML>\<open>PLPR_Pattern.find_matching_subterms\<close>
  are not passive boolean shells over \<^ML>\<open>PLPR_Pattern.matches\<close>: they build the
  \<open>bvs\<close> themselves as they descend and wire \<open>fixed_bounds\<close> to \<open>K true\<close>, so every
  binder in the object is declared treatable as a free variable and the caller has
  no say. They therefore need their own samples; the ones above cannot stand in.
\<close>

ML \<open>
(*A rule whose right-hand side repeats an abstraction from its left-hand side --
  the shape a self-looping simp rule has, and the shape `looping_simp' asks about.
  Both occurrences sit one binder deep, so the answer depends on the stored
  binding being numbered from the call site.*)
val sub_pat = s2 $ Abs ("u", a, vx) $ Abs ("u", a, vx);
val sub_obj = ff $ (s2 $ Abs ("u", a, ff $ Bound 1) $ Abs ("u", a, ff $ Bound 1));

val hit = PLPR_Pattern.matches_subterm_of thy c1 sub_pat sub_obj;
val found = PLPR_Pattern.find_matching_subterms thy c1 sub_pat sub_obj;

val want_found = sh (close c1 (s2 $ Abs ("u", a, ff $ Bound 1) $ Abs ("u", a, ff $ Bound 1)));

val subterm_errors =
  (if hit then []
   else ["matches_subterm_of missed a subterm that matches\n" ^
         "      pattern = " ^ sh sub_pat ^ "\n      object  = " ^ sh sub_obj]) @
  (case found of
     [t] => if sh t = want_found then []
            else ["find_matching_subterms returned " ^ sh t ^ "\n      want " ^ want_found]
   | ts => ["find_matching_subterms returned " ^ string_of_int (length ts) ^
            " subterms, expected 1"]);
\<close>

subsection \<open>Running it\<close>

ML \<open>
fun check ({name, bvs, fb, pat, rhs, obj, expect, use} : sample) =
  let
    val got = plpr fb bvs (pat, obj);
    val got_s = show_outcome got;
    val want_s = (case expect of Reject => "REJECT" | Accept s => "ACCEPT  " ^ s);

    val outcome_err =
      if got_s = want_s then []
      else ["outcome:  got " ^ quote got_s ^ "\n             want " ^ quote want_s];

    val sound_err =
      (case got of
         OK env =>
           (case sound pat obj env of
              NONE => []
            | SOME (lhs, rhs') =>
                ["unsound:  the stored binding does not reproduce the object\n" ^
                 "             pattern instantiated = " ^ lhs ^
                 "\n             object              = " ^ rhs' ^
                 "\n             (contextual bound variables shown as B<i>; bvs = " ^
                 commas (map fst bvs) ^ ", head innermost)"])
       | NO _ => []);

    (*the storage convention, machine-checked: one binder deeper, same `tenv'*)
    val deeper_err =
      let val deep_s = show_outcome (plpr fb bvs (deepen pat, deepen obj)) in
        if deep_s = got_s then []
        else ["depth:    putting the whole problem one binder deeper changed the result\n" ^
              "             here  " ^ quote got_s ^ "\n             deeper " ^ quote deep_s]
      end;

    val oracle_err =
      (case use of
         Escapes => []
       | Consult =>
           let
             val k = kernel (bvs, pat, rhs, obj);
             val rewrote = is_some k;
             val accepted = (case got of OK _ => true | NO _ => false);
           in if rewrote = accepted then []
              else ["oracle:   kernel " ^ (if rewrote then "rewrote" else "did not rewrite") ^
                    " but PLPR_Pattern " ^ (if accepted then "accepted" else "rejected")]
           end);

    (*the deliberately broken oracle must disagree somewhere, otherwise the
      oracle is not sensitive to the thing under test*)
    val control_differs =
      (case use of
         Escapes => NONE
       | Consult =>
           let val good = kernel (bvs, pat, rhs, obj)
               val bad = kernel_blind (bvs, pat, rhs, obj)
           in SOME (case (good, bad) of
                      (SOME x, SOME y) => sh x <> sh y
                    | (NONE, NONE) => false
                    | _ => true)
           end);

    val errs = outcome_err @ sound_err @ deeper_err @ oracle_err;
  in (name, errs, got_s, control_differs) end;

local

val results = map check corpus;

val _ =
  if report then
    writeln (cat_lines (map (fn (n, _, g, c) =>
      "  " ^ n ^ "\n      -> " ^ g ^
      (case c of NONE => "" | SOME b => "\n      control oracle differs: " ^ Bool.toString b))
      results))
  else ();

val failures =
  filter (fn (_, errs, _, _) => not (null errs)) results @
  (if null subterm_errors then [] else [("family 6: the subterm walkers", subterm_errors, "", NONE)]);

val _ =
  if null failures then
    writeln ("PLPR_Pattern_Test: " ^ string_of_int (length corpus) ^ " samples + the subterm " ^
             "walkers, all pass.  " ^
             "Control-oracle disagreements: " ^
             string_of_int (length (filter (fn (_, _, _, c) => c = SOME true) results)) ^
             " of " ^ string_of_int (length (filter (fn (_, _, _, c) => is_some c) results)) ^
             " consulted.")
  else
    error (cat_lines ("PLPR_Pattern_Test: " ^ string_of_int (length failures) ^ " of " ^
                      string_of_int (length corpus) ^ " samples FAILED" ::
           maps (fn (n, errs, _, _) => ("" :: ("  " ^ n) :: map (prefix "      ") errs)) failures));

in end
\<close>

end
