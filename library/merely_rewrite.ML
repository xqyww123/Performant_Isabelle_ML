(* Rewriting to a fixpoint with rules indexed by a discrimination net (iNet).

   THE NAME IS THE SPECIFICATION.  "Merely" is literal: pick candidate rules out of
   an iNet, rewrite bottom-up to a fixpoint, contract beta redexes on the way, and
   perform NO eta normalisation.  No conditional rewriting, no permutative or
   associative rules, no object-logic conversion, no simpset, no congruence rules,
   no solver.  Anything that needs those wants `Raw_Simplifier'.  The value here is
   what is ABSENT: no eta contraction and no binder renaming, so untouched material
   comes back exactly as it went in.  Beta redexes are the one exception, contracted
   eagerly and on purpose: material that exists only in the beta normal form is
   invisible to a subterm traversal (a rule matching `ff 2' never fires inside
   `(%x. gg (ff x)) $ 2'), and a rule whose right-hand side is an abstraction
   manufactures such a redex mid-traversal.  `Pattern.rewrite_term' contracts in
   the same places (more_pattern.ML:67, 73-75).

   Why not something existing.  `Raw_Simplifier.rewrite' has the right traversal but
   eta-contracts and renames binders: a rule firing at a node composes the equation
   with `Thm.eta_conversion' of that node, so parts no rule touched come back
   eta-contracted with the user's binder names gone -- for output read by a human or
   an LLM that is a real loss.  `Pure/conv.ML' does no such damage, but none of its
   four traversals re-scans the RESULT of a rewrite in place, so a fixpoint costs
   `Conv.repeat_changed_conv' around the whole term, i.e. up to O(depth) full sweeps.

   Candidates are tried most-specific-first across keys: a general rule never
   shadows a specific one.  `Raw_Simplifier' does the opposite (`sort_rrules'
   reverses the net list, so its most general candidate fires first); the
   divergence is deliberate.

   THE ONE STRUCTURAL RULE.  The traversal is built on `Conv.sub_conv' and its fork
   `sub_conv_skel', NEVER on a case table over `Pure.imp' / `Pure.all' / `&&&'.  A
   case table would stop the traversal descending into connectives the caller's own
   rules introduce, and it would have to re-implement the `abs_conv (conv o snd)'
   line, whose `snd' threads the EXTENDED context `Conv.abs_conv' hands back.
   Dropping that is not a compile error but a run-time one ("Bad context: clash of
   fresh free for bound", variable.ML).

   TERMINATION IS THE CALLER'S PROBLEM.  Nothing is inspected when a rule is added.
   Two run-time backstops keep a divergent run from taking the session down; they
   are not loop detectors and cannot say what was going round in circles:

     - a step limit;
     - a bound on how far the term may GROW relative to the input.  Cheap because a
       step replaces one node, so the running sum of `size(residue) - size(redex)'
       IS `size(current term) - size(input)'.  That identity needs an ADDITIVE
       measure, which is why `Term.size_of_term' is used and the smart one in
       library/term_size.ML is not.

   A beta contraction is accounted exactly like a rule step: it passes the step
   limit and its size delta is charged against the growth bound, so the identity
   above still holds.  (On well-typed input beta alone is strongly normalising;
   the accounting is there so that "steps" stays an honest number and argument
   duplication -- `(%x. f x x) BIG' -- stays inside the growth budget.)

   Divergence that neither repeats a term nor grows one is caught by neither.

   TWO LAYERS.  `Thm.cterm_of' REJECTS a term containing a loose `Bound' ("Loose
   bound variable: B.n", sign.ML), so the conv layer cannot be handed one.  The term
   layer (`rewrite_term_bvs') exists for callers that must rewrite exactly such
   terms; `Object_Logic.atomize_term' is the standard example.  It produces NO
   PROOF, which is what it gives up and also why it is much the faster of the two.

   SKELETON PRUNING.  Re-traversing the whole result of every hit is O(size^2) worst
   case.  A skeleton runs alongside the term and records where material came from:
   it is the rule's right-hand side, in which a `Var' is a HOLE (material matched
   out of the term, already in beta normal form -- condition (a) keeps a skeleton
   only when the whole step result is deeply beta-normal -- so skipped)
   and everything else is SHELL (new material from the rule, possibly a redex
   itself, so traversed).  The projections and `is_hole' are defined ONCE and both
   layers use them: the skeleton discipline is the one thing they must never
   disagree about.

   THREE CONDITIONS DISQUALIFY A RIGHT-HAND SIDE FROM BEING A SKELETON; when any
   holds, the step falls back to `skel0' and prunes nothing.  None of them subsumes
   another -- (a) and (c) were each verified to be load-bearing on their own:

   (a) the deep beta ending `Conv.rewr_conv' changed the right-hand side, so the
       skeleton no longer aligns with it, or hole material was rewritten IN PLACE
       into a form the traversal never normalised;
   (b) the right-hand side has a schematic the left-hand side does not bind, so that
       hole is filled with material that arrived with the RULE, never normalised;
   (c) the left-hand side is not a first-order pattern, so the matcher may have
       SYNTHESISED the hole material with `mkabs' -- a node not in the term at all.

   WHAT THE LAYERS SHARE: the skeleton projections and `is_hole'; the candidate
   lookup; the two backstops, built once by `make_guard'; conditions (b) and (c).
   Condition (a) is two implementations of one test -- read both.  NOT shared, and
   deliberately: the traversal recursion.  The carriers represent "nothing changed"
   in opposite ways (a reflexive theorem that must still be composed, versus `NONE'),
   and the conv layer must build a kernel inference at every node while the term
   layer must build nothing at all -- which is the entire reason the term layer
   exists.  A functor over an abstract carrier would save about ten lines and put an
   indirect call in the hottest loop of both.  The cross-layer differential test is
   what keeps the two `go' functions from drifting.

   TWO DELIBERATE DEVIATIONS FROM `Pattern.rewrite_term', both so that the two
   layers agree with each other:

   1. the result of each step IS `Envir.beta_norm'-ed, because that is what
      `Conv.rewr_conv' does at the conv layer.  If that deep beta is ever dropped,
      BOTH layers must drop it in one edit.  (It is also load-bearing for skeleton
      condition (a) and for the loose-Bound bindings contract of the PLPR pattern matcher
      (Phi_Logic_Programming_Reasoner/library/pattern.ML:26-30, NOT Pure) --
      do not remove it.)
   2. going under a binder REWRITES NOTHING: the term layer pushes the binder onto
      a `bvs' list threaded through the traversal and consumed by the matcher
      (`PLPR_Pattern.match') and the substituter (`PLPR_Pattern.subst_term', which
      lifts each binding by its landing depth), where `Pattern.rewrite_term' opens
      the binder with `variant_absfree' and re-abstracts afterwards.  Opening is
      what silently skipped every rewrite whose binding contained a loose `Bound'
      and let the first-order fallback capture one under a rule-supplied binder;
      threading `bvs' makes those positions rewritable and capture-free.

   (An earlier third deviation -- "a beta redex is not a rewrite step" -- was
   withdrawn 2026-08: it made rewrites that exist only in the beta normal form
   silently unreachable.  Beta contraction now mirrors more_pattern.ML:67/:73-75.)

   Measurements, soundness arguments and review history: NET_REWRITE_PLAN.md.

   Qiyuan Xu (with AI assistance)
*)

signature MERELY_REWRITE =
sig
  type rules = thm iNet.net

  (* Rule sets.

     INPUT CONTRACT: every rule must already be a meta-equation `lhs == rhs'.  This
     module does not convert object-logic equations and does not want to -- that
     conversion is logic-specific and `Raw_Simplifier.mksimps' (raw_simplifier.ML:67)
     is the canonical one.  Pass its output.  Anything else is rejected by
     `dest_rule'.

     ORDER AMONG RULES WITH THE SAME NET KEY: the whole semantics is a LIST
     PREPEND.  `add_rule' conses onto the front of that key's list, and lookup
     reads it from the front, so the LAST one added fires first -- override
     semantics: a later, better rule takes effect without deleting the old one.
     This is the OPPOSITE of Raw_Simplifier, where `sort_rrules' makes the
     first-registered rule win.

     `make_rules' builds the same list directly, so its argument IS that list,
     front first: `make_rules [a, b, c]' tries a, then b, then c.  (It therefore
     inserts back to front, which is the only way both readings can hold at
     once.)  `dest_rules' hands the list back in the same order, so

         make_rules (dest_rules net) = net

     for every net -- snapshotting and rebuilding a rule set is safe, and
     `Skel_Boundary' pins it.  It was not always: `make_rules' used to fold
     front-to-back, which quietly reversed every same-key group on the way
     round. *)
  val empty_rules: rules
  val add_rule: thm -> rules -> rules
  val del_rule: thm -> rules -> rules
  val make_rules: thm list -> rules
  val dest_rules: rules -> thm list

  (*`Theory_Data'/`Generic_Data' demand a merge, a theory being a DAG.  Writing one
    by hand is possible -- `rules' is transparent -- but `iNet.merge' takes an
    equality predicate, and it has to be the SAME one `add_rule' and `del_rule' use
    (`Thm.eq_thm_prop': prop + tpairs).  Guessing `Thm.eq_thm' -- which additionally
    compares hyps and shyps; NO predicate looks at certificates, so trimming never
    affects equality -- keeps two copies after a merge whenever same-prop rules
    differ in hyps or shyps, and both then fire as duplicate candidates (a later
    `del_rule' removes both at once -- `iNet' deletion filters every equal copy).
    Exported so that callers write `val merge = Merely_Rewrite.merge_rules' and
    cannot get that wrong.*)
  val merge_rules: rules * rules -> rules

  (* ONE rewrite step, at the current node only -- no traversal whatsoever.  The
     net is only where the candidates come from; the caller decides where in the
     term this gets applied.  `Pure/conv.ML' already offers three traversal orders
     to feed it to (`Conv.bottom_conv', `Conv.top_conv', `Conv.top_sweep_conv');
     the one this module adds is bottom-up with in-place re-scanning, below.

     The single-step functions contract no beta redexes; only the traversals
     below do.  Composing them with `Conv.top_sweep_conv' therefore does NOT
     reproduce `rewrite_conv' on a term containing one. *)
  val single_step_rewrite_conv: (Proof.context -> 'a -> conv) -> 'a iNet.net -> Proof.context -> conv
  val rewrs_net_conv: rules -> Proof.context -> conv

  (* The same, at the term level: one step at this node, `NONE' if no rule applies.
     `single_step_rewrite_term' is `single_step_rewrite_conv' with `get_first' in
     place of `Conv.first_conv', over the same net and the same candidates.
     `bvs' types the loose `Bound's of the node; see the loose-bound contract at
     the term entry points below.  NO ENTRY ASSERTION HERE, unlike the traversals:
     one node is not worth a rescan of the term, so a `bvs' too short for this
     node surfaces as whatever the matcher raises on the `Bound' it cannot type,
     not as the contract's own message. *)
  val single_step_rewrite_term:
    (Proof.context -> 'a -> bvs -> term -> term option) -> 'a iNet.net ->
    Proof.context -> bvs -> term -> term option
  val rewrs_net_term: rules -> Proof.context -> bvs -> term -> term option

  (* SKELETONS.  A skeleton is a term of the same shape as the right-hand side of
     the equation a step produced, with a `Var' wherever that position was filled
     with material taken out of the term being rewritten (a HOLE, already normal,
     skipped) and anything else where the rule's right-hand side put it (SHELL, new,
     traversed).  `skel0' is the wildcard: it claims nothing is a hole and therefore
     prunes nothing.

     A step that hands back a skeleton it cannot justify SILENTLY loses rewrites --
     no exception, no warning.  Produce skeletons with `rewr_skel_conv' /
     `rewrs_net_skel_conv' / `rewrs_net_skel_term', which know the three conditions
     that disqualify a right-hand side; do not invent them. *)
  type skel = term
  val skel0: skel
  val is_hole: skel -> bool
  val skel_fun: skel -> skel
  val skel_arg: skel -> skel
  val skel_body: skel -> skel

  type skel_conv = cterm -> thm * skel
  type skel_term = bvs -> term -> (term * skel) option
  val rewr_skel_conv: thm -> skel_conv
  val single_step_rewrite_skel_conv:
    (Proof.context -> 'a -> skel_conv) -> 'a iNet.net -> Proof.context -> skel_conv
  val single_step_rewrite_skel_term:
    (Proof.context -> 'a -> skel_term) -> 'a iNet.net -> Proof.context -> skel_term
  val rewrs_net_skel_conv: rules -> Proof.context -> skel_conv
  val rewrs_net_skel_term: rules -> Proof.context -> skel_term

  (* divergence.

     The payload is a `term', not a `cterm', because the term layer must be able to
     raise this same exception and its input may contain loose `Bound' variables,
     which `Thm.cterm_of' rejects ("Loose bound variable: B.n", sign.ML).

     A caller that wants the `cterm' back writes `Thm.cterm_of ctxt t'.  That is
     O(size), and it is NOT guaranteed to succeed -- the payload may be an open term
     from the term layer, or name a constant this theory does not have.  Nothing in
     the payload's type says which layer it came from, so be prepared for it to
     fail. *)
  datatype divergence =
      Step_Limit of int
    | Growth of {input_size: int, current_size: int, allowed_growth: int, residue: term}
  exception DIVERGES of divergence * term
  val string_of_divergence: Proof.context -> rules -> divergence * term -> string

  (* how much the term may grow before L5 gives up: growth_factor * size of the
     input + growth_offset *)
  val growth_factor: int Config.T
  val growth_offset: int Config.T

  (* the traversal, independent of how a single step is performed.

     THREE SOURCES, IN THIS ORDER OF PRECEDENCE -- this is the only place the rule
     is stated, everything else refers here:

       1. the `options' passed to the call        (highest)
       2. the Config values in the context
       3. the built-in defaults in this file      (lowest)

     The Config layer is for the USER: settable with `declare [[...]]', visible in
     `print_options', the way to raise the thresholds for a whole theory.  The
     `options' layer is for a LIBRARY CALLER who needs a hard guarantee -- "this call
     will never take more than N steps" must not be loosened by whatever a
     surrounding context happens to say, so an explicit argument wins.

     `step_limit' is doubly optional on purpose: `NONE' is "do not override",
     `SOME NONE' is "override, with no limit at all".

     The traversal itself contracts beta redexes (accounted like steps); a
     caller-supplied step never sees them and cannot veto them.  Consequently,
     with an empty rule set these are NOT the identity on a term containing a
     beta redex.

     The step MUST return an equation whose left-hand side is the cterm it was
     given.  This is not checked: a step that equates some OTHER term burns the
     whole step budget and then reports that unrelated term.  A step returning
     a non-equation is caught and re-raised as `Fail' with the offending
     theorem (a THM/CTERM/TERM/TYPE exception would be swallowed by
     `else_conv' as "no rewrite here"). *)
  type options =
    {size_check: bool option,
     step_limit: int option option,
     growth_factor: int option,
     growth_offset: int option} option
  val default_options: options   (*NONE: take everything from the layers below*)
  val no_check: options          (*every guard off -- see the note at its definition*)
  val bottom_fixpoint_conv: options -> (Proof.context -> conv) -> Proof.context -> conv
  val bottom_fixpoint_term:
    options -> (Proof.context -> bvs -> term -> term option) ->
    Proof.context -> bvs -> term -> term

  (* the same two traversals, given a step that also hands back a skeleton: the
     subtrees the skeleton marks as holes are neither descended into nor rewritten
     at.  The skeleton is taken ON TRUST; see the note above. *)
  val bottom_fixpoint_skel_conv: options -> (Proof.context -> skel_conv) -> Proof.context -> conv
  val bottom_fixpoint_skel_term:
    options -> (Proof.context -> skel_term) -> Proof.context -> bvs -> term -> term

  (* TEST-ONLY -- the switch the correctness comparison is built on.  `Reference' is
     the traversal as it was before skeletons existed, PLUS the same beta clauses
     as the live traversals -- an oracle must share deliberate semantics, or the
     three-way comparison reports the design as a bug.
     `No_Skeleton' is the forked traversal fed nothing but `skel0'.  So `Reference'
     vs `No_Skeleton' tests the FORK, `No_Skeleton' vs `Skeleton' tests the PRUNING.
     `Reference' is to be moved into a test-only file and deleted from here.

     There is deliberately no Config to turn pruning off: with conditions (a), (b)
     and (c) in place it does not change what comes out, only how many nodes are
     visited (re-measured after the beta change: pruning rate unchanged, see
     MERELY_REWRITE_EAGER_BETA_PLAN.md). *)
  datatype mode = Reference | No_Skeleton | Skeleton
  val bottom_fixpoint_conv_mode:
    mode -> options -> (Proof.context -> conv) -> Proof.context -> conv
  val bottom_fixpoint_term_mode:
    mode -> options -> (Proof.context -> bvs -> term -> term option) ->
    Proof.context -> bvs -> term -> term
  val rewrite_conv_mode: mode -> options -> rules -> Proof.context -> conv
  val rewrite_term_mode: mode -> options -> rules -> Proof.context -> bvs -> term -> term

  (* proof-producing entry points.  With an empty rule set these are NOT the
     identity: beta redexes are still contracted. *)
  val rewrite_conv: rules -> Proof.context -> conv
  val rewrite_conv_options: options -> rules -> Proof.context -> conv
  val rewrite_cterm: rules -> Proof.context -> cterm -> cterm
  val rewrite_rule: rules -> Proof.context -> thm -> thm

  (* term-level entry points: NO PROOF.  For callers that cannot use the conv layer
     because `Thm.cterm_of' would reject their term, and for callers that simply do
     not want a theorem.

     Entry points for input terms containing loose `Bound's.  `bvs' lists the
     binders the input sits under: entry k is the binder `Bound k' refers to,
     so the innermost binder comes first.  Same convention as
     `PLPR_Pattern.match'.  `rewrite_term net ctxt = rewrite_term_bvs net ctxt []'.

     This is a garbage-in interface: the content of `bvs' is entirely the
     caller's responsibility.  The single check performed is the entry assertion
     that every loose `Bound' of the input has an entry in `bvs'.  It makes a
     too-short `bvs' fail early with a clear message -- without it the failure
     would surface later as an uncaught TERM thrown from deep inside the
     matcher -- and it guards nothing else: a `bvs' in the wrong order cannot
     be detected (the usual consequence is again silently skipped rewrites;
     when the swapped binders share a type the swap is a complete no-op), and
     a wrong type in `bvs' cannot be detected either (through the first-order
     fallback of the matcher it can even yield an output `Term.type_of'
     rejects).  Extra entries beyond the deepest loose `Bound' are harmless.

     A beta contraction at this layer uses `Term.subst_bound', which renumbers the
     remaining loose `Bound's down by one.  That is correct -- the binder is
     genuinely consumed.

     With an empty rule set these are NOT the identity: beta redexes are still
     contracted. *)
  val rewrite_term: rules -> Proof.context -> term -> term
  val rewrite_term_options: options -> rules -> Proof.context -> term -> term
  val rewrite_term_bvs: rules -> Proof.context -> bvs -> term -> term
  val rewrite_term_bvs_options: options -> rules -> Proof.context -> bvs -> term -> term

end;

structure Merely_Rewrite: MERELY_REWRITE =
struct

type rules = thm iNet.net;

(*ONE equality predicate for insert, delete and merge -- see the signature for why
  that matters.*)
val eq_rule = Thm.eq_thm_prop;


(** rule sets **)

(*MESSAGE TEXT IS NOT FINAL -- see the report for wording candidates.*)
fun dest_rule th =
  Logic.dest_equals (Thm.prop_of th)
    handle TERM _ =>
      raise THM ("Merely_Rewrite: rule is not a meta-equation \"lhs == rhs\"; \
                 \object-logic theorems must be put through Raw_Simplifier.mksimps first",
                 0, [th]);

val empty_rules = iNet.empty;

(*No check that the rule set terminates: that is the caller's responsibility.  See
  the note at the top of the file for what that costs.*)
fun add_rule th = iNet.insert_term_safe eq_rule (#1 (dest_rule th), th);
fun del_rule th = iNet.delete_term_safe eq_rule (#1 (dest_rule th), th);
(*`fold_rev', not `fold': `add_rule' prepends, so building the list front first
  means inserting back to front.  See the order note in the signature.*)
fun make_rules ths = fold_rev add_rule ths empty_rules;
val dest_rules = iNet.content;
val merge_rules = iNet.merge eq_rule;


(** one step **)

(*ONE step, at this node, nothing else: ask the net for the candidates here, then
  try them in turn.  There is no descent into subterms -- that is the caller's
  choice of traversal.  The net is an over-approximation (it ignores types and
  treats a Var head as a wildcard), so a candidate may still fail to match; that is
  expected and cheap.

  iNet.insert_term/match_term beta-eta-contract the key term on both sides, so the
  two sides of the lookup agree.  That normalisation is confined to *key
  computation*; the cterm that gets rewritten is never touched by it.  Verified
  separately that it neither loses nor invents a rewrite.*)
fun single_step_rewrite_conv mk_conv net ctxt ct =
  Conv.first_conv (map (mk_conv ctxt) (iNet.match_term net (Thm.term_of ct))) ct;

(*The same at the term level.  `get_first' is to `term option' what
  `Conv.first_conv' is to a conversion: try the candidates in turn, keep the first
  that works.

  NO exception handler here, deliberately -- it used to swallow TERM/TYPE,
  mirroring `Conv.else_conv'.  The matcher now types a loose `Bound' from `bvs',
  so the one legitimate source of TERM (`fastype_of' on a bare `Bound',
  term.ML:394) is gone, and a candidate that fails to MATCH already comes back as
  NONE from `rewr_skel_term'.  What is left for an exception here to mean is a
  broken invariant or garbage input, and that must be LOUD, not a silently
  dropped candidate.  The conv layer keeps its catching `first' loop: there it is
  `Conv.else_conv' semantics, not a loose-`Bound' workaround.*)
fun single_step_rewrite_term mk_rew net ctxt bvs t =
  get_first (fn x => mk_rew ctxt x bvs t) (iNet.match_term net t);

(*`Thm.transfer'' so that rules stored context-free in theory data (the usual case
  for an incrementally maintained net) are usable in the current context.*)
val rewrs_net_conv = single_step_rewrite_conv (fn ctxt => Conv.rewr_conv o Thm.transfer' ctxt);


(** skeletons **)

type skel = term;
type skel_conv = cterm -> thm * skel;
type skel_term = bvs -> term -> (term * skel) option;

(*The wildcard skeleton and the projections, exactly as in Pure/more_pattern.ML:
  50-53.  `Bound 0' is the wildcard because it is the one term former that can never
  be a `Var' and therefore never a hole; the projections fall back to it whenever
  the skeleton does not have the same shape as the term, which is the whole of the
  defence against a skeleton that has drifted out of alignment.

  THESE FIVE DEFINITIONS ARE THE ONLY PLACE THE SKELETON DISCIPLINE IS STATED, and
  both traversals go through them.*)
val skel0: skel = Bound 0;
val is_hole = Term.is_Var;
fun skel_fun (skel $ _) = skel | skel_fun _ = skel0;
fun skel_arg (_ $ skel) = skel | skel_arg _ = skel0;
fun skel_body (Abs (_, _, skel)) = skel | skel_body _ = skel0;

(*Condition (b) at the top of this file: a schematic on the right that the left does
  not bind.  Cheap -- rules are small -- and it is only ever asked after a match has
  already succeeded.*)
fun has_extra_var (lhs, rhs) =
  let val bound = Term.add_vars lhs [] in
    Term.exists_subterm (fn Var v => not (member (op =) bound v) | _ => false) rhs
  end;

(*(c) A LEFT-HAND SIDE THAT IS NOT A FIRST-ORDER PATTERN, e.g. `qq (%x. ?P x)'.

  The whole point of a hole is that the material in it came OUT of the term being
  rewritten, and the bottom-up traversal has therefore already normalised it.  For
  a first-order left-hand side that is true: every binding `Pattern.match' produces
  is a subterm of the object.  For a higher-order one it is not.  `match_bind'
  (Pure/pattern.ML:319-329) calls `mkabs' (:109-113), which BUILDS an abstraction
  that does not occur in the object at all; the traversal has never visited it, so
  nothing has ever been tried on it, and pruning would skip it as if it had been.

  Counterexample, measured on the module before this test existed: rules
  `qq (%x. ?P x) == rr ?P' and `?F == hh' applied to `qq gg' give `rr (%x. gg x)'
  -- matching eta-expands the object, so `?P := %x. gg x', a node nowhere in
  `qq gg'; `?F == hh' never gets to fire inside the hole; the output is not even a
  fixpoint.

  `mkabs' is reached exactly when `is = ints_of pargs' is non-empty, i.e. exactly
  when a `Var' occurs applied in the pattern -- which is exactly what
  `Pattern.first_order' (Pure/more_pattern.ML:34-37) decides.  The test is therefore
  not an approximation of the danger; it is the same condition.

  IT IS HOWEVER THE CONSERVATIVE FORM, per-RULE: a rule that *could* synthesise
  gives up pruning at *every* application, including those where nothing was.  The
  exact form is per-HOLE and is cheap -- `match_bind' knows which bindings it built
  (they are the ones from the non-empty-`is' branch) and Pure simply discards that.
  Deferred, not dismissed; see NET_REWRITE_PLAN.md for what it would recover.

  NOT a substitute for condition (a), nor (a) for it: (a) catches a deep beta that
  rewrote hole material IN PLACE into a form the traversal never normalised, which
  happens with first-order left-hand sides too.  Removing (a) while keeping this
  test breaks the fuzz corpus.*)
fun lhs_not_first_order lhs = not (Pattern.first_order lhs);

(*A FORK of `Conv.rewr_conv' (Pure/conv.ML:170-183) that also returns the skeleton.
  Everything down to `rule4' is copied verbatim and must stay that way; a wrapper
  around `Conv.rewr_conv' cannot do this instead, because by the time the thm comes
  back the rule is gone AND the deep beta has already happened, so neither condition
  (a) nor the right-hand side itself is still available.*)
fun rewr_skel_conv rule ct =
  let
    val rule1 = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) rule;
    val lhs = Thm.lhs_of rule1;
    val rule2 = Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) rule1;
    val rule3 =
      Thm.instantiate (Thm.match (lhs, ct)) rule2
        handle Pattern.MATCH => raise CTERM ("rewr_conv", [lhs, ct]);
    val rule4 =
      if Thm.lhs_of rule3 aconvc ct then rule3
      else
        let val ceq = Thm.dest_fun2 (Thm.cprop_of rule3)
        in rule3 COMP Thm.trivial (Thm.mk_binop ceq ct (Thm.rhs_of rule3)) end;
    val beta = Thm.beta_conversion true (Thm.rhs_of rule4);
    val rhs = Thm.term_of (Thm.rhs_of rule1);
    val lhs_t = Thm.term_of lhs;
    val skel =
      if Thm.is_reflexive beta                                (*condition (a)*)
        andalso not (has_extra_var (lhs_t, rhs))              (*condition (b)*)
        andalso not (lhs_not_first_order lhs_t)               (*condition (c)*)
      then rhs else skel0;
  in (Thm.transitive rule4 beta, skel) end;

(*The term-level twin, rebuilt on the PLPR matcher so that a loose `Bound' in the
  object is typed from `bvs' instead of raising.  What `Pattern.match_rew' used to
  do here is reproduced piece by piece: `Term.rename_abs' (binder names from the
  redex onto the right-hand side, whose result is precisely the skeleton),
  `handle Pattern.MATCH => NONE' (an iNet candidate failing to match is the
  NORMAL case, and `PLPR_Pattern.match' raises `Pattern.MATCH' on failure -- this
  handler is load-bearing, and it is NOT the deleted TERM/TYPE one), and the
  substitution -- `PLPR_Pattern.subst_term', which lifts each binding by its
  landing depth (`Envir.subst_term' does not, and silent capture was the cost).
  `fixed_bounds' is `K true' ALWAYS: every contextual binder is a fixed variable
  to the matcher; anything else silently drops every rewrite whose binding
  mentions one, so the choice is not exported.  The `Envir.beta_norm' and the
  three conditions mirror `rewr_skel_conv' as before (`Thm.beta_conversion true'
  IS `Envir.beta_norm', thm.ML:1528; `beta_norm' returns the IDENTICAL value when
  there is nothing to contract, so `pointer_eq' answers condition (a) in constant
  time, failing toward lost pruning only).

  Still NOT done here, deliberately: `Thm.incr_indexes'.  `Conv.rewr_conv' renames
  the rule's schematics apart from the term's at every application; this function
  does not, so a rule variable can be conflated with a schematic of the same name
  in the input, and this includes TYPE variables (`Logic.incr_tvar').  Recorded as
  a known cross-layer difference.*)
fun rewr_skel_term thy rule bvs t =
  let
    val (lhs_t, rhs0) = Logic.dest_equals (Thm.prop_of rule);
    val rhs = perhaps (Term.rename_abs lhs_t t) rhs0;
  in
    (case (SOME (PLPR_Pattern.match thy (K true) bvs (lhs_t, t)
                   (Vartab.empty, Vartab.empty))
           handle Pattern.MATCH => NONE) of
      NONE => NONE
    | SOME env =>
        let
          val result = PLPR_Pattern.subst_term env rhs;
          val result' = Envir.beta_norm result;
          val skel =
            if pointer_eq (result, result')                           (*condition (a)*)
              andalso not (has_extra_var (lhs_t, rhs))                (*condition (b)*)
              andalso not (lhs_not_first_order lhs_t)                 (*condition (c)*)
            then rhs else skel0;
        in SOME (result', skel) end)
  end;

(*As `single_step_rewrite_conv' / `single_step_rewrite_term', for steps that carry a
  skeleton.  The conv version reproduces the exception behaviour of
  `Conv.first_conv', i.e. of `Conv.else_conv': the four exceptions a failing
  conversion is allowed to raise are caught and the next candidate tried; an empty
  candidate list raises what `Conv.no_conv' raises.*)
fun single_step_rewrite_skel_conv mk_conv net ctxt ct =
  let
    fun first [] = raise CTERM ("no conversion", [])
      | first (cv :: cvs) =
          cv ct
            handle THM _ => first cvs
              | CTERM _ => first cvs
              | TERM _ => first cvs
              | TYPE _ => first cvs;
  in first (map (mk_conv ctxt) (iNet.match_term net (Thm.term_of ct))) end;

(*no handler, for the reason explained at `single_step_rewrite_term'*)
fun single_step_rewrite_skel_term mk_rew net ctxt bvs t =
  get_first (fn x => mk_rew ctxt x bvs t) (iNet.match_term net t);

val rewrs_net_skel_conv =
  single_step_rewrite_skel_conv (fn ctxt => rewr_skel_conv o Thm.transfer' ctxt);

fun rewrs_net_skel_term net ctxt =
  single_step_rewrite_skel_term
    (fn ctxt' => rewr_skel_term (Proof_Context.theory_of ctxt')) net ctxt;

(*the skeleton-free term step, for `bottom_fixpoint_term'*)
fun rewrs_net_term net ctxt =
  single_step_rewrite_term
    (fn ctxt' => fn rule => fn bvs => fn t =>
      Option.map #1 (rewr_skel_term (Proof_Context.theory_of ctxt') rule bvs t))
    net ctxt;


(** divergence **)

datatype divergence =
    Step_Limit of int
  | Growth of {input_size: int, current_size: int, allowed_growth: int, residue: term};

(*CONFIG NAMES ARE NOT FINAL -- see the report for candidates.  These are options
  rather than constants because the right answer genuinely depends on the rule set:
  a set of unfolding rules is *supposed* to make the term much bigger, and a fixed
  ceiling would put that whole class of use out of reach.*)
(*`Attrib.setup_config_int', NOT `Config.declare_int': the latter creates the config
  value but does NOT register an Isar attribute, so `declare [[...]]' fails with
  "Undefined attribute" and `print_options' does not list it -- i.e. the whole
  Config layer would be reachable only from ML, while the signature above sells it
  as the layer that exists *for the user*, and the L5 failure message points the
  user at exactly these two names.*)
val growth_factor = Attrib.setup_config_int \<^binding>\<open>net_rewrite_growth_factor\<close> (K 10);
val growth_offset = Attrib.setup_config_int \<^binding>\<open>net_rewrite_growth_offset\<close> (K 1000);

(*A dedicated exception, NOT one of THM/CTERM/TERM/TYPE: those four are exactly
  what `Conv.else_conv' swallows, so a report raised with any of them would be
  caught by the `try_conv' inside the traversal and silently turn into "no
  rewrite".*)
exception DIVERGES of divergence * term;

(*MESSAGE TEXT IS NOT FINAL -- see the report for wording candidates.  What matters
  and should survive any rewording: name the rules that are implicated and show the
  terms that repeat.*)
fun string_of_divergence ctxt rules (d, t) =
  let
    val show = Syntax.string_of_term ctxt;
    val culprits = iNet.match_term rules t;
    val rule_text =
      if null culprits then "  (no rule of the set matches this term)"
      else cat_lines (map (fn th => "  " ^ Thm.string_of_thm ctxt th) culprits);
  in
    (case d of
      Step_Limit n =>
        "rewriting did not reach a fixpoint within " ^ string_of_int n ^
        " steps; cut off at\n  " ^ show t ^
        "\nrules applicable at that term:\n" ^ rule_text
    | Growth {input_size, current_size, allowed_growth, residue} =>
        "rewriting keeps making the term bigger: it has grown from " ^
        string_of_int input_size ^ " to " ^ string_of_int current_size ^
        ", past the allowed growth of " ^ string_of_int allowed_growth ^
        " (see net_rewrite_growth_factor, net_rewrite_growth_offset).\nThe last step rewrote\n  " ^
        show t ^ "\nto\n  " ^ show residue ^
        "\nrules applicable at that subterm:\n" ^ rule_text)
  end;


(** traversal **)

type options =
  {size_check: bool option,
   step_limit: int option option,
   growth_factor: int option,
   growth_offset: int option} option;

(*Built-in defaults: the bottom of the three layers described in the signature.

  CAUTION on the step limit.  `go' below is NOT tail recursive, so a divergence that
  actually reaches the limit has that many nested frames on the ML stack.  Measured:
  survival at ten million is not deterministic -- it depends on what the session has
  already done -- and even when it survives the report arrives after minutes, which
  for a backstop meant to stop an agent waiting on a hung rewrite is barely better
  than the hang.  Hence the value below rather than something larger.  Numbers in
  NET_REWRITE_PLAN.md.*)
val default_size_check = true;
val default_step_limit = SOME 4000000;

val default_options: options = NONE;
(*Every guard off: no step limit, no growth bound.  NOTHING then stops a divergent
  rule set -- a cycle runs until the ML stack gives out, which surfaces as
  "Unable to increase stack - interrupting thread" / Interrupt_Breakdown, aborts
  the enclosing theory, and cannot be pre-empted by `Timeout.apply'.  Its intended
  use is measurement: subtracting the guards from the total to time the traversal
  on its own.*)
val no_check: options =
  SOME {size_check = SOME false, step_limit = SOME NONE,
        growth_factor = NONE, growth_offset = NONE};

(*Resolve the three layers.  See the signature for the precedence rule.*)
fun resolve ctxt (opts: options) =
  let
    fun field sel dflt =
      (case opts of SOME r => (case sel r of SOME v => v | NONE => dflt) | NONE => dflt);
  in
    {size_check = field #size_check default_size_check,
     step_limit = field #step_limit default_step_limit,
     growth_factor = field #growth_factor (Config.get ctxt growth_factor),
     growth_offset = field #growth_offset (Config.get ctxt growth_offset)}
  end;

(*L4 AND L5, BUILT ONCE AND SHARED BY BOTH TRAVERSALS.  `before_step' is asked
  before a step is attempted; `after_step' is told what the step replaced and what
  it produced, and is called only for steps that really happened.  Everything is in
  terms of `term', which is why `DIVERGES' carries a term.*)
fun make_guard opts ctxt0 t0 =
  let
    val {size_check, step_limit, growth_factor = gfactor, growth_offset = goffset} =
      resolve ctxt0 opts;

    val remaining = Unsynchronized.ref (the_default ~1 step_limit);
    val bounded = is_some step_limit;

    (*L5 state.  `input_size' is measured once; `grown' is the running sum of
      size(residue) - size(redex), which by the identity documented at the top of
      this file equals size(current whole term) - input_size.*)
    val input_size = if size_check then Term.size_of_term t0 else 0;
    val allowed_growth = if size_check then gfactor * input_size + goffset else 0;
    val grown = Unsynchronized.ref 0;

    fun before_step t1 =
      if bounded andalso ! remaining <= 0
      then raise DIVERGES (Step_Limit (the step_limit), t1) else ();

    fun after_step (t1, t2) =
      (remaining := ! remaining - 1;
       if size_check then
         let
           val delta = Term.size_of_term t2 - Term.size_of_term t1;
           val _ = grown := ! grown + delta;
         in
           if ! grown > allowed_growth then
             raise DIVERGES (Growth {input_size = input_size,
               current_size = input_size + ! grown, allowed_growth = allowed_growth,
               residue = t2}, t1)
           else ()
         end
       else ());
  in {before_step = before_step, after_step = after_step} end;

(*A FORK of `Conv.sub_conv' (Pure/conv.ML:131), threading a skeleton and the two
  guards.  Three reasons the original cannot be used: its callback takes only a
  context, so there is nowhere to put the skeleton; it is `comb_conv (conv ctxt)',
  which gives the function part and the argument part the SAME conversion, where
  the two halves need DIFFERENT skeletons; and the descent must contract a beta
  redex BEFORE descending, charged against the guards -- which live inside
  `bottom_fixpoint_gen_conv', so they have to be threaded in as an argument
  (`(bef, aft)' below), or the two layers diverge at different moments.

  Two things kept from the original that a reviewer should check first: NO case
  analysis on the shape of the term (the three branches are "application",
  "abstraction", "neither" -- `Pure.imp' / `Pure.all' / `&&&' are not mentioned, so a
  connective the caller's own rules introduce is descended into like anything else);
  and the EXTENDED context that `Conv.abs_conv' hands back, which is what the body
  must be traversed under.  See the header for what dropping the latter costs.

  The beta branch dispatches BEFORE the `else_conv' chain on purpose:
  `Conv.combination_conv' SUCCEEDS on a redex, so a branch placed after it would
  never run -- the redex would be descended into instead of contracted first, and
  the call-by-name property (a discarded divergent argument terminates) would be
  silently lost.  After the contraction the result is re-scanned under `skel0',
  mirroring more_pattern.ML:73-75.

  Fed `skel0' and inert guards this degenerates to `Conv.sub_conv' plus eager
  beta contraction.*)
fun sub_conv_orig conv skel ctxt =
  Conv.combination_conv (conv (skel_fun skel) ctxt) (conv (skel_arg skel) ctxt)
  else_conv
  Conv.abs_conv (fn (_, ctxt') => conv (skel_body skel) ctxt') ctxt
  else_conv
  Conv.all_conv;

fun sub_conv_skel (bef, aft) conv skel ctxt ct =
  (case Thm.term_of ct of
     Abs _ $ _ =>
       let
         val _ = bef (Thm.term_of ct);
         val eq = Thm.beta_conversion false ct;
         val ct2 = Thm.rhs_of eq;
         val _ = aft (Thm.term_of ct, Thm.term_of ct2);
        in Thm.transitive eq (conv skel0 ctxt ct2) end
   | _ => sub_conv_orig conv skel ctxt ct);

(*the same for the `Reference' descent, over `Conv.sub_conv' itself*)
fun sub_conv_ref (bef, aft) cv ctxt ct =
  (case Thm.term_of ct of
     Abs _ $ _ =>
       let
         val _ = bef (Thm.term_of ct);
         val eq = Thm.beta_conversion false ct;
         val ct2 = Thm.rhs_of eq;
         val _ = aft (Thm.term_of ct, Thm.term_of ct2);
        in Thm.transitive eq (cv ctxt ct2) end
   | _ => Conv.sub_conv cv ctxt ct);

datatype mode = Reference | No_Skeleton | Skeleton;

(*Bottom-up; after a successful step at a node, re-traverse the *result* bottom-up
  in place.  Compare Conv.bottom_conv, which is

      sub_conv (bottom_conv conv) ctxt then_conv conv ctxt

  i.e. identical except that it does not come back after `conv ctxt' fires.

  `sub_conv_skel' / `sub_conv_ref' cannot fail (their fallback chain ends in
  `all_conv' and their beta branch always succeeds) and the right operand is
  wrapped in `Conv.try_conv', so the traversal itself never fails: on a term with
  no redex it returns a reflexive theorem.

  `Conv.changed_conv' is load-bearing, not decoration.  A conversion may *succeed*
  and still return a reflexive theorem -- `Conv.rewr_conv' does exactly that for a
  rule such as `?x == cc' applied to `cc'.  Without the guard, that "success"
  triggers another traversal of an unchanged term, which succeeds again, for ever.
  Measured: it exhausts the ML stack and kills the thread.  With the guard, a step
  that changes nothing counts as no step, which is also the right reading of
  "rewrite to a fixpoint".

  SHAPE OF THE RECURSION -- a known defect, left as it is pending a decision.  The
  recursive call sits in the ARGUMENT position of `Thm.transitive' on the last line,
  so it is not a tail call: stack depth AND live set both grow with the number of
  steps, and GC time grows superlinearly with them.  A tail-recursive accumulator
  prototype returning the same theorem is flat at ~0.8us/step with GC at ~1%; this
  shape degrades to ~1.8us/step with GC exceeding the compute time.  Since the step
  limit is the only thing between an oscillating rule set and an unbounded run, this
  decides how usable that backstop is.  Numbers in NET_REWRITE_PLAN.md.*)

(*One conv-level traversal, three ways in.  The guards are the shared ones and are
  the same whichever descent runs; only the shape of the descent differs.*)
fun bottom_fixpoint_gen_conv mode opts (step: Proof.context -> skel_conv) ctxt0 ct0 =
  let
    val {before_step, after_step} = make_guard opts ctxt0 (Thm.term_of ct0);

    (*one step at this node, with both guards, or `CTERM' if there is no step here.
      The `Conv.changed_conv' treatment is unchanged and still load-bearing: a
      conversion may succeed and return a reflexive theorem, and that must count as
      no step at all -- see the note below.*)
    fun accounted_step ctxt ct1 =
      let
        val _ = before_step (Thm.term_of ct1);
        val (eq, skel') = step ctxt ct1;
        val _ = if Thm.is_reflexive eq then raise CTERM ("changed_conv", [ct1]) else ();
        val ct2 = Thm.rhs_of eq
          handle TERM _ =>
            (*a caller-supplied step returned a non-equation; anything in
              THM/CTERM/TERM/TYPE would be swallowed by the surrounding
              `try_conv' as "no rewrite here"*)
            raise Fail ("Merely_Rewrite: step returned a non-equation: " ^
              Thm.string_of_thm ctxt eq);
        val _ = after_step (Thm.term_of ct1, Thm.term_of ct2);
      in (eq, ct2, skel') end;

    (*the step position: a redex the descent's reassembly has just built (a rule
      rewrote the function part to an abstraction) is contracted as one accounted
      step, `skel0' so the result is re-scanned -- more_pattern.ML:67's counterpart*)
    fun step_at ctxt ct1 =
      (case Thm.term_of ct1 of
         Abs _ $ _ =>
           let
             val _ = before_step (Thm.term_of ct1);
             val eq = Thm.beta_conversion false ct1;
             val ct2 = Thm.rhs_of eq;
             val _ = after_step (Thm.term_of ct1, Thm.term_of ct2);
            in (eq, ct2, skel0) end
       | _ => accounted_step ctxt ct1);

    (*the traversal as it was before skeletons existed; kept as the oracle the other
      one is compared against, and to be deleted once that comparison is over.*)
    fun go_ref ctxt ct =
      (sub_conv_ref (before_step, after_step) go_ref ctxt
         then_conv
       Conv.try_conv (fn ct1 =>
         let val (eq, ct2, _) = step_at ctxt ct1
         in Thm.transitive eq (go_ref ctxt ct2) end)) ct;

    (*the same, with the skeleton threaded through.  A hole is passed over with a
      reflexive theorem; `then_conv' short-circuits on one, so a passed-over subtree
      costs one `Thm.reflexive' and no kernel inference above it either.*)
    fun go skel ctxt ct =
      if is_hole skel then Thm.reflexive ct
      else
        (sub_conv_skel (before_step, after_step) go skel ctxt
           then_conv
         Conv.try_conv (fn ct1 =>
           let val (eq, ct2, skel') = step_at ctxt ct1
           in Thm.transitive eq (go skel' ctxt ct2) end)) ct;
  in
    (case mode of
      Reference => go_ref ctxt0 ct0
    | _ => go skel0 ctxt0 ct0)
  end;

fun bottom_fixpoint_skel_conv opts step = bottom_fixpoint_gen_conv Skeleton opts step;

fun bottom_fixpoint_conv_mode mode opts cv =
  bottom_fixpoint_gen_conv mode opts (fn ctxt => fn ct => (cv ctxt ct, skel0));

fun bottom_fixpoint_conv opts cv = bottom_fixpoint_conv_mode No_Skeleton opts cv;


(** the same traversal over plain terms **)

(*`NONE' means "nothing changed here", which is what a reflexive theorem means at the
  conv layer.  Compare `go' above line for line: the guards are the same object, the
  skeleton discipline is the same three projections and the same `is_hole', and the
  order of business at a node -- descend, then step, then re-descend the result under
  the new skeleton -- is the same.  What differs: nothing is proved, and the binder
  bookkeeping is a threaded `bvs' list where the conv layer extends its context.
  `ctxt0' itself no longer travels with the traversal -- it is captured once and
  handed to the step unchanged, because nothing extends it any more.*)
fun bottom_fixpoint_gen_term mode opts (step: Proof.context -> skel_term) ctxt0 bvs0 t0 =
  let
    val {before_step, after_step} = make_guard opts ctxt0 t0;

    (*THE ENTRY ASSERTION -- the single check the loose-bound contract in the
      signature promises: every loose `Bound' of the input has a `bvs' entry.
      Every TRAVERSAL passes through here whichever mode and skeleton variant it
      runs, so `rewrite_term', `rewrite_term_bvs' and the whole
      `bottom_fixpoint_*' family are covered.  The SINGLE-STEP entries are not:
      they are one node with no traversal, and checking there would rescan the
      term at every node.  `Fail', not TERM/TYPE: nothing downstream may read it
      as "no rewrite here".*)
    val _ =
      (case filter (fn i => i >= length bvs0) (Term.loose_bnos t0) of
        [] => ()
      | is =>
          raise Fail ("Merely_Rewrite: loose Bound " ^
            commas (map (fn i => "B." ^ string_of_int i) is) ^
            " without a bvs entry (bvs has " ^ string_of_int (length bvs0) ^
            " entries); the caller owes rewrite_term_bvs one entry per binder \
            \the input sits under"));

    fun accounted_step bvs t1 =
      (before_step t1;
       (case step ctxt0 bvs t1 of
         NONE => NONE
       | SOME (t2, skel') =>
           (*a step that changes nothing counts as no step, exactly as
             `Conv.changed_conv' decides at the conv layer*)
           if t1 aconv t2 then NONE
           else (after_step (t1, t2); SOME (t2, skel'))));

    (*the step position, `accounted_step' behind a beta clause -- see the conv
      layer's `step_at' for what it catches and why the guards are charged*)
    fun step_at _ (t1 as Abs (_, _, body) $ u) =
          (before_step t1;
           let val t2 = Term.subst_bound (u, body); val _ = after_step (t1, t2)
            in SOME (t2, skel0) end)
      | step_at bvs t = accounted_step bvs t;

    (*In the NONE branch below, `step_at's beta clause is provably dead: `sub'
      contracts a redex in its first clause, so a term `sub' returns NONE on is
      never a redex.  It is kept as an invariant guard, not live logic.*)
    fun go skel bvs t =
      if is_hole skel then NONE
      else
        (case sub skel bvs t of
          SOME t1 =>
            (case step_at bvs t1 of
              SOME (t2, skel') => SOME (perhaps (go skel' bvs) t2)
            | NONE => SOME t1)
        | NONE =>
            (case step_at bvs t of
              SOME (t1, skel') => SOME (perhaps (go skel' bvs) t1)
            | NONE => NONE))

    (*the term-level `sub_conv_skel'; its first clause is the descent-position beta
      of more_pattern.ML:73-75 -- contract, then re-scan the contraction under
      `skel0', and never descend into a redex's own subterms (call-by-name).
      Going under a binder PUSHES it onto `bvs' and leaves the body untouched:
      nothing is opened, nothing is re-abstracted, so there is no fresh name to
      clash and nothing a rule-supplied binder could capture (the substituter
      lifts by landing depth).*)
    and sub _ bvs (t1 as Abs (_, _, body) $ u) =
          (before_step t1;
           let val t2 = Term.subst_bound (u, body); val _ = after_step (t1, t2)
            in SOME (perhaps (go skel0 bvs) t2) end)
      | sub skel bvs (t $ u) =
          (case (go (skel_fun skel) bvs t, go (skel_arg skel) bvs u) of
            (SOME t', SOME u') => SOME (t' $ u')
          | (SOME t', NONE) => SOME (t' $ u)
          | (NONE, SOME u') => SOME (t $ u')
          | (NONE, NONE) => NONE)
      | sub skel bvs (Abs (a, T, b)) =
          Option.map (fn b' => Abs (a, T, b'))
            (go (skel_body skel) ((a, T) :: bvs) b)
      | sub _ _ _ = NONE;

    fun go_ref bvs t =
      (case sub_ref bvs t of
        SOME t1 =>
          (case step_at bvs t1 of
            SOME (t2, _) => SOME (perhaps (go_ref bvs) t2)
          | NONE => SOME t1)
      | NONE =>
          (case step_at bvs t of
            SOME (t1, _) => SOME (perhaps (go_ref bvs) t1)
          | NONE => NONE))

    and sub_ref bvs (t1 as Abs (_, _, body) $ u) =
          (before_step t1;
           let val t2 = Term.subst_bound (u, body); val _ = after_step (t1, t2)
            in SOME (perhaps (go_ref bvs) t2) end)
      | sub_ref bvs (t $ u) =
          (case (go_ref bvs t, go_ref bvs u) of
            (SOME t', SOME u') => SOME (t' $ u')
          | (SOME t', NONE) => SOME (t' $ u)
          | (NONE, SOME u') => SOME (t $ u')
          | (NONE, NONE) => NONE)
      | sub_ref bvs (Abs (a, T, b)) =
          Option.map (fn b' => Abs (a, T, b')) (go_ref ((a, T) :: bvs) b)
      | sub_ref _ _ = NONE;
  in
    perhaps (case mode of Reference => go_ref bvs0 | _ => go skel0 bvs0) t0
  end;

fun bottom_fixpoint_skel_term opts step = bottom_fixpoint_gen_term Skeleton opts step;

fun bottom_fixpoint_term_mode mode opts rew =
  bottom_fixpoint_gen_term mode opts
    (fn ctxt => fn bvs => fn t => Option.map (rpair skel0) (rew ctxt bvs t));

fun bottom_fixpoint_term opts rew = bottom_fixpoint_term_mode No_Skeleton opts rew;


(** entry points **)

(*PROTOTYPE ONLY: the explicit three-way switch the comparison is built on.*)
fun rewrite_conv_mode Skeleton opts net = bottom_fixpoint_skel_conv opts (rewrs_net_skel_conv net)
  | rewrite_conv_mode mode opts net = bottom_fixpoint_conv_mode mode opts (rewrs_net_conv net);

fun rewrite_term_mode Skeleton opts net = bottom_fixpoint_skel_term opts (rewrs_net_skel_term net)
  | rewrite_term_mode mode opts net = bottom_fixpoint_term_mode mode opts (rewrs_net_term net);

(*Skeleton pruning is not a knob.  With conditions (a), (b) and (c) in place it does
  not change what is produced -- only how many nodes are visited on the way -- so
  there is nothing for a caller to choose.  The three-way `mode' switch below it
  exists for the correctness comparison and is test-only.*)
fun rewrite_conv_options opts net ctxt = rewrite_conv_mode Skeleton opts net ctxt;
fun rewrite_conv net = rewrite_conv_options default_options net;
fun rewrite_cterm net ctxt = Thm.rhs_of o rewrite_conv net ctxt;
fun rewrite_rule net ctxt = Conv.fconv_rule (rewrite_conv net ctxt);

fun rewrite_term_bvs_options opts net ctxt = rewrite_term_mode Skeleton opts net ctxt;
fun rewrite_term_bvs net = rewrite_term_bvs_options default_options net;
fun rewrite_term_options opts net ctxt = rewrite_term_bvs_options opts net ctxt [];
fun rewrite_term net = rewrite_term_options default_options net;


end;
