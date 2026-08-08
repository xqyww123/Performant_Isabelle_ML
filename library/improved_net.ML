(*  Title:      Pure/net.ML

Discrimination nets: a data structure for indexing items

From the book
    E. Charniak, C. K. Riesbeck, D. V. McDermott.
    Artificial Intelligence Programming.
    (Lawrence Erlbaum Associates, 1980).  [Chapter 14]

match_term no longer treats lambda abstractions as wildcards; instead they are
encoded as virtual applications and discriminated by body structure.
Terms are automatically beta-eta-normalized on insert/delete/match/unify.  On the
query side the normalization is fused into the descent (`nf_view'): the net stops
at a `Leaf', so normalization stops there too.

MODIFIED BY: Qiyuan Xu

Adding special support for \<open>TYPE\<close> so that the net can efficiently match terms containing explicit
  type annotation.

Lambda abstractions are encoded as virtual applications Const("\<lambda>") $ body.

*)

(*
signature NET = sig
include NET

val insert_typ : ('a * 'a -> bool) -> typ * 'a -> 'a net -> 'a net
val insert_typ_safe : ('a * 'a -> bool) -> typ * 'a -> 'a net -> 'a net
val delete_typ : ('b * 'a -> bool) -> typ * 'b -> 'a net -> 'a net
val delete_typ_safe : ('b * 'a -> bool) -> typ * 'b -> 'a net -> 'a net
val match_typ : 'a net -> typ -> 'a list
val unify_typ : 'a net -> typ -> 'a list

end

structure Net : NET = struct
open Net

fun insert_typ eq (typ,x) = insert_term eq (encode_type typ, x)
fun insert_typ_safe eq (typ,x) = insert_term_safe eq (encode_type typ, x)
fun delete_typ eq (typ,x) = delete_term eq (encode_type typ, x)
fun delete_typ_safe eq (typ,x) = delete_term_safe eq (encode_type typ, x)

fun match_typ net typ 

end
*)


(*A copy of `NET' (Pure/net.ML:16-41) with two changes: `key' is made concrete, so
  that white-box tests can inspect the encoding, and `insert_term_last(_safe)' is
  added.  It is a copy and not an `include'
  because SML will not let a signature re-specify a type the include brought in
  ("Type (key) is already present in this signature").  Re-sync this block if Pure's
  `NET' changes; the ascription at the bottom of this file is what catches drift.*)
signature INET =
sig
  datatype key = CombK | VarK | AtomK of string
  (*beta-eta normalizes its input itself: the bare key agrees with what
    `insert_term' stores, so `lookup net (key_of_term t)' round-trips*)
  val key_of_term: term -> key list
  (*beta-eta normalize if needed: one guard scan, identity on normal terms*)
  val norm: term -> term
  (*normalizes the OUTERMOST shape only -- proper subterms come back untouched
    (`%x. k (%z. ?V z) x' loses its binder, but the inner eta redex stays).
    NOT a normalizer; for the normal form use `Envir.beta_eta_contract'.*)
  val nf_view: term -> term
  val encode_type: typ -> term
  type 'a net
  val empty: 'a net
  val is_empty: 'a net -> bool
  exception INSERT
  val insert: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net
  val insert_term: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  val insert_safe: ('a * 'a -> bool) -> key list * 'a -> 'a net -> 'a net
  val insert_term_safe: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  val insert_term_last: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  val insert_term_last_safe: ('a * 'a -> bool) -> term * 'a -> 'a net -> 'a net
  exception DELETE
  val delete: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net
  val delete_term: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net
  val delete_safe: ('b * 'a -> bool) -> key list * 'b -> 'a net -> 'a net
  val delete_term_safe: ('b * 'a -> bool) -> term * 'b -> 'a net -> 'a net
  val lookup: 'a net -> key list -> 'a list
  val match_term: 'a net -> term -> 'a list
  val unify_term: 'a net -> term -> 'a list
  val entries: 'a net -> 'a list
  val subtract: ('b * 'a -> bool) -> 'a net -> 'b net -> 'b list
  val merge: ('a * 'a -> bool) -> 'a net * 'a net -> 'a net
  val content: 'a net -> 'a list
end;

structure iNet : INET =
struct

datatype key = CombK | VarK | AtomK of string;

(*encode_type -- for indexing purposes*)
fun encode_type (Type (c, Ts)) = Term.list_comb (Const (c, dummyT), map encode_type Ts)
  | encode_type (TFree (a, _)) = Free (a, dummyT)
  | encode_type (TVar (a, _)) = Var (a, dummyT);

(*Keys are preorder lists of symbols -- Combinations, Vars, Atoms.
  Any term whose head is a Var is regarded entirely as a Var.
  Abstractions are encoded as CombK :: AtomK "\<lambda>" :: keys(body),
    i.e. virtual applications Const("\<lambda>") $ body.
*)
(*Eta-contraction is not stable under instantiation: a pattern that cannot contract
  may have instances that can, so the stored key keeps a lambda arc the query key has
  lost and the net reports no candidate for a rule that matches.  Upstream avoids
  this by making every abstraction a wildcard (net.ML:50-51); this does it only where
  needed.  Over-reporting danger is safe -- it only costs discrimination -- and all
  three conjuncts are load-bearing: without `has_var', `%x. G (F x) x' is misjudged.

  PRECONDITION: the term is beta-normal.  The front-rigid branch argues that a
  substitution cannot erase `x' from a front holding no schematic, which is false on
  a beta redex.  `key_of_term' normalizes its own input, which discharges the
  precondition for every key-building entry point (`insert_term',
  `insert_term_last', `delete_term') AND for the bare `key_of_term'+`lookup'
  round-trip -- before it did, `(%x. f x) $ a' keyed as if the argument were not
  there (the Abs branch dispatches on `head_of' and encodes only the abstraction).
  Only the raw-key `insert'/`delete'/`lookup' bypass normalization.
  (`match_term' and `unify_term' build no keys -- they normalize along the descent,
  see `nf_view'.)

  Edit the front-rigid branch last: it is the only clause resting on a negative
  property rather than an impossibility, it is the one already broken once, and
  random testing reaches it in 0.05% of verdicts.  Rationale and measurements:
  INET_FIX_PLAN.md.*)
fun may_unify_typ (T, U) =
      T = dummyT orelse U = dummyT orelse
      (case (T, U) of
          (TVar _, _) => true
        | (_, TVar _) => true
        | (Type (a, Ts), Type (b, Us)) =>
            a = b andalso length Ts = length Us andalso forall may_unify_typ (Ts ~~ Us)
        | (TFree (a, _), TFree (b, _)) => a = b
        | _ => false);

fun ftype (Ts, t) = (fastype_of1 (Ts, t) handle TERM _ => dummyT | General.Subscript => dummyT);
fun btype (Ts, k) = (nth Ts k handle General.Subscript => dummyT);

fun has_var t = Term.exists_subterm is_Var t;

fun may_be_app_ending_in (Ts, t, k) =
      Term.loose_bvar1 (t, k) andalso
      (case t of
          Abs (_, T, b) => may_be_app_ending_in (T::Ts, b, 0) andalso Term.loose_bvar1 (b, k+1)
        | _ => (case strip_comb t of
                   (Var _, _) => true
                 | (_, []) => false
                 | (h, args) =>
                     let val front = Term.list_comb (h, take (length args - 1) args)
                     in may_reduce_to_bound (Ts, List.last args, k) andalso
                        (not (Term.loose_bvar1 (front, k)) orelse has_var front)
                     end))
and may_reduce_to_bound (Ts, t, k) =
      Term.loose_bvar1 (t, k) andalso
      (case t of
          Bound _ => true
        | Abs (_, T, b) => may_be_app_ending_in (T::Ts, b, 0) andalso Term.loose_bvar1 (b, k+1)
        | _ => is_Var (head_of t) andalso may_unify_typ (ftype (Ts, t), btype (Ts, k)));

(*The abstraction \<open>\<lambda>x. body\<close> may lose its binder under some instantiation.*)
fun eta_unstable (Ts, body) = has_var body andalso may_be_app_ending_in (Ts, body, 0);

fun add_key_of_terms (Ts, t, cs) =
  let fun rands (f$t, cs) = CombK :: rands (f, add_key_of_terms(Ts, t, cs))
        | rands (Const(\<^const_name>\<open>Pure.type\<close>, \<^Type>\<open>itself T\<close>), cs) =
                    CombK :: AtomK "T" :: add_key_of_terms (Ts, encode_type T, cs)
        | rands (Const(c,_), cs) = AtomK c :: cs
        | rands (Free(c,_),  cs) = AtomK c :: cs
        | rands (Bound i,  cs)   = AtomK (Name.bound i) :: cs
  in case head_of t of
      Var _ => VarK :: cs
    | Abs (_, T, body) =>
        if eta_unstable (T::Ts, body) then VarK :: cs
        else CombK :: AtomK "\<lambda>" :: add_key_of_terms(T::Ts, body, cs)
    | _     => rands(t,cs)
  end;

(*beta-eta normalize if needed*)
fun norm t =
  if Term.could_beta_contract t orelse Term.could_eta_contract t then Envir.beta_eta_contract t else t;

(*convert a term to a list of keys; normalizes first (see PRECONDITION above)*)
fun key_of_term t = add_key_of_terms ([], norm t, []);

(*Trees indexed by key lists: each arc is labelled by a key.
  Each node contains a list of items, and arcs to children.
  The empty key addresses the entire net.
  Lookup functions preserve order in items stored at same level.
*)
datatype 'a net = Leaf of 'a list
                | Net of {comb: 'a net,
                          var: 'a net,
                          atoms: 'a net Symtab.table};

val empty = Leaf[];
fun is_empty (Leaf []) = true | is_empty _ = false;
val emptynet = Net{comb=empty, var=empty, atoms=Symtab.empty};


(*** Insertion into a discrimination net ***)

exception INSERT;       (*duplicate item in the net*)


(*Adds item x to the list at the node addressed by the keys.
  Creates node if not already present.
  eq is the equality test for items.
  The empty list of keys generates a Leaf node, others a Net node.

  The leaf row decides same-key priority: `insert' head-conses, so among items
  with the same key the LAST inserted is retrieved FIRST (and consumers such as
  `Merely_Rewrite' rely on that as override semantics).  `insert_term_last'
  appends at the leaf instead, for callers that need first-inserted-first.*)
fun gen_insert leaf_add eq (keys,x) net =
  let fun ins1 ([], Leaf xs) =
            if member eq xs x then  raise INSERT  else Leaf(leaf_add (xs, x))
        | ins1 (keys, Leaf[]) = ins1 (keys, emptynet)   (*expand empty...*)
        | ins1 (CombK :: keys, Net{comb,var,atoms}) =
            Net{comb=ins1(keys,comb), var=var, atoms=atoms}
        | ins1 (VarK :: keys, Net{comb,var,atoms}) =
            Net{comb=comb, var=ins1(keys,var), atoms=atoms}
        | ins1 (AtomK a :: keys, Net{comb,var,atoms}) =
            let val atoms' = Symtab.map_default (a, empty) (fn net' => ins1 (keys, net')) atoms;
            in  Net{comb=comb, var=var, atoms=atoms'}  end
  in  ins1 (keys,net)  end;

fun insert eq = gen_insert (fn (xs, x) => x :: xs) eq;

fun insert_term eq (t, x) = insert eq (key_of_term t, x);

fun insert_safe eq entry net = insert eq entry net handle INSERT => net;
fun insert_term_safe eq entry net = insert_term eq entry net handle INSERT => net;

fun insert_term_last eq (t, x) =
  gen_insert (fn (xs, x) => xs @ [x]) eq (key_of_term t, x);
fun insert_term_last_safe eq entry net = insert_term_last eq entry net handle INSERT => net;


(*** Deletion from a discrimination net ***)

exception DELETE;       (*missing item in the net*)

(*Create a new Net node if it would be nonempty*)
fun newnet (args as {comb,var,atoms}) =
  if is_empty comb andalso is_empty var andalso Symtab.is_empty atoms
  then empty else Net args;

(*Deletes item x from the list at the node addressed by the keys.
  Raises DELETE if absent.  Collapses the net if possible.
  eq is the equality test for items. *)
fun delete eq (keys, x) net =
  let fun del1 ([], Leaf xs) =
            if member eq xs x then Leaf (remove eq x xs)
            else raise DELETE
        | del1 (keys, Leaf[]) = raise DELETE
        | del1 (CombK :: keys, Net{comb,var,atoms}) =
            newnet{comb=del1(keys,comb), var=var, atoms=atoms}
        | del1 (VarK :: keys, Net{comb,var,atoms}) =
            newnet{comb=comb, var=del1(keys,var), atoms=atoms}
        | del1 (AtomK a :: keys, Net{comb,var,atoms}) =
            let val atoms' =
              (case Symtab.lookup atoms a of
                NONE => raise DELETE
              | SOME net' =>
                  (case del1 (keys, net') of
                    Leaf [] => Symtab.delete a atoms
                  | net'' => Symtab.update (a, net'') atoms))
            in  newnet{comb=comb, var=var, atoms=atoms'}  end
  in  del1 (keys,net)  end;

fun delete_term eq (t, x) = delete eq (key_of_term t, x);

fun delete_safe eq entry net = delete eq entry net handle DELETE => net;
fun delete_term_safe eq entry net = delete_term eq entry net handle DELETE => net;


(*** Retrieval functions for discrimination nets ***)

(*Return the list of items at the given node, [] if no such node*)
fun lookup (Leaf xs) [] = xs
  | lookup (Leaf _) (_ :: _) = []  (*non-empty keys and empty net*)
  | lookup (Net {comb, ...}) (CombK :: keys) = lookup comb keys
  | lookup (Net {var, ...}) (VarK :: keys) = lookup var keys
  | lookup (Net {atoms, ...}) (AtomK a :: keys) =
      (case Symtab.lookup atoms a of
        SOME net => lookup net keys
      | NONE => []);


(*Skipping a term in a net.  Recursively skip 2 levels if a combination*)
fun net_skip (Leaf _) nets = nets
  | net_skip (Net{comb,var,atoms}) nets =
      fold_rev net_skip (net_skip comb []) (Symtab.fold (cons o #2) atoms (var::nets));


(** Matching and Unification **)

(*conses the linked net, if present, to nets*)
fun look1 (atoms, a) nets =
  (case Symtab.lookup atoms a of
    NONE => nets
  | SOME net => net :: nets);

(*** Normalization fused with the descent: as deep as the net goes and no deeper ***)

val head_norm = Envir.head_norm Envir.init;

(*`nf_view t' returns a term with the same beta-eta normal form as `t' whose
  outermost shape -- `Abs', or rigid/Var head plus number of arguments -- is already
  the shape of that normal form.  Proper subterms are left as they are: the descent
  below normalizes them if and when it reaches them.  No precondition on `t'.

  Beta is upstream's `Envir.head_norm' with the empty environment, called only where
  a spine head is an `Abs'; a plain `Abs' node recurses into its body directly, so a
  lambda tower costs one step per binder, not one head normalization per binder.
  Eta is decided the way `Envir.eta_same' (envir.ML) decides it --
  `Term.is_dependent' on the operator -- except that the operator is beta-normalized
  first: upstream may test the raw operator only because `beta_eta_contract' runs
  `eta_contract' after `beta_norm', and `Envir.beta_norm' is the identity (and a
  single scan) when the operator holds no redex.

  One property carries the eta decision: eta contraction never changes the set of
  loose bound variables of a term, so `is_dependent' answers the same on
  `Envir.beta_norm f' as on the full normal form of `f'.  (A contraction step
  `Abs (x, T, g $ Bound 0) -> decr g' with `g' not depending on `Bound 0' sends
  loose set {i-1 | i in loose(g), i >= 1} to itself.)

  `eta_operator' hands back the very term to be decremented, so a `SOME' always
  carries a term without a loose `Bound 0': `Term.incr_boundvars ~1' can neither
  produce `Bound ~1' nor capture a variable.  Do not change it to return `bool' --
  the raw `f' may still hold the loose `Bound 0' that only beta removes, and
  decrementing that one is a silent bug no differential can see.*)
fun nf_view t =
      (case t of
         Abs (x, T, b) =>
           let val b' = nf_view b in
             (case (case b' of
                      f $ u => if nf_is_bound0 u then eta_operator f else NONE
                    | _ => NONE) of
               SOME f' => nf_view (Term.incr_boundvars ~1 f')     (*eta fires; cascades*)
             | NONE => if pointer_eq (b, b') then t else Abs (x, T, b'))
           end
       | _ =>
           (case head_of t of
              Abs _ => nf_view (head_norm t)          (*spine-head redex: contract it*)
            | _ => t))                                (*rigid or Var head: done, no work*)

(*a non-`Bound' operand may still normalize to one: `(%y. y) x', `%y. x y'*)
and nf_is_bound0 u = (case nf_view u of Bound 0 => true | _ => false)

and eta_operator f =
      let val f' = Envir.beta_norm f
      in if Term.is_dependent f' then NONE else SOME f' end;

(*Return the nodes accessible from the term (cons them before nets)
  "unif" signifies retrieval for unification rather than matching.
  Var in net matches any term.
  Abs or Var in object: if "unif", regarded as wildcard,
                                   else matches only a variable in net.

  INVARIANT: every term handed to `matching' is an `nf_view' result.  All call
  sites establish it: both entry points apply it, `rands' applies it to every
  argument it descends into, and `lambda_arc' hands on a body that came out of
  `nf_view' normalized.  (`encode_type' output holds no `Abs', no `Bound' and no
  redex, so `nf_view' is the identity on it.)*)
fun matching unif t net nets =
      (case net of
         Leaf _ => nets
       | Net {var, ...} =>
           (case head_of t of
              Var _ => if unif then net_skip net nets
                       else var :: nets           (*only matches Var in net*)
  (*If "unif" then a var instantiation in the abstraction could allow
    an eta-reduction, so regard the abstraction as a wildcard.*)
            | Abs (_, _, body) =>
                if unif then net_skip net nets
                else lambda_arc unif body (net, var :: nets)
            | _ => rands unif t (net, var :: nets)))   (*var could match also*)

and rands _ _ (Leaf _, nets) = nets
  | rands unif t (Net {comb, atoms, ...}, nets) =
      (case t of
         f $ u =>
           (case rands unif f (comb, []) of
              [] => nets                       (*no arc wants `u': do not normalize it*)
            | ns => fold_rev (matching unif (nf_view u)) ns nets)
       | Const (\<^const_name>\<open>Pure.type\<close>, \<^Type>\<open>itself T\<close>) =>
           (case rands unif (Const ("T", Term.dummyT)) (comb, []) of
              [] => nets
            | ns => fold_rev (matching unif (encode_type T)) ns nets)
       | Const (c, _) => look1 (atoms, c) nets
       | Free (c, _)  => look1 (atoms, c) nets
       | Bound i      => look1 (atoms, Name.bound i) nets
       | _            => nets)

(*what `rands' does for the virtual application Const("\<lambda>") $ body, except that
  `body' came out of `nf_view' already and must not be normalized a second time --
  else the body of an n-fold nested abstraction is re-normalized n times*)
and lambda_arc unif body (Net {comb = Net {atoms, ...}, ...}, nets) =
      fold_rev (matching unif body) (look1 (atoms, "\<lambda>") []) nets
  | lambda_arc _ _ (_, nets) = nets;

fun extract_leaves l = maps (fn Leaf xs => xs) l;

(*return items whose key could match t*)
fun match_term net t =
    extract_leaves (matching false (nf_view t) net []);

(*return items whose key could unify with t*)
fun unify_term net t =
    extract_leaves (matching true (nf_view t) net []);


(** operations on nets **)

(*subtraction: collect entries of second net that are NOT present in first net*)
fun subtract eq net1 net2 =
  let
    fun subtr (Net _) (Leaf ys) = append ys
      | subtr (Leaf xs) (Leaf ys) =
          fold_rev (fn y => if member eq xs y then I else cons y) ys
      | subtr (Leaf _) (net as Net _) = subtr emptynet net
      | subtr (Net {comb = comb1, var = var1, atoms = atoms1})
            (Net {comb = comb2, var = var2, atoms = atoms2}) =
          subtr comb1 comb2
          #> subtr var1 var2
          #> Symtab.fold (fn (a, net) =>
            subtr (the_default emptynet (Symtab.lookup atoms1 a)) net) atoms2
  in subtr net1 net2 [] end;

fun entries net = subtract (K false) empty net;


(* merge *)

fun cons_fst x (xs, y) = (x :: xs, y);

fun dest (Leaf xs) = map (pair []) xs
  | dest (Net {comb, var, atoms}) =
      map (cons_fst CombK) (dest comb) @
      map (cons_fst VarK) (dest var) @
      maps (fn (a, net) => map (cons_fst (AtomK a)) (dest net)) (Symtab.dest atoms);

(*`fold_rev', not `fold': `dest' emits each leaf in retrieval order and `insert'
  head-conses, so a plain `fold' would rebuild every net2 leaf REVERSED -- after a
  theory merge the EARLIER of two same-key rules declared in one theory would win
  the first match, silently rolling back the override semantics documented at
  `gen_insert' (measured 2026-08-08; Pure's net.ML still carries the plain fold
  with its "FIXME non-canonical merge order!?!").  Folding from the right
  re-inserts each leaf's run oldest-first, so net2's retrieval order survives.
  Relative order BETWEEN net1 items and net2 items stays merge-direction
  dependent -- only same-side order is preserved.*)
fun merge eq (net1, net2) =
  fold_rev (insert_safe eq) (dest net2) net1;

fun content net = map #2 (dest net);

end;

(*Fails to compile if `INET' ever stops covering `NET' -- either because an edit
  here dropped a member, or because Pure added one that was not copied over.  Local
  so the name does not escape; nothing should refer to it.*)
local structure iNet_Covers_NET : NET = iNet in end;
