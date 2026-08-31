theory SSymb
  imports Main Performant_Isabelle_ML.Performant_Isabelle_ML
    \<comment> \<open>Main first: a theory's data is merged from its parents in order, and the
      simpset keeps the FIRST parent's rule-preprocessing (\<open>mk_rews\<close>); a Pure-based
      parent ahead of a HOL-based one leaves the simplifier unable to use HOL facts.
      Importing Performant_Isabelle_ML here, behind Main, gives every theory below a
      single HOL-first parent instead of leaving the order to each of them.\<close>
begin

section \<open>Symbol Identifier unique in Isabelle Runtime and Its Persistent Image\<close>

text \<open>A symbol is an identifier interned at runtime.  Its term representation is a
  bijective base-6 numeral over \<open>symbol\<close> itself: \<open>Z\<close> is 0 and the digit constructors
  \<open>A\<close> \<dots> \<open>F\<close> stand for \<open>6x+1\<close> \<dots> \<open>6x+6\<close>, so every natural number has exactly one
  representation, e.g. \<open>A (B Z)\<close> = 6*2+1 = 13.  When the runtime system uses N
  symbols in total, a representation consumes at most \<open>1 + 2 log\<^sub>6 N\<close> terms, and the
  numeral is the symbol -- there is no wrapper constant.

  The numeral is allocated per process, so it must never be persisted: anything that
  leaves the process (serializers, hashers) goes through \<open>Phi_Tool_Symbol.dest_symbol\<close>
  and carries the identifier instead.

  The seven constant names are hidden (\<open>hide_const (open)\<close>), as the short names would
  shadow ordinary variables \<open>A\<close>, \<open>B\<close>, \<open>Z\<close> \<dots> in every theory importing this one.\<close>

typedef symbol = \<open>UNIV::nat set\<close>
  morphisms Abs_symbol mk_symbol
  by auto

hide_const Abs_symbol

setup_lifting type_definition_symbol

declare mk_symbol_inject[simplified, iff]

text \<open>No \<open>mk_symbol_cong\<close> here any more (author ruling 2026-08-31): the old
  representation wrapped an interned NUMERAL in \<open>mk_symbol\<close>, and a reflexive cong
  froze that argument so simplification (e.g. \<open>1 \<leadsto> Suc 0\<close>) could not break the
  shape the printer and the ML recogniser matched on.  The digit-chain
  representation has no numeral to protect, \<open>mk_symbol\<close> is the typedef's Abs and
  never appears in ordinary terms, and freezing its argument actively harms the
  one consumer that builds \<open>mk_symbol <numeral>\<close> on purpose -- the guard refuter,
  whose folded arithmetic must evaluate before the model search
  (phi-system, GUARD_NITPICK_FALSIFY_PLAN.md section 26.10).\<close>

lift_definition Z :: symbol is 0 .
lift_definition A :: \<open>symbol \<Rightarrow> symbol\<close> is \<open>\<lambda>x. x * 6 + 1\<close> .
lift_definition B :: \<open>symbol \<Rightarrow> symbol\<close> is \<open>\<lambda>x. x * 6 + 2\<close> .
lift_definition C :: \<open>symbol \<Rightarrow> symbol\<close> is \<open>\<lambda>x. x * 6 + 3\<close> .
lift_definition D :: \<open>symbol \<Rightarrow> symbol\<close> is \<open>\<lambda>x. x * 6 + 4\<close> .
lift_definition E :: \<open>symbol \<Rightarrow> symbol\<close> is \<open>\<lambda>x. x * 6 + 5\<close> .
lift_definition F :: \<open>symbol \<Rightarrow> symbol\<close> is \<open>\<lambda>x. x * 6 + 6\<close> .

text \<open>Deciding equality of two symbols by simplification: injectivity of each digit,
  and disequality of every two distinct digits and of every digit against \<open>Z\<close>.
  A disequality is used by the simplifier in the written orientation only, so each
  is declared in both (\<open>[simp, symmetric, simp]\<close>).

  The three groups are named because a simpset that REPLACES the ambient one (rather
  than extending it) must list them explicitly -- \<open>\<phi>safe_simp\<close> in phi-system decides
  field-name distinctness of named tuples with nothing but these.  Note that the
  \<open>symmetric\<close> attribute leaves the named fact in the flipped orientation; a client
  wanting both writes \<open>name name[symmetric]\<close>.\<close>

lemma symbol_digit_inject[simp]:
  \<open>A x = A y \<longleftrightarrow> x = y\<close>  \<open>B x = B y \<longleftrightarrow> x = y\<close>  \<open>C x = C y \<longleftrightarrow> x = y\<close>
  \<open>D x = D y \<longleftrightarrow> x = y\<close>  \<open>E x = E y \<longleftrightarrow> x = y\<close>  \<open>F x = F y \<longleftrightarrow> x = y\<close>
  by (transfer, simp)+

lemma symbol_digit_distinct[simp, symmetric, simp]:
  \<open>A x \<noteq> B y\<close> \<open>A x \<noteq> C y\<close> \<open>A x \<noteq> D y\<close> \<open>A x \<noteq> E y\<close> \<open>A x \<noteq> F y\<close>
  \<open>B x \<noteq> C y\<close> \<open>B x \<noteq> D y\<close> \<open>B x \<noteq> E y\<close> \<open>B x \<noteq> F y\<close>
  \<open>C x \<noteq> D y\<close> \<open>C x \<noteq> E y\<close> \<open>C x \<noteq> F y\<close>
  \<open>D x \<noteq> E y\<close> \<open>D x \<noteq> F y\<close>
  \<open>E x \<noteq> F y\<close>
  by (transfer, presburger)+

lemma symbol_digit_neq_zero[simp, symmetric, simp]:
  \<open>A x \<noteq> Z\<close> \<open>B x \<noteq> Z\<close> \<open>C x \<noteq> Z\<close> \<open>D x \<noteq> Z\<close> \<open>E x \<noteq> Z\<close> \<open>F x \<noteq> Z\<close>
  by (transfer, simp)+

text \<open>Folding a digit chain back into the wrapped-numeral shape \<open>mk_symbol n\<close>: a model
  finder (Nitpick) copes with \<open>mk_symbol 13\<close> -- one literal under the type's Abs --
  but not with \<open>A (B Z)\<close>, whose digit functions it must interpret as \<open>6x+k\<close> inside a
  tiny nat scope.  NOT simp rules: the digit chain is the representation everywhere
  else (printing recognises the digit constants), so a consumer that wants numerals
  adds these itself, right before the term leaves for the model finder.\<close>

lemma symbol_digit_eval:
  \<open>Z = mk_symbol 0\<close>
  \<open>A (mk_symbol n) = mk_symbol (n * 6 + 1)\<close>  \<open>B (mk_symbol n) = mk_symbol (n * 6 + 2)\<close>
  \<open>C (mk_symbol n) = mk_symbol (n * 6 + 3)\<close>  \<open>D (mk_symbol n) = mk_symbol (n * 6 + 4)\<close>
  \<open>E (mk_symbol n) = mk_symbol (n * 6 + 5)\<close>  \<open>F (mk_symbol n) = mk_symbol (n * 6 + 6)\<close>
  by (simp_all add: Abs_symbol_inject[symmetric] Z.rep_eq A.rep_eq B.rep_eq C.rep_eq
                    D.rep_eq E.rep_eq F.rep_eq mk_symbol_inverse)

ML_file \<open>../library/ssymb_syntax.ML\<close>
ML_file \<open>../library/ssymb.ML\<close>

hide_const (open) Z A B C D E F

nonterminal "\<phi>_symbol_"

syntax "_ID_SYMBOL_" :: \<open>id \<Rightarrow> \<phi>_symbol_\<close> ("_")
       "_LOG_EXPR_SYMBOL_" :: \<open>logic \<Rightarrow> \<phi>_symbol_\<close> ("SYMBOL'_VAR'(_')")
       "_MK_SYMBOL_" :: \<open>\<phi>_symbol_ \<Rightarrow> symbol\<close> ("SYMBOL'(_')")

ML \<open>
structure Phi_Tool_Symbol = struct
open Phi_Tool_Symbol

fun parse (Free (id, _)) = Phi_Tool_Symbol.mk_symbol id
  | parse tm = (@{print} tm; error "Expect an identifier.")

(*The syntax-level twin of dest_symbol: the term carries \<^const_syntax> names.*)
local
  val digits = [\<^const_syntax>\<open>SSymb.A\<close>, \<^const_syntax>\<open>SSymb.B\<close>, \<^const_syntax>\<open>SSymb.C\<close>,
                \<^const_syntax>\<open>SSymb.D\<close>, \<^const_syntax>\<open>SSymb.E\<close>, \<^const_syntax>\<open>SSymb.F\<close>]
  fun dest (Const (\<^const_syntax>\<open>SSymb.Z\<close>, _)) = SOME 0
    | dest (Const (name, _) $ x) =
        (case find_index (fn d => d = name) digits
           of ~1 => NONE
            | k => Option.map (fn r => 6 * r + k + 1) (dest x))
    | dest _ = NONE
in
fun decode_synt tm = Option.map Phi_Tool_Symbol.revert_symbol1 (dest tm)
end

(*Pretty-printing a symbol: the identifier as a free variable when the syntax term is
  a literal symbol (an unregistered literal is an error, no such term may exist), the
  term itself otherwise.*)
fun print tm =
  case decode_synt tm
    of SOME id => Free (id, dummyT)
     | NONE => tm

end
\<close>

parse_translation \<open>[
  (\<^syntax_const>\<open>_ID_SYMBOL_\<close>, (fn ctxt => fn [x] => Phi_Tool_Symbol.parse x)),
  (\<^syntax_const>\<open>_LOG_EXPR_SYMBOL_\<close>, (fn ctxt => fn [x] =>
        Const (\<^syntax_const>\<open>_constrain\<close>, dummyT) $ x $ Const(\<^type_syntax>\<open>symbol\<close>, dummyT))),
  (\<^syntax_const>\<open>_MK_SYMBOL_\<close>, (fn ctxt => fn [x] => x))
]\<close>

print_translation \<open>
  let fun tr name = (name, fn _ => fn args =>
        let val tm = Term.list_comb (Const (name, dummyT), args)
         in case Phi_Tool_Symbol.decode_synt tm
              of SOME id => Const (\<^syntax_const>\<open>_MK_SYMBOL_\<close>, dummyT) $ Free (id, dummyT)
               | NONE => raise Match
        end)
   in map tr [\<^const_syntax>\<open>SSymb.Z\<close>, \<^const_syntax>\<open>SSymb.A\<close>, \<^const_syntax>\<open>SSymb.B\<close>,
              \<^const_syntax>\<open>SSymb.C\<close>, \<^const_syntax>\<open>SSymb.D\<close>, \<^const_syntax>\<open>SSymb.E\<close>,
              \<^const_syntax>\<open>SSymb.F\<close>]
  end
\<close>

ML \<open>@{term \<open>SYMBOL(xxx)\<close>}\<close>

end
