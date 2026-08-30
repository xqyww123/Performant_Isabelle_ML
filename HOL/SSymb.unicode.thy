theory SSymb
  imports Main Performant_Isabelle_ML.Performant_Isabelle_ML
    ― ‹Main first: a theory's data is merged from its parents in order, and the
      simpset keeps the FIRST parent's rule-preprocessing (‹mk_rews›); a Pure-based
      parent ahead of a HOL-based one leaves the simplifier unable to use HOL facts.
      Importing Performant_Isabelle_ML here, behind Main, gives every theory below a
      single HOL-first parent instead of leaving the order to each of them.›
begin

section ‹Symbol Identifier unique in Isabelle Runtime and Its Persistent Image›

text ‹A symbol is an identifier interned at runtime.  Its term representation is a
  bijective base-6 numeral over ‹symbol› itself: ‹Z› is 0 and the digit constructors
  ‹A› … ‹F› stand for ‹6x+1› … ‹6x+6›, so every natural number has exactly one
  representation, e.g. ‹A (B Z)› = 6*2+1 = 13.  When the runtime system uses N
  symbols in total, a representation consumes at most ‹1 + 2 log₆ N› terms, and the
  numeral is the symbol -- there is no wrapper constant.

  The numeral is allocated per process, so it must never be persisted: anything that
  leaves the process (serializers, hashers) goes through ‹Phi_Tool_Symbol.dest_symbol›
  and carries the identifier instead.

  The seven constant names are hidden (‹hide_const (open)›), as the short names would
  shadow ordinary variables ‹A›, ‹B›, ‹Z› … in every theory importing this one.›

typedef symbol = ‹UNIV::nat set›
  morphisms Abs_symbol mk_symbol
  by auto

hide_const Abs_symbol

setup_lifting type_definition_symbol

declare mk_symbol_inject[simplified, iff]

lemma mk_symbol_cong[cong]:
  ‹mk_symbol A ≡ mk_symbol A› .

lift_definition Z :: symbol is 0 .
lift_definition A :: ‹symbol ⇒ symbol› is ‹λx. x * 6 + 1› .
lift_definition B :: ‹symbol ⇒ symbol› is ‹λx. x * 6 + 2› .
lift_definition C :: ‹symbol ⇒ symbol› is ‹λx. x * 6 + 3› .
lift_definition D :: ‹symbol ⇒ symbol› is ‹λx. x * 6 + 4› .
lift_definition E :: ‹symbol ⇒ symbol› is ‹λx. x * 6 + 5› .
lift_definition F :: ‹symbol ⇒ symbol› is ‹λx. x * 6 + 6› .

text ‹Deciding equality of two symbols by simplification: injectivity of each digit,
  and disequality of every two distinct digits and of every digit against ‹Z›.
  A disequality is used by the simplifier in the written orientation only, so each
  is declared in both (‹[simp, symmetric, simp]›).›

lemma [simp]:
  ‹A x = A y ⟷ x = y›  ‹B x = B y ⟷ x = y›  ‹C x = C y ⟷ x = y›
  ‹D x = D y ⟷ x = y›  ‹E x = E y ⟷ x = y›  ‹F x = F y ⟷ x = y›
  by (transfer, simp)+

lemma [simp, symmetric, simp]:
  ‹A x ≠ B y› ‹A x ≠ C y› ‹A x ≠ D y› ‹A x ≠ E y› ‹A x ≠ F y›
  ‹B x ≠ C y› ‹B x ≠ D y› ‹B x ≠ E y› ‹B x ≠ F y›
  ‹C x ≠ D y› ‹C x ≠ E y› ‹C x ≠ F y›
  ‹D x ≠ E y› ‹D x ≠ F y›
  ‹E x ≠ F y›
  by (transfer, presburger)+

lemma [simp, symmetric, simp]:
  ‹A x ≠ Z› ‹B x ≠ Z› ‹C x ≠ Z› ‹D x ≠ Z› ‹E x ≠ Z› ‹F x ≠ Z›
  by (transfer, simp)+

ML_file ‹../library/ssymb_syntax.ML›
ML_file ‹../library/ssymb.ML›

hide_const (open) Z A B C D E F

nonterminal "φ_symbol_"

syntax "_ID_SYMBOL_" :: ‹id ⇒ φ_symbol_› ("_")
       "_LOG_EXPR_SYMBOL_" :: ‹logic ⇒ φ_symbol_› ("SYMBOL'_VAR'(_')")
       "_MK_SYMBOL_" :: ‹φ_symbol_ ⇒ symbol› ("SYMBOL'(_')")

ML ‹
structure Phi_Tool_Symbol = struct
open Phi_Tool_Symbol

fun parse (Free (id, _)) = Phi_Tool_Symbol.mk_symbol id
  | parse tm = (@{print} tm; error "Expect an identifier.")

(*The syntax-level twin of dest_symbol: the term carries \<^const_syntax> names.*)
local
  val digits = [\<^const_syntax>‹SSymb.A›, \<^const_syntax>‹SSymb.B›, \<^const_syntax>‹SSymb.C›,
                \<^const_syntax>‹SSymb.D›, \<^const_syntax>‹SSymb.E›, \<^const_syntax>‹SSymb.F›]
  fun dest (Const (\<^const_syntax>‹SSymb.Z›, _)) = SOME 0
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
›

parse_translation ‹[
  (\<^syntax_const>‹_ID_SYMBOL_›, (fn ctxt => fn [x] => Phi_Tool_Symbol.parse x)),
  (\<^syntax_const>‹_LOG_EXPR_SYMBOL_›, (fn ctxt => fn [x] =>
        Const (\<^syntax_const>‹_constrain›, dummyT) $ x $ Const(\<^type_syntax>‹symbol›, dummyT))),
  (\<^syntax_const>‹_MK_SYMBOL_›, (fn ctxt => fn [x] => x))
]›

print_translation ‹
  let fun tr name = (name, fn _ => fn args =>
        let val tm = Term.list_comb (Const (name, dummyT), args)
         in case Phi_Tool_Symbol.decode_synt tm
              of SOME id => Const (\<^syntax_const>‹_MK_SYMBOL_›, dummyT) $ Free (id, dummyT)
               | NONE => raise Match
        end)
   in map tr [\<^const_syntax>‹SSymb.Z›, \<^const_syntax>‹SSymb.A›, \<^const_syntax>‹SSymb.B›,
              \<^const_syntax>‹SSymb.C›, \<^const_syntax>‹SSymb.D›, \<^const_syntax>‹SSymb.E›,
              \<^const_syntax>‹SSymb.F›]
  end
›

ML ‹@{term ‹SYMBOL(xxx)›}›

end
