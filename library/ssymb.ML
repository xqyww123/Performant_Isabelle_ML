(*  Title:  library/ssymb.ML

Runtime symbols: identifiers interned per process, represented as bijective
base-6 numerals over type `symbol` (HOL/SSymb.thy).  The numeral of an identifier
is its first-come allocation order, so it is meaningful in this process only.

Loaded in the Pure half (Performant_Isabelle_ML.thy) so that serializers below
HOL can name it: the file builds and inspects terms structurally and consults no
theory, so the constant names are literals here; SSymb.thy certifies `constants`
against the real declarations.
*)

signature PHI_TOOL_SYMBOL = sig

val mk_symbol : string -> term
val revert_symbol : int -> string option
val revert_symbol1: int -> string

(*SOME identifier iff the term is a literal symbol.  A literal never registered is
  an error, by specification: no such term may exist in the runtime.  Any other
  term, including a digit over a non-literal (a schematic variable, say), is NONE.
  This is the entry point for anything that must not let a numeral leave the
  process -- serializers and hashers.*)
val dest_symbol : term -> string option

(*Every constant this file builds -- zero and the six digits -- for SSymb.thy to
  certify against the declarations.*)
val constants : term list

end

structure Phi_Tool_Symbol : PHI_TOOL_SYMBOL = struct

val symbolT = Type ("SSymb.symbol", [])
val digits = ["SSymb.A", "SSymb.B", "SSymb.C", "SSymb.D", "SSymb.E", "SSymb.F"]
val zero = Const ("SSymb.Z", symbolT)
val digit_consts = map (fn d => Const (d, symbolT --> symbolT)) digits
val constants = zero :: digit_consts

(*bijective base 6: n = 6 r + k with k in 1..6, written `digit_k (encode r)`*)
fun encode 0 = zero
  | encode n =
      let val k = (n - 1) mod 6 + 1
       in nth digit_consts (k - 1) $ encode ((n - k) div 6) end

fun decode t =
  if t aconv zero then SOME 0
  else case t
    of Const (name, _) $ x =>
        (case find_index (fn d => d = name) digits
           of ~1 => NONE
            | k => Option.map (fn r => 6 * r + k + 1) (decode x))
     | _ => NONE

val symbols = Synchronized.var "Phi_Tool_Symbol.symbols"
                {cnt = 0,
                 syms = Symtab.empty : term Symtab.table,
                 lookup = Inttab.empty : string Inttab.table}

fun mk_symbol identifier =
  Synchronized.change_result symbols (fn (data as {cnt, syms, lookup}) =>
    case Symtab.lookup syms identifier
      of SOME tm => (tm, data)
       | NONE =>
          let val tm = encode cnt
           in (tm, {cnt = cnt+1, syms = Symtab.update_new (identifier, tm) syms,
                    lookup = Inttab.update_new (cnt, identifier) lookup}) end)

fun revert_symbol id =
  Inttab.lookup (#lookup (Synchronized.value symbols)) id

fun revert_symbol1 id =
  case revert_symbol id
    of SOME x => x
     | NONE => error ("Phi_Tool_Symbol: bad symbol " ^ string_of_int id)

fun dest_symbol tm = Option.map revert_symbol1 (decode tm)

end
