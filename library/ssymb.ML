(*  Title:  library/ssymb.ML

Runtime symbols: identifiers interned per process, represented as bijective
base-6 numerals over type `symbol` (SSymb.thy).  The numeral of an identifier is
its first-come allocation order, so it is meaningful in this process only.
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

end

structure Phi_Tool_Symbol : PHI_TOOL_SYMBOL = struct

val symbolT = \<^typ>\<open>symbol\<close>
val digits = [\<^const_name>\<open>SSymb.A\<close>, \<^const_name>\<open>SSymb.B\<close>, \<^const_name>\<open>SSymb.C\<close>,
              \<^const_name>\<open>SSymb.D\<close>, \<^const_name>\<open>SSymb.E\<close>, \<^const_name>\<open>SSymb.F\<close>]
val zero = Const (\<^const_name>\<open>SSymb.Z\<close>, symbolT)

(*bijective base 6: n = 6 r + k with k in 1..6, written `digit_k (encode r)`*)
fun encode 0 = zero
  | encode n =
      let val k = (n - 1) mod 6 + 1
       in Const (nth digits (k - 1), symbolT --> symbolT) $ encode ((n - k) div 6) end

fun decode (Const (\<^const_name>\<open>SSymb.Z\<close>, _)) = SOME 0
  | decode (Const (name, _) $ x) =
      (case find_index (fn d => d = name) digits
         of ~1 => NONE
          | k => Option.map (fn r => 6 * r + k + 1) (decode x))
  | decode _ = NONE

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
