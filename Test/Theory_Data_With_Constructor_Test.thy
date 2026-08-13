(*
  Tests for Theory_Data_With_Constructor, following the numbering of
  THEORY_DATA_WITH_CONSTRUCTOR_PLAN.md §5.

  The instance's value is a string spelling out the whole construction:
  construct [(p1, v1), (p2, v2)] = "C(p1=v1, p2=v2)" (base names).  Every
  expected value is computed by the same function, so the assertions state
  the contract ("value = construct(parents with their values)") directly.

  The functor applications sit in the first ML block; the assertions in the
  second.  This split is REQUIRED for test 6: \<^theory> is the static
  compile-time context of its block and does not see the same block's
  Theory.setup.
*)
theory Theory_Data_With_Constructor_Test
  imports "../Performant_Isabelle_ML"
begin

ML \<open>
val tdwc_counter1 = Unsynchronized.ref 0
val tdwc_counter2 = Unsynchronized.ref 0

fun tdwc_value args =
  "C(" ^ commas (map (fn (thy, v) => Context.theory_base_name thy ^ "=" ^ v) args) ^ ")"

structure TDWC_1 = Theory_Data_With_Constructor(
  type T = string
  val empty = "E"
  fun construct args = (Unsynchronized.inc tdwc_counter1; tdwc_value args))

structure TDWC_2 = Theory_Data_With_Constructor(
  type T = string
  val empty = "e"
  fun construct args = (Unsynchronized.inc tdwc_counter2; tdwc_value args))
\<close>

ML \<open>
local

fun check msg b =
  if b then () else error ("Theory_Data_With_Constructor_Test: " ^ msg)

fun mk name parents = Theory.begin_theory (name, Position.none) parents

val thyT = \<^theory>          (* the declaring theory: in scope, a draft *)
val pure = Theory.get_pure ()  (* out of scope *)

(* 6: declaring theory constructed, from (parent, empty) pairs only *)
val parents0 = Theory.parents_of thyT
val _ = check "(6) declaring theory constructed"
  (TDWC_1.get thyT = tdwc_value (map (fn p => (p, "E")) parents0))
val _ = check "(6b) exactly one construction for the declaring theory"
  (! tdwc_counter1 = 1 andalso ! tdwc_counter2 = 1)

(* 7: out-of-scope theory reads empty *)
val _ = check "(7) out-of-scope theory reads empty"
  (TDWC_1.get pure = "E")

(* 1: single parent reconstructs *)
val vT = TDWC_1.get thyT
val pA = mk "A" [thyT]
val vA = TDWC_1.get pA
val _ = check "(1) single parent reconstructs"
  (vA = tdwc_value [(thyT, vT)])
val _ = check "(1b) not inherited verbatim" (vA <> vT)

(* 11: put does not trigger reconstruction *)
val n11 = ! tdwc_counter1
val pA' = TDWC_1.put "B0" pA
val _ = check "(11) put does not reconstruct"
  (TDWC_1.get pA' = "B0" andalso ! tdwc_counter1 = n11)

(* 2: mid-theory put reaches the child *)
val c2 = mk "C2" [pA']
val _ = check "(2) put value reaches the child's construct"
  (TDWC_1.get c2 = tdwc_value [(pA', "B0")])

(* 5: exactly one construction per begin *)
val n5 = ! tdwc_counter1
val _ = mk "E1" [pA']
val _ = check "(5) exactly one construction per begin"
  (! tdwc_counter1 = n5 + 1)

(* 3: two parents, in parents_of order *)
val pX = mk "X" [thyT]
val pY = mk "Y" [thyT]
val vX = TDWC_1.get pX
val vY = TDWC_1.get pY
val cXY = mk "XY" [pX, pY]
val _ = check "(3) two parents in order"
  (TDWC_1.get cXY = tdwc_value [(pX, vX), (pY, vY)])

(* 4: diamond -- construct sees the parents, not the ancestors *)
val pDA = mk "DA" [thyT]
val pDB = mk "DB" [pDA]
val pDC = mk "DC" [pDA]
val cDD = mk "DD" [pDB, pDC]
val _ = check "(4) diamond passes parents only"
  (TDWC_1.get cDD = tdwc_value [(pDB, TDWC_1.get pDB), (pDC, TDWC_1.get pDC)])

(* 13: make_parents drops an import subsumed by another *)
val cDR = mk "DR" [pDA, pDB]
val _ = check "(13) subsumed import dropped"
  (TDWC_1.get cDR = tdwc_value [(pDB, TDWC_1.get pDB)])

(* 8: same-base-name siblings are told apart *)
val s1 = mk "S" [pX]
val s2 = mk "S" [pY]
val _ = check "(8) same-name siblings"
  (TDWC_1.get s1 = tdwc_value [(pX, vX)] andalso
   TDWC_1.get s2 = tdwc_value [(pY, vY)] andalso
   TDWC_1.get s1 <> TDWC_1.get s2)

(* 9: mixed-scope parents -- the one-carrier (Datatab.default) path.
   pO is hand-built directly over Pure: out of scope, and not subsumed by pX. *)
val pO = mk "O" [pure]
val _ = check "(9a) hand-built Pure child is out of scope"
  (TDWC_1.get pO = "E")
val cM = mk "M" [pX, pO]
val _ = check "(9) out-of-scope parent contributes empty"
  (TDWC_1.get cM = tdwc_value [(pX, vX), (pO, "E")])

(* 10: two instances, one begin, each constructed exactly once *)
val n10a = ! tdwc_counter1
val n10b = ! tdwc_counter2
val c10 = mk "T10" [pX]
val _ = check "(10) both instances constructed exactly once"
  (! tdwc_counter1 = n10a + 1 andalso ! tdwc_counter2 = n10b + 1)
val _ = check "(10b) second instance's value"
  (TDWC_2.get c10 = tdwc_value [(pX, TDWC_2.get pX)])

(* 12: value survives end_theory unchanged *)
val c12 = mk "T12" [pX]
val v12 = TDWC_1.get c12
val c12' = Theory.end_theory c12
val _ = check "(12) value survives end_theory"
  (TDWC_1.get c12' = v12)

in
val _ = writeln "Theory_Data_With_Constructor_Test: all checks passed"
end
\<close>

end
