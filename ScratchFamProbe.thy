theory ScratchFamProbe
  imports Skel_Fuzz
begin

ML \<open>
(*probe: do the F4 families actually occur and actually fire?  (plan gate (\<alpha>))*)
fun lhs_of th = #1 (Logic.dest_equals (Thm.prop_of th));
fun rhs_of th = #2 (Logic.dest_equals (Thm.prop_of th));

fun classify th =
  (case lhs_of th of
    Var _ => "bare"
  | Const _ => "beta"
  | l =>
      (case Term.head_of l of
        Const (c, _) =>
          if c = "ScratchFamProbe.qh2" orelse c = "Skel_Fuzz.qh2" then "qh2"
          else if c = "ScratchFamProbe.qh" orelse c = "Skel_Fuzz.qh" then
            (case l of _ $ Abs (_, _, Var _) => "qh_X" | _ => "qh_P")
          else if Term.exists_Const (fn (c', _) =>
                     c' = "ScratchFamProbe.qh" orelse c' = "Skel_Fuzz.qh") l
          then "rep2"
          else if c = "ScratchFamProbe.f5" orelse c = "Skel_Fuzz.f5" then "fo_f5"
          else "fo"
      | _ => "other"));

(*a first-order f5 rule is a REAL family-4 rule iff its rhs puts a Var under qh*)
fun q4 t =
  (case t of
    Const (c, _) $ Abs (_, _, b) =>
      ((c = "ScratchFamProbe.qh" orelse c = "Skel_Fuzz.qh")
        andalso Term.exists_subterm Term.is_Var b)
      orelse q4 b
  | t $ u => q4 t orelse q4 u
  | Abs (_, _, b) => q4 b
  | _ => false);

(*family distribution over 3000 draws*)
val _ =
  let
    val tally = Symtab.empty |> fold (fn i =>
      let val _ = srand (700000000 + i);
          val th = gen_rule2 i;
          val f = classify th;
          val f = if f = "fo_f5" andalso q4 (rhs_of th) then "fam4(f5+qh-hole)" else f;
      in Symtab.map_default (f, 0) (fn n => n + 1) end) (1 upto 3000);
  in writeln ("rule families in 3000 draws:\n  " ^
       cat_lines (map (fn (k, v) => k ^ " = " ^ string_of_int v) (Symtab.dest tally)))
  end;

(*per family: over n rounds, rounds where a net of ONLY that family's rules
  changes a random input (DIVERGES counts as fired)*)
fun fires fam n =
  let
    fun step i a =
      let
        val _ = srand (800000000 + i);
        val rules = map gen_rule2 (1 upto 9)
          |> filter (fn th =>
               let val f = classify th
               in if fam = "fam4" then f = "fo_f5" andalso q4 (rhs_of th) else f = fam end);
      in
        if null rules then a
        else
          let
            val net = Merely_Rewrite.make_rules rules;
            val input = gen_term (4 + rand 3) [];
            val fired =
              (case Exn.capture (fn () =>
                  Merely_Rewrite.rewrite_term_mode Merely_Rewrite.Skeleton opts net ctxt0 input) () of
                 Exn.Res out => not (out aconv input)
               | Exn.Exn _ => true);
          in (#1 a + (if fired then 1 else 0), #2 a + 1) end
      end;
    val (f, present) = fold step (1 upto n) (0, 0);
  in writeln (fam ^ ": fired " ^ string_of_int f ^ " / present " ^ string_of_int present ^
              " / rounds " ^ string_of_int n) end;

val _ = List.app (fn f => fires f 2000) ["qh_X", "qh2", "rep2", "fam4"];
\<close>

end
