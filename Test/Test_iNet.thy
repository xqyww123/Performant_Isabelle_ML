theory Test_iNet
  imports "../Performant_Isabelle_ML"
begin

ML \<open>
local

open iNet;

val T = dummyT;

fun assert_true msg b = if b then () else error ("FAIL: " ^ msg);

fun assert_eq_set msg expected actual =
  assert_true (msg ^ "\n  expected: " ^ ML_Syntax.print_list ML_Syntax.print_string expected ^
               "\n  actual:   " ^ ML_Syntax.print_list ML_Syntax.print_string actual)
    (eq_set (op =) (expected, actual));

fun assert_eq_keys msg expected actual =
  let fun key_to_string CombK = "CombK"
        | key_to_string VarK = "VarK"
        | key_to_string (AtomK s) = "AtomK " ^ quote s
      val show = ML_Syntax.print_list key_to_string
  in assert_true (msg ^ "\n  expected: " ^ show expected ^
                  "\n  actual:   " ^ show actual)
       (expected = actual)
  end;

val eq_str = (op =) : string * string -> bool;

fun ins (t, x) net = insert_term eq_str (t, x) net;

in

(* Test 1: Key encoding for Abs terms *)
val _ =
  let
    val _ = assert_eq_keys "Abs/Bound 0"
      [CombK, AtomK "\<lambda>", AtomK (Name.bound 0)]
      (key_of_term (Abs("x", T, Bound 0)))
    val _ = assert_eq_keys "Abs/Const f"
      [CombK, AtomK "\<lambda>", AtomK "f"]
      (key_of_term (Abs("x", T, Const("f", T))))
    val _ = assert_eq_keys "Abs/Free y"
      [CombK, AtomK "\<lambda>", AtomK "y"]
      (key_of_term (Abs("x", T, Free("y", T))))
    val _ = assert_eq_keys "nested Abs"
      [CombK, AtomK "\<lambda>", CombK, AtomK "\<lambda>", AtomK (Name.bound 1)]
      (key_of_term (Abs("x", T, Abs("y", T, Bound 1))))
  in writeln "Test 1 (key encoding): pass" end;

(* Test 2: Discrimination power -- different lambda bodies *)
val _ =
  let
    val net = empty
      |> ins (Abs("x", T, Const("f", T)), "f_item")
      |> ins (Abs("x", T, Const("g", T)), "g_item")
    val _ = assert_eq_set "match f" ["f_item"]
      (match_term net (Abs("x", T, Const("f", T))))
    val _ = assert_eq_set "match g" ["g_item"]
      (match_term net (Abs("x", T, Const("g", T))))
  in writeln "Test 2 (discrimination): pass" end;

(* Test 3: Var patterns still match Abs terms *)
val _ =
  let
    val net = empty
      |> ins (Var(("x",0), T), "var_item")
    val result = match_term net (Abs("x", T, Bound 0))
    val _ = assert_eq_set "Var matches Abs" ["var_item"] result
  in writeln "Test 3 (Var matches Abs): pass" end;

(* Test 4: Mixed net -- Abs items found alongside Var-keyed items *)
val _ =
  let
    val net = empty
      |> ins (Var(("x",0), T), "var_item")
      |> ins (Abs("x", T, Const("f", T)), "abs_f")
      |> ins (Abs("x", T, Const("g", T)), "abs_g")
    val result = match_term net (Abs("x", T, Const("f", T)))
    val _ = assert_eq_set "mixed match f" ["abs_f", "var_item"] result
  in writeln "Test 4 (mixed net): pass" end;

(* Test 5: unify_term is conservative (returns all) *)
val _ =
  let
    val net = empty
      |> ins (Var(("x",0), T), "var_item")
      |> ins (Abs("x", T, Const("f", T)), "abs_f")
      |> ins (Abs("x", T, Const("g", T)), "abs_g")
    val result = unify_term net (Abs("x", T, Const("f", T)))
    val _ = assert_eq_set "unify returns all" ["abs_f", "abs_g", "var_item"] result
  in writeln "Test 5 (unify conservative): pass" end;

(* Test 6: Non-lambda terms unchanged *)
val _ =
  let
    val net = empty
      |> ins (Const("f", T), "const_f")
      |> ins (Free("x", T), "free_x")
      |> ins (Const("f", T) $ Free("x", T), "app_fx")
    val _ = assert_eq_set "match const" ["const_f"]
      (match_term net (Const("f", T)))
    val _ = assert_eq_set "match free" ["free_x"]
      (match_term net (Free("x", T)))
    val _ = assert_eq_set "match app" ["app_fx"]
      (match_term net (Const("f", T) $ Free("x", T)))
  in writeln "Test 6 (non-lambda): pass" end;

(* Test 7: Nested lambdas discriminate *)
val _ =
  let
    val net = empty
      |> ins (Abs("x", T, Abs("y", T, Bound 0)), "bound0")
      |> ins (Abs("x", T, Abs("y", T, Bound 1)), "bound1")
    val _ = assert_eq_set "nested bound 0" ["bound0"]
      (match_term net (Abs("x", T, Abs("y", T, Bound 0))))
    val _ = assert_eq_set "nested bound 1" ["bound1"]
      (match_term net (Abs("x", T, Abs("y", T, Bound 1))))
  in writeln "Test 7 (nested lambdas): pass" end;

(* Test 8: Insert and delete round-trip *)
val _ =
  let
    val t = Abs("x", T, Const("f", T))
    val net = empty |> ins (t, "item")
    val net' = delete_term eq_str (t, "item") net
    val _ = assert_true "empty after delete" (is_empty net')
  in writeln "Test 8 (insert/delete round-trip): pass" end;

(* Test 9: Lambda vs non-lambda -- no cross-matching *)
val _ =
  let
    val net = empty
      |> ins (Const("\<lambda>", T), "const_lambda")
      |> ins (Abs("x", T, Bound 0), "abs_item")
    val _ = assert_eq_set "const lambda only" ["const_lambda"]
      (match_term net (Const("\<lambda>", T)))
    val _ = assert_eq_set "abs only" ["abs_item"]
      (match_term net (Abs("x", T, Bound 0)))
  in writeln "Test 9 (lambda vs non-lambda): pass" end;

(* Test 10: Application inside lambda body *)
val _ =
  let
    val _ = assert_eq_keys "app in body"
      [CombK, AtomK "\<lambda>", CombK, AtomK "f", AtomK (Name.bound 0)]
      (key_of_term (Abs("x", T, Const("f", T) $ Bound 0)))
    val net = empty
      |> ins (Abs("x", T, Const("f", T) $ Bound 0), "f_app")
      |> ins (Abs("x", T, Const("g", T) $ Bound 0), "g_app")
    val _ = assert_eq_set "app body f" ["f_app"]
      (match_term net (Abs("x", T, Const("f", T) $ Bound 0)))
    val _ = assert_eq_set "app body g" ["g_app"]
      (match_term net (Abs("x", T, Const("g", T) $ Bound 0)))
  in writeln "Test 10 (app inside lambda body): pass" end;

val _ = writeln "All iNet lambda abstraction tests passed."

end
\<close>

text \<open>End-to-end test: insert every global fact from the current theory into an iNet,
  then verify each one can be retrieved via @{ML "iNet.match_term"}.\<close>

ML \<open>
let
  val thy = \<^theory>

  (* Collect all global facts (including inherited ones) *)
  val facts = Global_Theory.facts_of thy
  val all_facts = Facts.dest_static false [] facts

  (* Flatten to (prop, label) pairs — one per individual theorem *)
  val entries = all_facts |> maps (fn (name, thms) =>
    thms |> map_index (fn (i, thm) =>
      let
        val label =
          if length thms = 1 then name
          else name ^ "(" ^ string_of_int i ^ ")"
      in (Thm.prop_of thm, label) end))

  val n = length entries
  val _ = writeln ("E2E: " ^ string_of_int n ^ " facts to index")

  (* Insert all entries *)
  val net = fold (fn (prop, label) =>
    iNet.insert_term_safe (op =) (prop, label)) entries iNet.empty

  (* Verify: match_term on each prop must return its label *)
  val (n_ok, failures) = fold (fn (prop, label) => fn (ok, fails) =>
    let val results = iNet.match_term net prop
    in if member (op =) results label
       then (ok + 1, fails)
       else (ok, (label, length results) :: fails)
    end) entries (0, [])

  val n_fail = length failures
  val _ = writeln ("E2E: " ^ string_of_int n_ok ^ " ok, " ^
                   string_of_int n_fail ^ " failed")

  (* Report selectivity: how well does the net discriminate? *)
  (* Sample up to 200 non-Var-headed facts for selectivity stats *)
  val sample = entries
    |> filter (fn (prop, _) => not (is_Var (head_of prop)))
    |> take 200
  val selectivities = sample |> map (fn (prop, _) =>
    length (iNet.match_term net prop))
  val _ = if null selectivities then ()
    else let
      val total = List.foldl (op +) 0 selectivities
      val avg = total div length selectivities
      val mx = fold Integer.max selectivities 0
    in writeln ("E2E selectivity (sample " ^ string_of_int (length selectivities) ^
                " non-Var facts): avg " ^ string_of_int avg ^
                " matches, max " ^ string_of_int mx ^
                " (out of " ^ string_of_int n ^ " total)")
    end
in
  if n_fail = 0 then ()
  else
    (app (fn (label, nres) =>
       writeln ("  FAIL: " ^ label ^ " (" ^ string_of_int nres ^ " results)"))
     (take 20 failures);
     error ("E2E: " ^ string_of_int n_fail ^ "/" ^ string_of_int n ^
            " facts not retrieved"))
end
\<close>

end
