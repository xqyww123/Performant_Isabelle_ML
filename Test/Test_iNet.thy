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

(* Test 10: Application inside lambda body.
   The expected key is [AtomK "f"]: `key_of_term' normalizes its input, and
   `%x. f x' eta-contracts to `f'.  This is the key `insert_term' has ALWAYS
   stored for this term (it normalized before keying since day one) -- the old
   expectation [CombK, AtomK "\<lambda>", CombK, AtomK "f", AtomK ":000"] pinned an
   encoding that never occurred in any net, observable only through the bare
   `key_of_term'.  If this assertion goes red, fix the expectation, do not make
   `key_of_term' stop normalizing: that reopens the `(%x. f x) $ a' key-drops-
   the-argument gap (improved_net.ML, PRECONDITION comment). *)
val _ =
  let
    val _ = assert_eq_keys "app in body"
      [AtomK "f"]
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

(* Test 11: insert_term_last -- same-key order, and order-preserving rebuild *)
ML \<open>
local
  val T = dummyT;
  val eq = (fn ((_, a), (_, b)) => a = b) : (term * string) * (term * string) -> bool;
  val key = Const ("k", T) $ Var (("x", 0), T);
  fun item s = (key, s);
  fun ins_head x net = iNet.insert_term eq (key, x) net;
  fun ins_last x net = iNet.insert_term_last eq (key, x) net;
  fun names net = map #2 (iNet.match_term net (Const ("k", T) $ Const ("c", T)));
  fun assert_order msg expected actual =
    if expected = actual then ()
    else error ("FAIL: " ^ msg ^
                "\n  expected: " ^ ML_Syntax.print_list ML_Syntax.print_string expected ^
                "\n  actual:   " ^ ML_Syntax.print_list ML_Syntax.print_string actual);
in
val _ =
  let
    (*head-insert: last registered first -- the shipped behaviour, unchanged*)
    val net_head = iNet.empty |> ins_head (item "a") |> ins_head (item "b") |> ins_head (item "c");
    val _ = assert_order "insert_term same-key order (last first)" ["c", "b", "a"] (names net_head);
    (*tail-insert: first registered first*)
    val net_last = iNet.empty |> ins_last (item "a") |> ins_last (item "b") |> ins_last (item "c");
    val _ = assert_order "insert_term_last same-key order (first first)" ["a", "b", "c"] (names net_last);
    (*dest + rebuild with insert_term_last preserves the retrieval order, which the
      head-insert rebuild reverses (see the note at `add_rule' in merely_rewrite.ML)*)
    val rebuilt =
      fold (fn x => iNet.insert_term_last eq (key, x)) (iNet.content net_last) iNet.empty;
    val _ = assert_order "insert_term_last rebuild preserves order" (names net_last) (names rebuilt);
    val _ =
      (iNet.insert_term_last eq (key, item "a") net_last; error "FAIL: duplicate not rejected")
        handle iNet.INSERT => ();
    val _ = iNet.insert_term_last_safe eq (key, item "a") net_last;
  in writeln "Test 11 (insert_term_last): pass" end;
end
\<close>

(* Test 12: merge -- each side's same-key order survives, duplicates are dropped.
   `merge' folds net2 into net1 with `fold_rev' over `dest'; a plain `fold' here
   reverses every net2 leaf, which for consumers relying on last-inserted-first
   override semantics silently makes the EARLIER rule win after a theory merge
   (measured 2026-08-08; this test pins the fix). *)
ML \<open>
local
  val T = dummyT;
  val eq = (fn ((_, a), (_, b)) => a = b) : (term * string) * (term * string) -> bool;
  val key = Const ("k", T) $ Var (("x", 0), T);
  val other = Const ("k2", T) $ Var (("x", 0), T);
  fun ins k s net = iNet.insert_term eq (k, (k, s)) net;
  fun names net = map #2 (iNet.match_term net (Const ("k", T) $ Const ("c", T)));
  fun assert_order msg expected actual =
    if expected = actual then ()
    else error ("FAIL: " ^ msg ^
                "\n  expected: " ^ ML_Syntax.print_list ML_Syntax.print_string expected ^
                "\n  actual:   " ^ ML_Syntax.print_list ML_Syntax.print_string actual);
in
val _ =
  let
    val net2 = iNet.empty |> ins key "a" |> ins key "b" |> ins key "c";  (*retrieval [c,b,a]*)
    val net1 = iNet.empty |> ins other "u";
    val _ = assert_order "merge keeps net2 same-key order (empty base)"
              ["c", "b", "a"] (names (iNet.merge eq (iNet.empty, net2)));
    val _ = assert_order "merge keeps net2 same-key order (non-empty base)"
              ["c", "b", "a"] (names (iNet.merge eq (net1, net2)));
    val _ = assert_order "merge keeps net1 same-key order (net1 is the fold base)"
              ["c", "b", "a"] (names (iNet.merge eq (net2, net1)));
    (*duplicates arriving from net2 are dropped without disturbing either order;
      net2's genuinely new items land IN FRONT of the base's -- that cross-side
      placement is measured behaviour, not contract (merge-direction dependent)*)
    val net3 = iNet.empty |> ins key "b" |> ins key "d";  (*retrieval [d,b]; "b" duplicates net2's*)
    val _ = assert_order "merge drops eq-duplicates, keeps both orders"
              ["d", "c", "b", "a"] (names (iNet.merge eq (net2, net3)));
  in writeln "Test 12 (merge order): pass" end;
end
\<close>

end
