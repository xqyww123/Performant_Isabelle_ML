(* Checks for library/dynamic_array.ML.

   Run it by hand -- like every other test here, it is deliberately NOT in ROOT.
   Failure is an `error'; each part announces itself when it passes, and part 3
   prints its measurements.

   Part 1 checks each operation on small hand-written cases, part 2 drives a
   dynamic array and a list model with the same random operation sequence and
   compares them after every step, part 3 times the hot paths, with a raw
   `Array' baseline where one exists and `Library.sort' on a list as the
   sorting baseline. *)
theory Dynamic_Array_Test
  imports "../Performant_Isabelle_ML"
begin

ML \<open>
  fun assert _ true = ()
    | assert msg false = error ("FAILED: " ^ msg)

  fun assert_eq msg show expected actual =
    assert (msg ^ ": expected " ^ show expected ^ ", got " ^ show actual) (expected = actual)

  val ints = ML_Syntax.print_list string_of_int
  fun assert_dest msg expected d = assert_eq msg ints expected (Dynamic_Array.dest d)

  fun raises_Subscript f = (f (); false) handle Subscript => true
  fun raises_Empty f = (f (); false) handle Empty => true
  fun raises_Size f = (f (); false) handle Size => true
\<close>

text \<open>Part 1: each operation\<close>

ML \<open>
local
  open Dynamic_Array

  (* empty, push, storage acquired at the first push *)
  val d = empty 100 : int T
  val _ = assert "empty: length 0" (length d = 0)
  val _ = assert "empty: is_empty" (is_empty d)
  val _ = assert "empty: no storage" (capacity d = 0)
  val _ = assert "empty: dest = []" (dest d = [])
  val _ = assert "empty: pop raises Empty" (raises_Empty (fn () => pop d))
  val _ = assert "empty: last raises Empty" (raises_Empty (fn () => last d))
  val _ = assert "empty: sub 0 raises Subscript" (raises_Subscript (fn () => sub (d, 0)))
  val _ = push (d, 7)
  val _ = assert "first push: hint honoured" (capacity d = 100)
  val _ = assert_dest "first push" [7] d
  val _ = assert "sub 0" (sub (d, 0) = 7)
  val _ = assert "sub 1 raises Subscript" (raises_Subscript (fn () => sub (d, 1)))
  val _ = assert "sub ~1 raises Subscript" (raises_Subscript (fn () => sub (d, ~1)))
  val _ = assert "update 1 raises Subscript" (raises_Subscript (fn () => update (d, 1, 0)))
  val _ = update (d, 0, 8)
  val _ = assert "update 0" (sub (d, 0) = 8 andalso last d = 8)

  (* hint below the minimum, growth by doubling *)
  val d = empty 0 : int T
  val _ = List.app (fn i => push (d, i)) (0 upto 16)
  val _ = assert "minimum storage 16, doubled once" (capacity d = 32)
  val _ = assert_dest "17 pushes" (0 upto 16) d
  val _ = List.app (fn i => push (d, i)) (17 upto 99)
  val _ = assert "storage 128 after 100 pushes" (capacity d = 128)
  val _ = assert_dest "100 pushes" (0 upto 99) d
  val _ = assert "fold sums" (fold (curry op +) d 0 = 4950)
  val _ = assert "fold_rev builds in order" (fold_rev cons d [] = (0 upto 99))
  val _ = assert "fold_index sees indices" (fold_index (fn (i, x) => fn b => b andalso i = x) d true)
  val _ = assert "exists 42" (exists (fn x => x = 42) d)
  val _ = assert "not exists 100" (not (exists (fn x => x = 100) d))
  val _ = assert "forall < 100" (forall (fn x => x < 100) d)
  val _ = assert "not forall < 99" (not (forall (fn x => x < 99) d))
  val _ = assert "get_first" (get_first (fn x => if x > 50 then SOME (x * 2) else NONE) d = SOME 102)
  val _ = assert "member" (member op = d 99 andalso not (member op = d ~1))
  val _ = assert "app in order" (let val r = Unsynchronized.ref [] in app (fn x => r := x :: !r) d; !r = rev (0 upto 99) end)
  val _ = assert "to_array" (Array.foldr op :: [] (to_array d) = (0 upto 99))
  val _ = assert "to_vector" (Vector.foldr op :: [] (to_vector d) = (0 upto 99))
  val _ = assert "map" (dest (map (fn x => x * 3) d) = List.map (fn x => x * 3) (0 upto 99))
  val _ = assert "map: exact storage" (capacity (map I d) = 100)
  val c = copy d
  val _ = assert "copy: same elements, exact storage" (dest c = (0 upto 99) andalso capacity c = 100)
  val _ = update (c, 0, ~1)
  val _ = assert "copy: independent" (sub (d, 0) = 0)

  (* pop, truncate, clear; the storage stays *)
  val _ = assert "pop returns the last" (pop d = 99 andalso length d = 99)
  val _ = truncate (d, 10)
  val _ = assert_dest "truncate 10" (0 upto 9) d
  val _ = assert "truncate keeps storage" (capacity d = 128)
  val _ = assert "truncate 11 raises Subscript" (raises_Subscript (fn () => truncate (d, 11)))
  val _ = assert "truncate ~1 raises Subscript" (raises_Subscript (fn () => truncate (d, ~1)))
  val _ = truncate (d, 10)
  val _ = assert_dest "truncate to the same length" (0 upto 9) d
  val _ = truncate (d, 0)
  val _ = assert "truncate 0: empty, storage kept" (is_empty d andalso capacity d = 128)
  val _ = push (d, 1)
  val _ = assert "refill allocates nothing" (capacity d = 128)
  val _ = assert "pop to empty" (pop d = 1 andalso is_empty d andalso capacity d = 128)
  val _ = push_list (d, [1, 2, 3])
  val _ = clear d
  val _ = assert "clear" (is_empty d andalso capacity d = 128)
  val _ = push_list (d, [])
  val _ = assert "push_list []" (is_empty d)
  val _ = push_list (d, 0 upto 199)
  val _ = assert_dest "push_list 200" (0 upto 199) d
  val _ = assert "push_list grows once, doubling" (capacity d = 256)

  (* reserve, shrink_to_fit *)
  val d = empty 0 : int T
  val _ = reserve (d, 1000)
  val _ = assert "reserve on empty: no storage yet" (capacity d = 0)
  val _ = push (d, 1)
  val _ = assert "reserve on empty: honoured at the first push" (capacity d = 1000)
  val _ = shrink_to_fit d
  val _ = assert "shrink_to_fit" (capacity d = 1 andalso dest d = [1])
  val _ = reserve (d, 5)
  val _ = assert "reserve when full: at least 5" (capacity d >= 5 andalso dest d = [1])
  val _ = push_list (d, [2, 3, 4])
  val _ = reserve (d, 300)
  val _ = assert "reserve when partly full" (capacity d >= 300 andalso dest d = [1, 2, 3, 4])
  val _ = shrink_to_fit d
  val _ = shrink_to_fit d
  val _ = assert "shrink_to_fit twice" (capacity d = 4 andalso dest d = [1, 2, 3, 4])
  val _ = assert "reserve beyond Array.maxLen raises Size" (raises_Size (fn () => reserve (d, Array.maxLen)))
  val _ = clear d
  val _ = assert "clear keeps the storage" (capacity d = 4)
  val _ = shrink_to_fit d
  val _ = assert "shrink_to_fit on empty releases the storage" (capacity d = 0)
  val _ = push (d, 0)
  val _ = assert "the hint survives: it was raised to 1000 by reserve" (capacity d = 1000)

  (* unsafe access *)
  val _ = assert "unsafe_sub" (unsafe_sub (d, 0) = 0)
  val _ = unsafe_update (d, 0, 5)
  val _ = assert "unsafe_update" (sub (d, 0) = 5)
  val _ = assert "unsafe_sub beyond storage still raises" (raises_Subscript (fn () => unsafe_sub (d, capacity d)))

  (* insert, delete *)
  val d = make [10, 20, 30]
  val _ = assert "make: exact storage" (capacity d = 3)
  val _ = assert "insert 4 raises Subscript" (raises_Subscript (fn () => insert (d, 4, 0)))
  val _ = assert "insert ~1 raises Subscript" (raises_Subscript (fn () => insert (d, ~1, 0)))
  val _ = insert (d, 3, 40)
  val _ = assert_dest "insert at length" [10, 20, 30, 40] d
  val _ = insert (d, 0, 5)
  val _ = assert_dest "insert at 0" [5, 10, 20, 30, 40] d
  val _ = insert (d, 2, 15)
  val _ = assert_dest "insert in the middle" [5, 10, 15, 20, 30, 40] d
  val _ = assert "delete 6 raises Subscript" (raises_Subscript (fn () => delete (d, 6)))
  val _ = assert "delete ~1 raises Subscript" (raises_Subscript (fn () => delete (d, ~1)))
  val _ = assert "delete 0" (delete (d, 0) = 5)
  val _ = assert_dest "after delete 0" [10, 15, 20, 30, 40] d
  val _ = assert "delete last" (delete (d, 4) = 40)
  val _ = assert "delete middle" (delete (d, 1) = 15)
  val _ = assert_dest "after deletes" [10, 20, 30] d
  val _ = (delete (d, 0); delete (d, 0); delete (d, 0))
  val _ = assert "delete to empty keeps the storage" (is_empty d andalso capacity d = 6)
  val _ = insert (d, 0, 1)
  val _ = assert_dest "insert into empty" [1] d
  val _ = assert "make []" (is_empty (make []) andalso capacity (make [] : int T) = 0)
  val _ = assert "of_array" (dest (of_array (Array.fromList [1, 2])) = [1, 2])
  val _ = assert "of_array []" (is_empty (of_array (Array.fromList []) : int T))
  val e = empty 0 : int T
  val _ = assert "conversions on empty"
    (is_empty (copy e) andalso is_empty (map I e) andalso
     Array.length (to_array e) = 0 andalso Vector.length (to_vector e) = 0)

  (* released slots keep nothing but the element at index 0 (see release) *)
  val d = make [10, 20, 30, 40]
  val _ = truncate (d, 1)
  val _ = assert "truncate overwrites the released slots"
    (unsafe_sub (d, 1) = 10 andalso unsafe_sub (d, 2) = 10 andalso unsafe_sub (d, 3) = 10)
  val _ = push_list (d, [20, 30, 40])
  val _ = assert "pop overwrites the released slot" (pop d = 40 andalso unsafe_sub (d, 3) = 10)
  val _ = assert "delete overwrites the released slot" (delete (d, 1) = 20 andalso unsafe_sub (d, 2) = 10)
  val _ = clear d
  val _ = assert "clear overwrites the released slots" (unsafe_sub (d, 0) = 10 andalso unsafe_sub (d, 1) = 10)

  (* sort: stable, on ranges below and above the insertion-sort threshold *)
  fun check_sort n =
    let
      val xs = List.tabulate (n, fn i => ((i * 7919) mod 13, i))   (*key, original position*)
      val d = make xs
      val _ = sort (int_ord o apply2 fst) d
    in
      assert_eq ("sort " ^ string_of_int n) (ML_Syntax.print_list (ML_Syntax.print_pair string_of_int string_of_int))
        (Library.sort (int_ord o apply2 fst) xs) (dest d)   (*Isabelle's sort is stable too*)
    end
  val _ = List.app check_sort [0, 1, 2, 3, 7, 8, 9, 16, 17, 100, 1000, 1001]
  val d = make (rev (0 upto 99))
  val _ = sort int_ord d
  val _ = assert_dest "sort reversed" (0 upto 99) d

  (* lower_bound, upper_bound, binary_search, insert_sorted *)
  val d = make [1, 3, 3, 3, 5, 7]
  val _ = assert "lower_bound below all" (lower_bound int_ord d 0 = 0)
  val _ = assert "lower_bound first equal" (lower_bound int_ord d 3 = 1)
  val _ = assert "lower_bound between" (lower_bound int_ord d 4 = 4)
  val _ = assert "lower_bound above all" (lower_bound int_ord d 8 = 6)
  val _ = assert "upper_bound below all" (upper_bound int_ord d 0 = 0)
  val _ = assert "upper_bound after the equals" (upper_bound int_ord d 3 = 4)
  val _ = assert "upper_bound between" (upper_bound int_ord d 4 = 4)
  val _ = assert "upper_bound above all" (upper_bound int_ord d 8 = 6)
  val _ = assert "bounds on empty" (lower_bound int_ord (empty 0) 1 = 0 andalso upper_bound int_ord (empty 0) 1 = 0)
  val _ = assert "binary_search first equal" (binary_search int_ord d 3 = SOME 1)
  val _ = assert "binary_search present" (binary_search int_ord d 7 = SOME 5)
  val _ = assert "binary_search absent" (binary_search int_ord d 4 = NONE andalso binary_search int_ord d 8 = NONE)
  val _ = assert "binary_search on empty" (binary_search int_ord (empty 0) 1 = NONE)
  val _ = insert_sorted int_ord d 4
  val _ = insert_sorted int_ord d 0
  val _ = insert_sorted int_ord d 9
  val _ = assert_dest "insert_sorted" [0, 1, 3, 3, 3, 4, 5, 7, 9] d
  val d = make [(1, "a"), (2, "b")]
  val _ = insert_sorted (int_ord o apply2 fst) d (1, "c")
  val _ = insert_sorted (int_ord o apply2 fst) d (1, "d")
  val _ = assert "insert_sorted goes after its equals, keeping insertion order"
    (List.map snd (dest d) = ["a", "c", "d", "b"])
in
  val _ = writeln "part 1 passed"
end
\<close>

text \<open>Part 2: random operations against a list model\<close>

ML \<open>
local
  open Dynamic_Array

  (*a small linear congruential generator, deterministic (Random.random_range shares a global seed)*)
  val seed = Unsynchronized.ref 12345
  fun rand n = (seed := (!seed * 1103515245 + 12345) mod 2147483648; !seed mod n)

  fun list_insert (xs, i, x) = take i xs @ x :: drop i xs

  (*one random operation on both; the model after it, and whether the storage may have shrunk*)
  fun step (d, model) =
    let val n = List.length model in
      case rand 10 of
        0 => let val x = rand 1000 in push (d, x); (model @ [x], false) end
      | 1 => if n = 0 then (model, false) else (pop d; (take (n - 1) model, false))
      | 2 => let val i = rand (n + 1); val x = rand 1000 in insert (d, i, x); (list_insert (model, i, x), false) end
      | 3 => if n = 0 then (model, false) else let val i = rand n
                                                in assert "delete agrees" (delete (d, i) = nth model i); (nth_drop i model, false) end
      | 4 => if n = 0 then (model, false) else let val i = rand n; val x = rand 1000 in update (d, i, x); (nth_map i (K x) model, false) end
      | 5 => let val k = rand (n + 1) in truncate (d, k); (take k model, false) end
      | 6 => let val xs = List.tabulate (rand 5, fn _ => rand 1000) in push_list (d, xs); (model @ xs, false) end
      | 7 => (sort int_ord d; (Library.sort int_ord model, false))
      | 8 => (reserve (d, rand 50); (model, false))
      | _ => (shrink_to_fit d; (model, true))
    end

  val steps = 20000
  fun run d model k =
    if k > steps then ()
    else
      let
        val cap = capacity d
        val (model', shrunk) = step (d, model)
        val _ = assert_eq ("model after step " ^ string_of_int k) ints model' (dest d)
        val _ = assert "length agrees" (length d = List.length model')
        val _ = assert "storage holds the length" (capacity d >= length d)
        val _ = assert "only shrink_to_fit releases storage" (if shrunk then capacity d = length d else capacity d >= cap)
        val _ = assert "sub agrees" (List.all (fn i => sub (d, i) = nth model' i) (0 upto (List.length model' - 1)))
      in run d model' (k + 1) end
in
  val _ = run (empty 0) [] 1
  val _ = writeln "part 2 passed"
end
\<close>

text \<open>Part 3: timings\<close>

ML \<open>
local
  open Dynamic_Array
  val n = 10000000

  (*one warm-up run, then the measured run*)
  fun time msg f = (f (); writeln (msg ^ ": " ^ Timing.message (#1 (Timing.timing f ()))))

  val a = Array.array (n, 0)
  fun fill_fresh () =
    let val d = empty 0 : int T; fun go i = if i < n then (push (d, i); go (i + 1)) else () in go 0; d end
  val _ = time "push x n from empty 0 (with growth)" (fn () => fill_fresh ())
  val d = fill_fresh ()
  (*the dynamic array allocates its storage at the first push, so this baseline allocates too*)
  val _ = time "empty n + push x n (no growth)" (fn () => let val e = empty n : int T; fun go i = if i < n then (push (e, i); go (i + 1)) else () in go 0 end)
  val _ = time "Array.array n + Array.update x n" (fn () => let val b = Array.array (n, 0); fun go i = if i < n then (Array.update (b, i, i); go (i + 1)) else () in go 0 end)
  val _ = time "Array.update x n (storage already allocated)" (fn () => let fun go i = if i < n then (Array.update (a, i, i); go (i + 1)) else () in go 0 end)
  (*the accumulator stays a small int: a sum of 1e7 indices would be a bignum*)
  fun count x s = if x >= 0 then s + 1 else s
  val _ = time "sub x n" (fn () => let fun go i s = if i < n then go (i + 1) (count (sub (d, i)) s) else s in go 0 0 end)
  val _ = time "unsafe_sub x n" (fn () => let fun go i s = if i < n then go (i + 1) (count (unsafe_sub (d, i)) s) else s in go 0 0 end)
  val _ = time "Array.sub x n" (fn () => let fun go i s = if i < n then go (i + 1) (count (Array.sub (a, i)) s) else s in go 0 0 end)
  val _ = time "fold" (fn () => fold count d 0)
  val _ = time "Array.fold" (fn () => Array.fold count a 0)
  val _ = time "app" (fn () => app (fn _ => ()) d)
  val _ = time "Array.app" (fn () => Array.app (fn _ => ()) a)
  val small = make [1, 2, 3, 4]
  val _ = time "fold over 4 elements x 1e6" (fn () => let fun go i s = if i < 1000000 then go (i + 1) (fold count small s) else s in go 0 0 end)
  val _ = time "copy + pop x n" (fn () => let val c = copy d; fun go () = if is_empty c then () else (pop c; go ()) in go () end)
  val _ = time "dest" (fn () => dest d)
  val _ = time "to_array" (fn () => to_array d)
  val _ = time "copy" (fn () => copy d)
  val m = 1000000
  val xs = List.tabulate (m, fn i => (i * 7919) mod 1000003)
  val _ = time "make 1e6 (list -> array; included in the next line)" (fn () => make xs)
  val _ = time "make + sort 1e6" (fn () => sort int_ord (make xs))
  val _ = time "Library.sort 1e6 (list)" (fn () => Library.sort int_ord xs)
  val _ = time "make + copy 1e6 (exact fit: one native move)" (fn () => copy (make xs))
  val s = make xs
  val _ = Dynamic_Array.sort int_ord s
  val _ = time "binary_search x 1e6" (fn () => List.app (fn x => (binary_search int_ord s x; ())) xs)
  val _ = time "insert at 0 x 1e4 into 1e6" (fn () => let val c = copy s; fun go i = if i < 10000 then (insert (c, 0, i); go (i + 1)) else () in go 0 end)
in end
\<close>

end
