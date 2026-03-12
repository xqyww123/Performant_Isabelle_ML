theory Hash_Table_Test
  imports "../Performant_Isabelle_ML"
begin

text \<open>Functional correctness tests\<close>

ML \<open>
local
  fun assert msg true = ()
    | assert msg false = error ("FAILED: " ^ msg)

  fun assert_eq msg expected actual =
    assert (msg ^ " (expected " ^ expected ^ ")") (expected = actual)

  (* --- Inthashtab tests --- *)
  val _ = writeln "=== Inthashtab functional tests ==="

  (* empty table *)
  val t = Inthashtab.empty 4
  val _ = assert "empty size = 0" (Inthashtab.size t = 0)
  val _ = assert "empty is_empty" (Inthashtab.is_empty t)
  val _ = assert "lookup on empty = NONE" (Inthashtab.lookup t 1 = NONE)
  val _ = assert "defined on empty = false" (not (Inthashtab.defined t 1))

  (* insert and lookup *)
  val _ = Inthashtab.update t (1, 10)
  val _ = Inthashtab.update t (2, 20)
  val _ = Inthashtab.update t (3, 30)
  val _ = assert "size after 3 inserts = 3" (Inthashtab.size t = 3)
  val _ = assert "not is_empty" (not (Inthashtab.is_empty t))
  val _ = assert "lookup 1 = SOME 10" (Inthashtab.lookup t 1 = SOME 10)
  val _ = assert "lookup 2 = SOME 20" (Inthashtab.lookup t 2 = SOME 20)
  val _ = assert "lookup 3 = SOME 30" (Inthashtab.lookup t 3 = SOME 30)
  val _ = assert "lookup 4 = NONE" (Inthashtab.lookup t 4 = NONE)

  (* overwrite *)
  val _ = Inthashtab.update t (2, 200)
  val _ = assert "overwrite: size still 3" (Inthashtab.size t = 3)
  val _ = assert "overwrite: lookup 2 = SOME 200" (Inthashtab.lookup t 2 = SOME 200)

  (* update_new raises DUP *)
  val _ = assert "update_new raises DUP"
    ((Inthashtab.update_new t (1, 99); false) handle Inthashtab.DUP _ => true)
  val _ = assert "after DUP: lookup 1 unchanged" (Inthashtab.lookup t 1 = SOME 10)

  (* delete *)
  val _ = Inthashtab.delete t 2
  val _ = assert "delete: size = 2" (Inthashtab.size t = 2)
  val _ = assert "delete: lookup 2 = NONE" (Inthashtab.lookup t 2 = NONE)
  val _ = assert "delete: lookup 1 still works" (Inthashtab.lookup t 1 = SOME 10)

  (* delete raises UNDEF *)
  val _ = assert "delete UNDEF"
    ((Inthashtab.delete t 999; false) handle Inthashtab.UNDEF _ => true)

  (* delete_safe on missing key *)
  val _ = Inthashtab.delete_safe t 999

  (* re-insert after delete *)
  val _ = Inthashtab.update t (2, 222)
  val _ = assert "re-insert: lookup 2 = SOME 222" (Inthashtab.lookup t 2 = SOME 222)
  val _ = assert "re-insert: size = 3" (Inthashtab.size t = 3)

  (* fold, dest, keys *)
  val sum = Inthashtab.fold (fn (_, v) => fn acc => acc + v) t 0
  val _ = assert "fold sum" (sum = 10 + 222 + 30)
  val ds = Inthashtab.dest t
  val _ = assert "dest length = 3" (length ds = 3)
  val ks = Inthashtab.keys t
  val _ = assert "keys length = 3" (length ks = 3)

  (* exists / forall *)
  val _ = assert "exists finds 222" (Inthashtab.exists (fn (_, v) => v = 222) t)
  val _ = assert "exists misses 999" (not (Inthashtab.exists (fn (_, v) => v = 999) t))
  val _ = assert "forall > 0" (Inthashtab.forall (fn (_, v) => v > 0) t)
  val _ = assert "not forall > 100" (not (Inthashtab.forall (fn (_, v) => v > 100) t))

  (* map *)
  val t2 = Inthashtab.map (fn _ => fn v => v * 2) t
  val _ = assert "map: lookup 1 = SOME 20" (Inthashtab.lookup t2 1 = SOME 20)
  val _ = assert "map: original unchanged" (Inthashtab.lookup t 1 = SOME 10)

  (* make *)
  val t3 = Inthashtab.make [(10, 100), (20, 200), (30, 300)]
  val _ = assert "make: size = 3" (Inthashtab.size t3 = 3)
  val _ = assert "make: lookup 20 = SOME 200" (Inthashtab.lookup t3 20 = SOME 200)

  (* stress: many inserts trigger rehash *)
  val big = Inthashtab.empty 4
  val _ = List.app (fn i => Inthashtab.update big (i, i * i)) (List.tabulate (1000, fn i => i))
  val _ = assert "stress: size = 1000" (Inthashtab.size big = 1000)
  val _ = assert "stress: lookup 500" (Inthashtab.lookup big 500 = SOME 250000)
  val _ = assert "stress: lookup 999" (Inthashtab.lookup big 999 = SOME 998001)

  (* stress: delete all then re-insert *)
  val _ = List.app (fn i => Inthashtab.delete big i) (List.tabulate (1000, fn i => i))
  val _ = assert "stress: empty after delete all" (Inthashtab.size big = 0)
  val _ = List.app (fn i => Inthashtab.update big (i, i)) (List.tabulate (100, fn i => i))
  val _ = assert "stress: re-insert after delete" (Inthashtab.size big = 100)
  val _ = assert "stress: re-insert lookup" (Inthashtab.lookup big 50 = SOME 50)

  (* --- Strhashtab tests --- *)
  val _ = writeln "=== Strhashtab functional tests ==="

  val st = Strhashtab.empty 4
  val _ = Strhashtab.update st ("foo", 1)
  val _ = Strhashtab.update st ("bar", 2)
  val _ = Strhashtab.update st ("baz", 3)
  val _ = assert "str: size = 3" (Strhashtab.size st = 3)
  val _ = assert "str: lookup foo" (Strhashtab.lookup st "foo" = SOME 1)
  val _ = assert "str: lookup bar" (Strhashtab.lookup st "bar" = SOME 2)
  val _ = assert "str: lookup miss" (Strhashtab.lookup st "qux" = NONE)
  val _ = Strhashtab.delete st "bar"
  val _ = assert "str: after delete" (Strhashtab.lookup st "bar" = NONE)
  val _ = assert "str: size after delete = 2" (Strhashtab.size st = 2)
  val _ = Strhashtab.update st ("bar", 22)
  val _ = assert "str: re-insert bar" (Strhashtab.lookup st "bar" = SOME 22)

  val _ = writeln "All functional tests passed."
in end
\<close>

text \<open>Performance benchmarks\<close>

ML \<open>
local

fun lcg seed =
  Word.toInt (Word.andb (
    Word.+ (Word.* (Word.fromInt seed, 0w1103515245), 0w12345),
    0w2147483647))

fun gen_keys n =
  let
    fun go 0 _ acc = rev acc
      | go i seed acc =
          let val s = lcg seed
          in go (i - 1) s (s :: acc) end
  in go n 42 [] end

fun seq_keys n = List.tabulate (n, fn i => i + 1)

fun time_it label f =
  let
    val timer = Timing.start ()
    val _ = f ()
    val result = Timing.result timer
  in
    writeln (label ^ ": " ^ Timing.message result)
  end

fun bench_inttab n =
  let
    val skeys = seq_keys n
    val rkeys = gen_keys n
    val miss_keys = List.tabulate (n, fn i => n + i + 1)
    val _ = writeln ("--- Inttab (n=" ^ string_of_int n ^ ") ---")

    (* Sequential insert *)
    val tab = Unsynchronized.ref Inttab.empty
    val _ = time_it "  seq insert" (fn () =>
      List.app (fn k => tab := Inttab.update (k, k) (!tab)) skeys)

    (* Sequential lookup *)
    val t = !tab
    val _ = time_it "  seq lookup" (fn () =>
      List.app (fn k => ignore (Inttab.lookup t k)) skeys)

    (* Random insert *)
    val tab2 = Unsynchronized.ref Inttab.empty
    val _ = time_it "  rnd insert" (fn () =>
      List.app (fn k => tab2 := Inttab.update (k, k) (!tab2)) rkeys)

    (* Random lookup *)
    val t2 = !tab2
    val _ = time_it "  rnd lookup" (fn () =>
      List.app (fn k => ignore (Inttab.lookup t2 k)) rkeys)

    (* Miss lookup *)
    val _ = time_it "  miss lookup" (fn () =>
      List.app (fn k => ignore (Inttab.lookup t k)) miss_keys)

    (* Delete *)
    val tab3 = Unsynchronized.ref t
    val _ = time_it "  delete" (fn () =>
      List.app (fn k => tab3 := Inttab.delete k (!tab3)) skeys)

    (* Fold *)
    val _ = time_it "  fold" (fn () =>
      ignore (Inttab.fold (fn (_, v) => fn acc => acc + v) t 0))
  in () end

fun bench_inthashtab n =
  let
    val skeys = seq_keys n
    val rkeys = gen_keys n
    val miss_keys = List.tabulate (n, fn i => n + i + 1)
    val _ = writeln ("--- Inthashtab (n=" ^ string_of_int n ^ ") ---")

    (* Sequential insert *)
    val tab = Inthashtab.empty 16
    val _ = time_it "  seq insert" (fn () =>
      List.app (fn k => Inthashtab.update tab (k, k)) skeys)

    (* Sequential lookup *)
    val _ = time_it "  seq lookup" (fn () =>
      List.app (fn k => ignore (Inthashtab.lookup tab k)) skeys)

    (* Random insert *)
    val tab2 = Inthashtab.empty 16
    val _ = time_it "  rnd insert" (fn () =>
      List.app (fn k => Inthashtab.update tab2 (k, k)) rkeys)

    (* Random lookup *)
    val _ = time_it "  rnd lookup" (fn () =>
      List.app (fn k => ignore (Inthashtab.lookup tab2 k)) rkeys)

    (* Miss lookup *)
    val _ = time_it "  miss lookup" (fn () =>
      List.app (fn k => ignore (Inthashtab.lookup tab k)) miss_keys)

    (* Delete *)
    val tab3 = Inthashtab.make (List.map (fn k => (k, k)) skeys)
    val _ = time_it "  delete" (fn () =>
      List.app (fn k => Inthashtab.delete_safe tab3 k) skeys)

    (* Fold *)
    val _ = time_it "  fold" (fn () =>
      ignore (Inthashtab.fold (fn (_, v) => fn acc => acc + v) tab 0))
  in () end

fun bench n =
  (writeln ("=== N = " ^ string_of_int n ^ " ===");
   bench_inttab n;
   bench_inthashtab n;
   writeln "")

in

val _ = bench 10000
val _ = bench 100000
val _ = bench 1000000
val _ = bench 10000000

end
\<close>

(*
=== N = 10000 === 
--- Inttab (n=10000) --- 
  seq insert: 0.002s elapsed time, 0.002s cpu time, 0.000s GC time 
  seq lookup: 0.001s elapsed time, 0.001s cpu time, 0.000s GC time 
  rnd insert: 0.003s elapsed time, 0.003s cpu time, 0.000s GC time 
  rnd lookup: 0.001s elapsed time, 0.001s cpu time, 0.000s GC time 
  miss lookup: 0.000s elapsed time, 0.000s cpu time, 0.000s GC time 
  delete: 0.002s elapsed time, 0.002s cpu time, 0.000s GC time 
  fold: 0.000s elapsed time, 0.000s cpu time, 0.000s GC time 
--- Inthashtab (n=10000) --- 
  seq insert: 0.000s elapsed time, 0.000s cpu time, 0.000s GC time 
  seq lookup: 0.000s elapsed time, 0.000s cpu time, 0.000s GC time 
  rnd insert: 0.000s elapsed time, 0.000s cpu time, 0.000s GC time 
  rnd lookup: 0.000s elapsed time, 0.000s cpu time, 0.000s GC time 
  miss lookup: 0.000s elapsed time, 0.000s cpu time, 0.000s GC time 
  delete: 0.000s elapsed time, 0.000s cpu time, 0.000s GC time 
  fold: 0.000s elapsed time, 0.000s cpu time, 0.000s GC time 
=== N = 100000 === 
--- Inttab (n=100000) --- 
  seq insert: 0.021s elapsed time, 0.021s cpu time, 0.000s GC time 
  seq lookup: 0.012s elapsed time, 0.012s cpu time, 0.000s GC time 
  rnd insert: 0.064s elapsed time, 0.064s cpu time, 0.000s GC time 
  rnd lookup: 0.041s elapsed time, 0.041s cpu time, 0.000s GC time 
  miss lookup: 0.005s elapsed time, 0.005s cpu time, 0.000s GC time 
  delete: 0.024s elapsed time, 0.024s cpu time, 0.000s GC time 
  fold: 0.003s elapsed time, 0.003s cpu time, 0.000s GC time 
--- Inthashtab (n=100000) --- 
  seq insert: 0.003s elapsed time, 0.003s cpu time, 0.000s GC time 
  seq lookup: 0.002s elapsed time, 0.002s cpu time, 0.000s GC time 
  rnd insert: 0.003s elapsed time, 0.003s cpu time, 0.000s GC time 
  rnd lookup: 0.002s elapsed time, 0.002s cpu time, 0.000s GC time 
  miss lookup: 0.002s elapsed time, 0.002s cpu time, 0.000s GC time 
  delete: 0.005s elapsed time, 0.005s cpu time, 0.000s GC time 
  fold: 0.001s elapsed time, 0.001s cpu time, 0.000s GC time 
=== N = 1000000 === 
--- Inttab (n=1000000) --- 
  seq insert: 0.264s elapsed time, 0.265s cpu time, 0.000s GC time 
  seq lookup: 0.127s elapsed time, 0.128s cpu time, 0.000s GC time 
  rnd insert: 1.302s elapsed time, 1.630s cpu time, 0.432s GC time 
  rnd lookup: 0.990s elapsed time, 0.991s cpu time, 0.000s GC time 
  miss lookup: 0.059s elapsed time, 0.060s cpu time, 0.000s GC time 
  delete: 0.230s elapsed time, 0.230s cpu time, 0.000s GC time 
  fold: 0.005s elapsed time, 0.006s cpu time, 0.000s GC time 
--- Inthashtab (n=1000000) --- 
  seq insert: 0.067s elapsed time, 0.067s cpu time, 0.000s GC time 
  seq lookup: 0.047s elapsed time, 0.047s cpu time, 0.000s GC time 
  rnd insert: 0.070s elapsed time, 0.070s cpu time, 0.000s GC time 
  rnd lookup: 0.046s elapsed time, 0.047s cpu time, 0.000s GC time 
  miss lookup: 0.022s elapsed time, 0.022s cpu time, 0.000s GC time 
  delete: 0.069s elapsed time, 0.069s cpu time, 0.000s GC time 
  fold: 0.014s elapsed time, 0.014s cpu time, 0.000s GC time 
=== N = 10000000 === 
--- Inttab (n=10000000) --- 
  seq insert: 5.912s elapsed time, 13.060s cpu time, 8.831s GC time 
  seq lookup: 0.844s elapsed time, 0.845s cpu time, 0.000s GC time 
  rnd insert: 23.421s elapsed time, 28.740s cpu time, 6.082s GC time 
  rnd lookup: 16.358s elapsed time, 16.382s cpu time, 0.000s GC time 
  miss lookup: 0.686s elapsed time, 0.687s cpu time, 0.000s GC time 
  delete: 3.560s elapsed time, 3.797s cpu time, 0.282s GC time 
  fold: 0.130s elapsed time, 0.131s cpu time, 0.003s GC time 
--- Inthashtab (n=10000000) --- 
  seq insert: 0.607s elapsed time, 0.607s cpu time, 0.000s GC time 
  seq lookup: 0.374s elapsed time, 0.375s cpu time, 0.000s GC time 
  rnd insert: 0.610s elapsed time, 0.611s cpu time, 0.000s GC time 
  rnd lookup: 0.373s elapsed time, 0.374s cpu time, 0.000s GC time 
  miss lookup: 0.423s elapsed time, 0.424s cpu time, 0.000s GC time 
  delete: 0.418s elapsed time, 0.419s cpu time, 0.000s GC time 
  fold: 0.118s elapsed time, 0.118s cpu time, 0.000s GC time


  ┌\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┬\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┬\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┬\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┬\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┐                                                                        
  │  N  │ Operation  │     Inttab      │ Inthashtab  │ Speedup │
  ├\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┤                                                                        
  │ 1M  │ seq insert │ 0.264s          │ 0.067s      │ 4x      │
  ├\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┤
  │ 1M  │ rnd insert │ 1.302s          │ 0.070s      │ 19x     │                                                                        
  ├\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┤                                                                        
  │ 1M  │ rnd lookup │ 0.990s          │ 0.046s      │ 22x     │                                                                        
  ├\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┤                                                                        
  │ 10M │ seq insert │ 5.9s (8.8s GC!) │ 0.6s (0 GC) │ 10x     │
  ├\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┤                                                                        
  │ 10M │ rnd insert │ 23.4s (6.1s GC) │ 0.6s (0 GC) │ 38x     │
  ├\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┼\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┤                                                                        
  │ 10M │ rnd lookup │ 16.4s           │ 0.4s        │ 44x     │
  └\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┴\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┴\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┴\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┴\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>┘

Two standout patterns:                                                                                                                
  - Random access is where the hash table really shines — the tree's O(log n) with poor cache locality gets destroyed by O(1) amortized
  with flat array access                                                                                                                
  - GC pressure — Inttab allocates tree nodes on every insert, causing significant GC overhead at scale (8.8s GC at 10M seq insert). The
   hash table allocates zero GC-tracked objects during steady-state operations
*)

end
