(*  Title:  Test/xxhash_checks.ML
    Author: Qiyuan Xu (with AI assistance)

The one copy of the values that pin XXHash and the theory-hash formula.  Loaded
(ML_file, so it has no theory header) by Test/XXHash_Test.thy and, in the release
workflow's verify job, by the check session Check_Native on Linux and on Windows
against the installed package.  XXHash_Checks.run raises an error on the first
mismatch.  Needs a process whose heap holds Main.

The theory hashes are golden values over Isabelle2026's stock sources.  A mismatch
on an unchanged Isabelle means the formula of library/theory_hash.ML's header
changed, which re-keys every semantic DB.  At an Isabelle upgrade, recompute them
independently -- never copy what Theory_Hash.hash_of prints:
  - Pure, ML_Bootstrap and Pure.Sessions directly from their single files:
    xxh128(long name, NUL, file bytes, then the parent hashes), lowest bit of
    byte 0 cleared; Pure has no parent, the other two have Pure;
  - Main with dump_graph below, which writes Main and every ancestor -- long name,
    file, parents in Theory.parents_of order -- without hashing anything, and this
    fold over its output:

      import sys, xxhash
      rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1], encoding="utf-8")]
      info = {n: (p, ps.split(",") if ps else []) for n, p, ps in rows}
      memo = {}
      def h(n):
          if n not in memo:
              p, ps = info[n]
              x = xxhash.xxh128()
              x.update(n.encode("utf-8")); x.update(b"\0"); x.update(open(p, "rb").read())
              for q in ps: x.update(h(q))
              d = bytearray(x.digest()); d[0] &= 0xFE; memo[n] = bytes(d)
          return memo[n]
      print(h(sys.argv[2]).hex())        # python3 fold.py graph.tsv Main

The XXHash digests are Python's: xxhash.xxh128(<the same bytes>).hexdigest().
*)

structure XXHash_Checks:
sig
  val run: unit -> unit
  val dump_graph: theory -> Path.T -> unit
end =
struct

fun check what got expected =
  if got = expected then ()
  else error ("XXHash check failed: " ^ what ^ " is " ^ got ^ ", expected " ^ expected)

fun digest_of pieces = Theory_Hash.to_hex (XXHash.xxh128 (fn st => List.app (XXHash.update st) pieces))

(*bytes (i * 31 + 7) mod 256: 300 of them cross XXH3's 256-byte internal buffer*)
val s300 = String.implode (List.tabulate (300, fn i => Char.chr ((i * 31 + 7) mod 256)))

(*CR, LF and 0x1A (Windows text mode's end of file) explicitly, then every byte value,
  past the C side's 64 KiB read block*)
val file_content =
  "line one\r\nline two\n\026after ctrl-z\r\n" ^
  String.implode (List.tabulate (70000, fn i => Char.chr ((i * 7 + 13) mod 256)))

val golden_theory_hashes =
 [("Pure", "a2d0ad12bc775ef1191131f7e739c4be"),
  (*raw byte 0 is 0x8b: checks the bit clear and an appended parent hash*)
  ("ML_Bootstrap", "8a33ba2baf891d7a6d3dc3d302eb6882"),
  (*long name and base name differ: checks the long name is hashed*)
  (\<^unchecked_name>\<open>Pure.Sessions\<close>, "ae76da35940e1bff0bff0b39580308ac"),
  (*several parents: checks their Theory.parents_of order*)
  ("Main", "7038a01d75d8546b0858d3c5d0078089")]

fun the_theory name =
  (case Build.lookup_theory name of
    SOME thy => thy
  | NONE => error ("XXHash check: theory " ^ quote name ^ " is not in this process's heap"))

fun run () =
  let
    val _ = check "the digest of no bytes" (digest_of []) "99aa06d3014798d86001c324468d497f"
    val _ = check "the digest of \"Isabelle\"" (digest_of ["Isabelle"]) "1c6023c42c8b23bdc7af2781a5acfd4c"
    val _ = check "the digest of \"Isabelle\" in two pieces" (digest_of ["Isa", "belle"])
      "1c6023c42c8b23bdc7af2781a5acfd4c"
    val _ = check "the digest of 300 bytes" (digest_of [s300]) "a0b29158ee3e8112baad8e6a5f186ce6"
    val _ = check "the digest of 300 bytes in three pieces"
      (digest_of [String.substring (s300, 0, 1), String.substring (s300, 1, 255), String.extract (s300, 256, NONE)])
      "a0b29158ee3e8112baad8e6a5f186ce6"
    val _ =
      Isabelle_System.with_tmp_file "xxhash_check" "bin" (fn path =>
        (File.write path file_content;
         check "the digest of a 70034-byte file with CR, LF and 0x1A"
           (Theory_Hash.to_hex (XXHash.xxh128 (fn st => XXHash.update_file st path)))
           "db034d4a897e74e8a76ccaad8eac4720"))
    val _ =
      golden_theory_hashes |> List.app (fn (name, expected) =>
        check ("the theory hash of " ^ name)
          (Theory_Hash.to_hex (Theory_Hash.hash_of (the_theory name))) expected)
  in () end

(*one line per theory: long name TAB file TAB parents (comma-separated, in
  Theory.parents_of order); no hash is computed*)
fun dump_graph thy path =
  Theory.nodes_of thy
  |> map (fn t =>
      Context.theory_long_name t ^ "\t" ^ File.platform_path (Theory_Hash.get_theory_path t) ^ "\t" ^
      space_implode "," (map Context.theory_long_name (Theory.parents_of t)) ^ "\n")
  |> File.write_list path

end
