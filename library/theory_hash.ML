(*
  Theory Hash: 16-byte content hashing for Isabelle theories.

  For loaded theories (Resources.loaded_theory: from a heap, or of the session
  being built):
    xxhash128 of the long theory name, a NUL, the .thy file content and the
    parent hashes, computed natively by XXHash. LSB of byte 0 is cleared (= 0).
    The name is in the digest so that two theories sharing a base name -- or
    one .thy file loaded under two long names -- do not share an identity.

  For non-loaded theories (e.g., being processed in jEdit):
    FNV-1a 128-bit hash of the long theory name, computed locally.
    LSB of byte 0 is set (= 1).

  The LSB convention allows downstream code to distinguish which
  hash scheme produced the value.

  These hashes prefix the keys of every semantic DB, published ones included:
  the formula above must never change.  Test/xxhash_checks.ML pins it.

  What a long name does and does not identify
  -------------------------------------------

  hash_of takes a theory VALUE and memoizes on Context.theory_identifier, the only
  per-process identity a theory has, so it is a function: same value, same hash.

  Callers key caches on the theory's LONG NAME instead -- Universal_Key.cache on
  (entity, long name), a constituent list on (long name, hash) pairs.  That is sound
  only while a long name determines a content hash within one process.  It usually
  does.  Three situations threaten it.  The first cannot arise; the other two are
  reachable and MEASURED (2026-11-02), and NEITHER is handled.  Their preconditions
  are things a normal workflow does not do, and the requirement is that they are not
  done.

  1. A theory of the session being built, loaded a second time with different
     content.  It cannot arise: Build loads no theory on request and refuses a
     second commit of a loaded name (build.ML:64-67 in check_new).

  2. A second theory begun under a name already loaded.  Nothing checks for it:
     Resources.begin_theory -> Theory.begin_theory -> Context.begin_thy verify a
     non-empty name, non-empty imports, and ancestors with distinct base names, and
     no more.  Isa-REPL builds theories this way (its init_thy calls
     Resources.begin_theory), producing a second value under an already-used long
     name, so a collision there is silent.  Re-evaluating a theory under the same
     base name is expected in the REPL, so this situation is now common, still
     silent, and still unhandled.

  3. A source file edited after the heap was built.  hash_of reads the file at
     get_theory_path from DISK, not the content of the theory value handed to it, so
     a process on a stale heap hashes the new file while working with the old theory.
     This one needs no coincidence; the remedy is the ordinary one, rebuild the heap.
*)

signature THEORY_HASH = sig
  type hash = Word8Vector.vector  (* 16 bytes, xxhash128 *)
  exception Cannot_Hash of theory
  (* Raises Cannot_Hash when a persistent theory's file cannot be named or read,
     and XXHash's ERROR (naming the build command) when the native library cannot
     be loaded. *)
  val hash_of : theory -> hash
  (* Hash of a theory given by its LONG name.  Prefers Build's registry of
     loaded theories (a graph lookup) over Theory.resolve_theory, whose
     Context.get_theory is a linear scan of the context's ancestors.  See
     hash_of_long below for why the two routes cannot disagree on the hash. *)
  val hash_of_long : Context.generic -> string -> hash
  val theory_of : hash -> theory option
  val is_persistent : hash -> bool
  val hasher : hash -> word
  val to_hex : hash -> string
  (* Identity of THIS ML process, generated once on first use.  Together with a
     theory's serial (Context.theory_identifier) it forms the WIP theory-status
     skip pair (Semantic_Embedding CHECK_OUTDATE_PLAN.md §3.4): a serial is a
     process-local counter, so two sessions can mint the same value for
     different content -- a stored serial may only ever be trusted alongside
     the process that minted it.  LAZY on purpose: a plain top-level value
     would be computed at heap-build time and frozen into the heap, giving
     every process that loads the heap the SAME identity. *)
  val process_id : unit -> string
  (* The theory's own .thy file, as a Path.T (see the comment at the definition for
     why the conversion to a string is left to the caller).  Exposed because it is
     what the hash above is taken over, so a caller that must name the same file --
     the entity dump's per-theory source path,
     BUG_UNIVERSAL_KEY_SHORT_NAME_FIX_PLAN.md §B.3 -- names it identically. *)
  val get_theory_path : theory -> Path.T
end

structure Theory_Hash : THEORY_HASH = struct

type hash = Word8Vector.vector

exception Cannot_Hash of theory

val hasher = Hashers.bitvec

(* Cache: theory identifier -> hash *)
val cache : hash Inttab.table Synchronized.var =
  Synchronized.var \<^unchecked_name>\<open>Theory_Hash.cache\<close> Inttab.empty

(* Reverse map: hash -> theory *)
structure Hash_Tab = Hash_Table(
  type key = hash
  val hash = hasher
  val eq = op = : hash * hash -> bool)

val hash_to_thy : theory Hash_Tab.table Synchronized.var =
  Synchronized.var \<^unchecked_name>\<open>Theory_Hash.hash_to_thy\<close> (Hash_Tab.empty 64)

fun theory_of h =
  Synchronized.change_result hash_to_thy (fn tab => (Hash_Tab.lookup tab h, tab))

(* Convert 16-byte hash to 32-char hex string *)
local
  val hex = "0123456789abcdef"
  fun byte_hex b =
    let val n = Word8.toInt b
    in String.implode [String.sub (hex, n div 16), String.sub (hex, n mod 16)]
    end
in
fun to_hex (h : hash) =
  String.concat (List.tabulate (Word8Vector.length h, fn i =>
    byte_hex (Word8Vector.sub (h, i))))
end

fun is_persistent (h : hash) : bool =
  Word8.andb (Word8Vector.sub (h, 0), 0w1) = 0w0

(* Everything internal stays a Path.T.  The conversion to a platform string happens ONLY
   where a platform string is actually wanted -- the argument of a native call.

   This split is the fix for a Windows-only failure: the old version returned
   File.platform_path and a caller immediately fed that back to Path.explode, which
   rejects `:` and `\` (Path.check_elem).  On Linux and macOS ML_System.platform_path is
   the identity, so the round trip was invisible and every platform but one was correct.
   See auto_sledgehammer/library/cache_file.ML:243 for the same rule stated positively:
   keep Path.T internally, convert in the argument position, never store the result. *)
fun get_theory_path thy =
  let
    val thy_name = Context.theory_long_name thy
    val master_dir = Resources.master_directory thy
    val thy_base = Long_Name.base_name thy_name
    val thy_file = Path.ext "thy" (master_dir + Path.basic thy_base)
  in
    File.full_path master_dir thy_file
  end


fun hash_of thy =
  let
    val id = Context.theory_identifier thy
  in
    case Synchronized.change_result cache (fn tab =>
      case Inttab.lookup tab id of
        SOME h => (SOME h, tab)
      | NONE => (NONE, tab)) of
      SOME h => h
    | NONE =>
        let
          val name = Context.theory_long_name thy

          val h =
            if Resources.loaded_theory name then
              let
                (* Path construction and the existence check sit INSIDE one \<^try>,
                   because on Windows each of them can raise and the intended behaviour
                   for both is the same: degrade to Cannot_Hash.

                   File.is_file runs File.platform_path -- the very conversion
                   XXHash.update_file runs below (file.ML:41, :89) -- and runs it
                   OUTSIDE its own `can' (file.ML:89 in val exists), so a conversion
                   failure (ML_System.platform_path raises Fail "Unknown environment
                   variable CYGWIN_ROOT" for an absolute path not under /cygdrive when
                   that variable is unset, ml_system.ML:50-52 in val platform_path)
                   surfaces here, inside the \<^try>, and becomes Cannot_Hash. *)
                val file = \<^try>\<open>
                    let val p = get_theory_path thy in
                      if File.is_file p then p else raise Cannot_Hash thy
                    end
                  catch _ => raise Cannot_Hash thy\<close>

                (* Recursively hash parent theories *)
                val parent_hashes = map hash_of (Theory.parents_of thy)

                (* Only IO.Io becomes Cannot_Hash here: the ERROR of a native library
                   that cannot be loaded must reach the user with its build command. *)
                val digest =
                  XXHash.xxh128 (fn st =>
                    (XXHash.update st name;
                     XXHash.update st "\000";
                     XXHash.update_file st file;
                     List.app (XXHash.update st o Byte.bytesToString) parent_hashes))
                  handle IO.Io _ => raise Cannot_Hash thy
              in
                (* clear byte 0's LSB: marks a persistent hash, see is_persistent *)
                Word8Vector.update (digest, 0, Word8.andb (Word8Vector.sub (digest, 0), 0wxFE))
              end
            else
              let
                (* FNV-1a 128-bit hash of theory name, set LSB.

                   THIS BRANCH DEFINES "WIP": a theory with Resources.loaded_theory
                   false is a WIP theory, keyed by NAME -- the hash is deliberately
                   content-independent (it does not change when the theory's content
                   changes), giving identity that is stable across edits and
                   sessions.  Change detection for WIP entities is someone else's
                   job by design: Semantic_Embedding's incremental-invalidation
                   fields (semantic digest / deps / version / interpreted_at, see
                   its CHECK_OUTDATE_PLAN.md §2-§4) exist exactly for keys minted
                   here, and its enumerate_entries computes digests only for
                   theories on this side of the fork.  Keep the two branch
                   conditions in sync with that consumer: the WIP bit this branch
                   sets (LSB = 1) is what Python's is_WIP and the CI export filter
                   read. *)
                val arr = Term_Digest.digest128_to_array (Term_Digest.string128 name)
                val _ = Word8Array.update (arr, 0,
                  Word8.orb (Word8Array.sub (arr, 0), 0w1))
              in Word8Array.vector arr end

          (* Cache the result *)
          val _ = Synchronized.change cache (Inttab.update (id, h))
          val _ = Synchronized.change hash_to_thy (fn tab => (Hash_Tab.update tab (h, thy); tab))
        in h end
  end

(* Long theory name -> hash.  No memo of its own: hash_of memoizes on the theory
   identifier, and Build.lookup_theory is a graph lookup in Isabelle's own
   registry, which holds only theories from heaps and from session builds; a build
   commits the theories of a ROOT theories section together when that section
   finishes (build.ML:185-187 in schedule_theories).  Theory.resolve_theory is the
   route for every other theory: the unfinished theory, a theory of a theories
   section still being built, or one loaded by PIDE or by Isa-REPL.

   The two routes may hand back different theory VALUES for one long name, with no
   key divergence: hash_of reads only the name (Resources.loaded_theory picks the
   branch; the WIP hash is FNV of the name) and the file content plus parent hashes.
   Do NOT route key_of_ns_entity through here — it would prefer the heap-registered
   theory over the in-flight one, a regression in the editing case.

   Theory.resolve_theory infers long-vs-short by String.isSubstring ".", so the
   dotless global names (Pure, Main, Complex_Main, ML_Bootstrap, the AFP (global)
   theories) take its base-name branch.  Harmless: no loaded theory shares a base
   name with them, and the path is reached only on a Build registry miss. *)
fun hash_of_long context long =
  hash_of (case Build.lookup_theory long of
             SOME thy => thy
           | NONE => Theory.resolve_theory (Context.proof_of context) (long, Position.none))

(* See the signature comment.  Nanosecond start time ++ Isabelle's own serial
   counter: unique enough that a collision would additionally need the same
   theory serial to cause even one false skip. *)
local
  val id_var : string option Synchronized.var =
    Synchronized.var \<^unchecked_name>\<open>Theory_Hash.process_id\<close> NONE
in
fun process_id () =
  Synchronized.change_result id_var (fn
    SOME id => (id, SOME id)
  | NONE =>
      let val id =
        string_of_int (Time.toNanoseconds (Time.now ())) ^ "-" ^ serial_string ()
      in (id, SOME id) end)
end

end
