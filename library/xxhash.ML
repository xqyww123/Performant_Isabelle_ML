(*  Title:  library/xxhash.ML
    Author: Qiyuan Xu (with AI assistance)

XXH3 128-bit, streaming: the hash Python's xxhash.xxh128() computes, seed 0.

THE MECHANISM.  library/native/xxhash.c, part of libperformant_isabelle_ml --
the library Thread_CPU uses, loaded here by code of our own.  It holds
xxHash's own implementation (xxhash.h, vendored) behind five entry points over
an opaque C state; a file is read by the C side itself, in blocks, so its bytes
never pass through ML.

WITHOUT THE LIBRARY there is no fallback: xxh128 raises an ERROR naming the
build command.  The library is loaded lazily on first use, so a heap builds
without it.  Poly/ML keeps a loaded library for the life of the process, so a
library built or rebuilt while Isabelle runs takes effect only after a restart
-- the case of a checkout whose library predates xxhash.c, which reports an
undefined xxh128_create.

THE STATE is C memory, so its life is owned by xxh128: created, fed by the
caller's function, digested and freed, on every exit.  Every C call on it runs
under the state's lock, and the free sets it to NONE under that same lock, so
an escaped state -- even one used by a Future still running after xxh128 has
returned -- raises Fail instead of touching freed memory, and concurrent
updates cannot interleave inside the C state (their order then decides the
digest).
*)

signature XXHASH =
sig
  (* XXH3 128-bit, seed 0: the hash Python's xxhash.xxh128() computes. *)
  type state
  (* xxh128 f: a fresh state, fed by f, then digested -- the 16-byte canonical
     (big-endian) form, equal to Python's digest() after the same updates.
     The state lives only while f runs and is freed on every exit, interrupts
     included; using it afterwards raises Fail.  Raises ERROR naming
     library/native/build <platform> when the native library cannot be loaded. *)
  val xxh128 : (state -> unit) -> Word8Vector.vector
  val update : state -> string -> unit
  (* The file's bytes, read by the C library in blocks.  Raises IO.Io when the
     file cannot be opened or read; a failure of File.platform_path passes
     through unchanged, as in File.read. *)
  val update_file : state -> Path.T -> unit
end

structure XXHash : XXHASH =
struct

(** the C library **)

local
  open Foreign

  (*ML_PLATFORM with the compact-object "_32" stripped: the process is still
    64-bit and takes the same library (library/thread_cpu.ML)*)
  val platform =
    (case space_explode "-" ML_System.platform of
      [arch, os] => perhaps (try (unsuffix "_32")) arch ^ "-" ^ os
    | _ => ML_System.platform)

  val path =
    Resources.master_directory \<^theory> + Path.make ["library", "native", platform,
      if ML_System.platform_is_windows then \<^unchecked_name>\<open>performant_isabelle_ml.dll\<close>
      else \<^unchecked_name>\<open>libperformant_isabelle_ml.so\<close>]

  val library = loadLibraryIndirect (fn () => File.platform_path path)

  (*the library and its symbols are memoised thunks resolved at the first call;
    a load failure names the path tried*)
  fun explain call x =
    call x handle Foreign.Foreign msg =>
      error (msg ^ "\nbuild (or rebuild) it with library/native/build " ^ platform ^
        ", then restart Isabelle")
in
  val c_create = explain (buildCall0 (getSymbol library "xxh128_create", (), cPointer))
  val c_update =
    explain (buildCall3 (getSymbol library "xxh128_update", (cPointer, cByteArray, cSize), cVoid))
  val c_update_file =
    explain (buildCall2 (getSymbol library "xxh128_update_file", (cPointer, cString), cInt))
  val c_digest = explain (buildCall2 (getSymbol library "xxh128_digest", (cPointer, cPointer), cVoid))
  val c_free = explain (buildCall1 (getSymbol library "xxh128_free", cPointer, cVoid))
end


(** the state **)

(*NONE once freed*)
datatype state = State of Foreign.Memory.voidStar option Synchronized.var

fun with_live (State var) f =
  Synchronized.change var
    (fn SOME p => (f p; SOME p)
      | NONE => raise Fail "XXHash: a state used after its xxh128 returned")

fun update st s = with_live st (fn p => c_update (p, Byte.stringToBytes s, size s))

fun update_file st file =
  let val name = File.platform_path file in
    with_live st (fn p =>
      (case c_update_file (p, name) of
        0 => ()
      | code =>
          raise IO.Io {name = name, function = \<^unchecked_name>\<open>XXHash.update_file\<close>,
            cause = OS.SysErr ("errno " ^ string_of_int code, NONE)}))
  end

(*alloca frees the buffer on return and on raise*)
fun digest p =
  Foreign.Memory.alloca (0w16, fn out =>
    (c_digest (p, out);
     Word8Vector.tabulate (16, fn i => Foreign.Memory.get8 (out, Word.fromInt i))))


(** xxh128 **)

(*interrupts are restored only around f; capture0, as in Thread_CPU.with_clock,
  leaves the break flag to the caller*)
fun xxh128 f =
  Thread_Attributes.uninterruptible_body (fn run =>
    let
      val p = c_create ()
      val _ = if p = Foreign.Memory.null then error "XXHash: out of memory" else ()
      val var = Synchronized.var \<^unchecked_name>\<open>XXHash.state\<close> (SOME p)
      val result = Exn.capture0 (fn () => run f (State var)) ()
      val d =
        Synchronized.change_result var (fn _ =>
          let val d = Exn.capture0 (fn () => (Exn.release result; digest p)) ()
          in c_free p; (d, NONE) end)
    in Exn.release d end)

end
