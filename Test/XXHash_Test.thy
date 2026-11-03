(* Checks for library/xxhash.ML, library/theory_hash.ML and library/resolve_theory.ML.

   Run it by hand -- like every other test here, it is deliberately NOT in ROOT --
   on logic HOL: a heap that holds Main but not this repository, so this
   checkout's sources are what is tested.  In a batch build the `../' import is
   an implicit use of another session's directory, so a batch run takes a scratch
   directory holding a copy of this file with the import changed to
   "Performant_Isabelle_ML.Performant_Isabelle_ML", a copy of xxhash_checks.ML, and
     ROOT:  session S = HOL + sessions Performant_Isabelle_ML theories XXHash_Test
   run with  isabelle build -d <dir> S.
   Failure is an `error'; success is silence.  Needs library/native/build
   <platform> run once on this machine.  The pinned values live in
   xxhash_checks.ML, shared with the release workflow's verify job. *)
theory XXHash_Test
  imports "../Performant_Isabelle_ML"
begin

ML_file \<open>xxhash_checks.ML\<close>

ML \<open>XXHash_Checks.run ()\<close>

text \<open>A state used after its xxh128 returned raises Fail -- also from a Future
  still running, which never reaches freed C memory.\<close>

ML \<open>
  fun expect_fail what f =
    (case Exn.result f () of
      Exn.Exn (Fail _) => ()
    | Exn.Exn exn => error (what ^ ": expected Fail, got " ^ General.exnMessage exn)
    | Exn.Res _ => error (what ^ ": expected Fail, got a result"))

  val escaped = Unsynchronized.ref NONE
  val _ = XXHash.xxh128 (fn st => escaped := SOME st)
  val _ = expect_fail "update on an escaped state" (fn () => XXHash.update (the (! escaped)) "x")
  val _ = expect_fail "update_file on an escaped state" (fn () =>
    XXHash.update_file (the (! escaped)) (Path.explode "$ISABELLE_HOME/ROOTS"))

  val gate = Synchronized.var "gate" false
  val late = Unsynchronized.ref NONE
  val _ = XXHash.xxh128 (fn st =>
    late := SOME (Future.fork (fn () =>
      (Synchronized.guarded_access gate (fn b => if b then SOME ((), b) else NONE);
       Exn.result (XXHash.update st) "late"))))
  val _ = Synchronized.change gate (K true)
  val _ =
    (case Future.join (the (! late)) of
      Exn.Exn (Fail _) => ()
    | _ => error "update from a Future after xxh128 returned: expected Fail")
\<close>

text \<open>A missing file and a directory raise IO.Io.\<close>

ML \<open>
  fun expect_io what path =
    (case Exn.result (fn () => XXHash.xxh128 (fn st => XXHash.update_file st path)) () of
      Exn.Exn (IO.Io _) => ()
    | Exn.Exn exn => error (what ^ ": expected IO.Io, got " ^ General.exnMessage exn)
    | Exn.Res _ => error (what ^ ": expected IO.Io, got a digest"))

  val _ =
    Isabelle_System.with_tmp_dir "xxhash_test" (fn dir =>
      (expect_io "a missing file" (dir + Path.basic "missing");
       expect_io "a directory" dir))
\<close>

text \<open>Theory.resolve_theory finds the context's own theory although it is unfinished
  (Theory.check refuses it), an ancestor by base and by long name, and rejects an
  unknown name as Theory.check does.\<close>

ML \<open>
  val thy = \<^theory>
  val ctxt = \<^context>
  fun resolve name = Theory.resolve_theory ctxt (name, Position.none)

  val _ = Context.eq_thy (resolve (Context.theory_base_name thy), thy) orelse
    error "resolve_theory: the own theory by base name"
  val _ = Context.eq_thy (resolve (Context.theory_long_name thy), thy) orelse
    error "resolve_theory: the own theory by long name"
  val _ = can (Theory.check {long = false} ctxt) (Context.theory_base_name thy, Position.none) andalso
    error "Theory.check accepted the unfinished own theory: resolve_theory's bypass is no longer needed"

  val parent = hd (Theory.parents_of thy)
  val _ = Context.eq_thy (resolve (Context.theory_long_name parent), parent) orelse
    error "resolve_theory: an ancestor by long name"
  val _ = Context.eq_thy (resolve (Context.theory_base_name parent), parent) orelse
    error "resolve_theory: an ancestor by base name"
  val _ =
    (case Exn.result resolve "No_Such_Theory" of
      Exn.Exn (ERROR msg) =>
        String.isSubstring "Unknown ancestor theory" msg orelse
          error ("resolve_theory: unexpected error text: " ^ msg)
    | _ => error "resolve_theory: an unknown name was accepted")
\<close>

text \<open>The kind of this theory's own hash follows Resources.loaded_theory: WIP (the lowest
  bit of byte 0 set) when evaluated interactively; persistent under a batch build,
  which registers the session's own theories as loaded while it processes them
  (measured; Semantic_Embedding Test/Test_All.thy, the WIP boundary probe).\<close>

ML \<open>
  val _ =
    Theory_Hash.is_persistent (Theory_Hash.hash_of \<^theory>) =
      Resources.loaded_theory (Context.theory_long_name \<^theory>) orelse
    error "hash_of: the kind of this theory's hash disagrees with Resources.loaded_theory"
\<close>

end
