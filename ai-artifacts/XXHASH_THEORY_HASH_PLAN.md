# Native xxh128 in Performant_Isabelle_ML, and Theory_Hash moving here (plan, 2026-11-02)

Status (2026-11-03): every design point APPROVED by the owner (section 3), including the decisions on plan
review 1 (section 9). Both reviews' fixes are in this text; the re-review (section 9a) ruled the plan ready.
IMPLEMENTATION STARTED 2026-11-03 (steps of section 5 in order). Not committed (plans may be; decide at
commit).

## 1. What this work is

The persistent theory hash is computed in Python today (ML asks the Python RPC host). This work computes it
in ML instead, through a streaming xxh128 interface whose C half lives in Performant_Isabelle_ML's native
library and reads files itself. Once no hash needs Python, Theory_Hash's computing part moves into
Performant_Isabelle_ML; Isabelle_RPC keeps only the parts that talk to Python, under the new name
Theory_Hash_Store. resolve_theory leaves Theory_Hash for a reopened `Theory` structure.

## 2. Background (verified 2026-11-02)

The theory hash is a theory's 16-byte identity; every universal key in the semantic DB starts with it.
Two kinds, told apart by the lowest bit of byte 0:
- Persistent hash (the theory is in a heap or a session build: `Resources.loaded_theory` true):
  xxh128 over the long name, one NUL byte, the raw bytes of the theory's .thy file, then each parent's
  persistent hash in `Theory.parents_of` order; then the lowest bit of byte 0 cleared. Today: ML
  (contrib/Isabelle_RPC/Tools/theory_hash.ML, hash_of) calls the RPC procedure "xxhash128_theory" with
  (long name, File.platform_path of the file, parent hashes); Python
  (Isabelle_RPC_Host/theory_hash.py:19-49 theory_xxhash128) does `h = xxhash.xxh128(); h.update(name
  utf-8); h.update(b"\0"); h.update(file bytes); for ph in parents: h.update(ph); d = digest; d[0] &= 0xFE`.
  The file is read from DISK at hash time (situation 3 of the header: a stale heap hashes the new file).
- WIP hash (`Resources.loaded_theory` false): FNV-1a 128 of the long name (Term_Digest.string128), lowest
  bit of byte 0 set. Computed in ML. Unchanged by this work.

Bit-identity is MANDATORY: persistent hashes prefix the keys of the published semantic DB
(isabelle-semantic-data) and of every user DB, and the theory-hash registry (theory_hash.lmdb) maps them to
names. One differing bit silently re-keys everything.

Why Theory_Hash cannot move today: it calls RPC, and Isabelle_RPC is built on Performant_Isabelle_ML
(`session Isabelle_RPC = Performant_Isabelle_ML +`). With the hash computed natively, only three parts
still need RPC: store_theory_hash (RPC command "Theory_Hash.store": for a theory and all its ancestors,
Theory.nodes_of, send (hash, long name) pairs; Python writes them into theory_hash.lmdb) and two global
callbacks registered for Python ("Theory_Hash.theory_name_of", "Theory_Hash.process_serial_of").

Other facts:
- Isabelle merges the ML name tables of a theory's parents with Symtab.merge (K true) (ml_env.ML:78-86):
  on a name clash the FIRST parent's binding wins. So two different structures under one name, one per
  session, resolve by import order (review 1, C5; reproduced by two agents). A structure that exists only
  in the global name space (Pure's Theory, Timeout) plus one theory-level binding has no clash.
- Nobody catches Cannot_Hash (git grep over all contrib repos).
- No live Python code computes a theory hash: the only caller of theory_xxhash128 is the RPC procedure;
  Semantic_Embedding and isasearch-web Python only read hashes ML produced (keys, theory_hash.lmdb).
  isabelle-rpc depends on python-xxhash only for this (conda/recipe.yaml:217, pyproject.toml:33).
- python-xxhash 3.6.0 (installed here) bundles libxxhash 0.8.2; XXH3/XXH128 output is frozen since 0.8.0.
  XXH3 streaming over pieces gives the same digest as one-shot over their concatenation; Python's digest()
  is the canonical big-endian form (C: XXH128_canonicalFromHash).
- Isabelle2026 File.read / File_Stream use BinIO (byte-exact); ML strings are UTF-8 bytes.
  File.platform_path = ML_System.platform_path o (Path.implode o Path.expand) (file.ML:40-41); on Windows
  it raises Fail "Unknown environment variable CYGWIN_ROOT" for some absolute paths (ml_system.ML:52);
  File.is_file runs it outside its own `can` (file.ML:89, :94).
- Context.get_theory (context.ML:353-359) errors "Unfinished theory" on the context's own unfinished
  theory; today's resolve_theory (theory_hash.ML:84-93) bypasses that and infers long/base from ".".
  Theory.check_theory {get, all} ctxt (name, pos) is exported (theory.ML:20, :148-161): it calls `get`,
  turns an ERROR into one with position and completion, and reports the theory's markup at pos.
- Copies of resolve_theory / get_theory_path elsewhere: Semantic_Embedding interpret_command.ML:43-51
  resolve_root (adds only a real position); Semantic_Embedding theory_structure.ML:32-48 resolve_theory
  (no live caller) and :50-59 get_theory_file_path (= File.platform_path o get_theory_path);
  Isabelle_RPC context.ML:1572-1576 inline in a callback.
- Native library: library/native/ holds thread_cpu.c, test_thread_cpu.c, build, README. `./build TARGET`
  compiles the `sources`, links a staged file, self-tests it (POSIX targets) or checks the PE export table
  (x86_64-windows), and installs TARGET/libperformant_isabelle_ml.so (performant_isabelle_ml.dll on
  Windows). TARGET = ML_PLATFORM minus a compact "_32". Built products are gitignored; the conda package
  (noarch) ships all five, built by release-conda.yml's `native` job (five runners; Windows under msys2
  MINGW64). Thread_CPU loads it lazily with Foreign.loadLibraryIndirect (thread_cpu.ML:139-160) and
  degrades to "no clock" when it cannot. The Linux builds need GLIBC_2.34 (pthread_getcpuclockid); owner:
  accepted, settled long ago -- not to be raised again.
- Poly/ML memoises a loaded library, and dlopen returns the existing handle for a path even after the
  file is replaced: a running Isabelle keeps a stale library until restarted (review 1, verified there).
- Isabelle2026 binds Foreign itself (ML_Bootstrap.thy:17,33); Performant_Isabelle_ML's old rescue hack
  was deleted in c5ddc1d (0.2.1). Nothing else to remove (owner's request of 2026-11-02, checked).
- Tests in Performant_Isabelle_ML/Test are run by hand, not in ROOT. The release workflow's `verify` job
  runs on ubuntu only and calls Thread_CPU against the installed package (Check_Native, generated as
  `session Check_Native = Performant_Isabelle_ML`, release-conda.yml:462); nothing in CI loads the Windows
  DLL today. Precedents for a pre-publish Windows leg: Semantic_Embedding/.github/workflows/
  release-conda.yml's verify job (:243-430, maintained, win-64, builds a HOL-based session) and this
  workflow's own smoke job (:545-561: isabelle.bat dispatch, /cygdrive conversion). A native Windows path
  given to -d fails Path.explode (Isabelle_RPC release-conda.yml:483-487).
- Published (conda.qiyuan.me, 2026-11-02): performant-ml 0.2.1, isabelle-rpc 0.5.2 (both Isabelle2026);
  no Isabelle2026 build of isabelle-semantic-embedding or isabelle-minilang exists. Caps on performant-ml:
  isabelle-rpc, auto-sledgehammer 0.3.0 and Semantic_Embedding all say `>=0.2.0,<0.3.0`; Semantic_Embedding
  says `isabelle-rpc >=0.5.0` (no cap); Isa-Mini `isabelle-rpc >=0.5.1`.
- Users of the moving names: Isabelle_RPC (context.ML:314, :1188, :1571 resolve_theory; Universal_Key.ML:308
  alias used at :796, :803; list_theory_hash_app.ML; tests Test_Cache_Scope, Test_Name_Spaces:31,
  Test_Universal_Key, Test_Thm_Key_Cache); Semantic_Embedding (semantic_store.ML:2425 resolve_theory;
  interpret_command.ML resolve_root; store_theory_hash at interpret_command.ML:93,
  semantic_interpretation_app.ML:95, semantic_store.ML:2435; hash_of/is_persistent/process_id elsewhere;
  Test/Entity_Position_Refusal_Test.thy comment names "xxhash128_theory").

## 3. Owner rulings (verbatim where it matters)

Origin (RPC port session): "Theory_Hash 应该整体被挪动到 Performant ML 里"; on the content hash: "你觉得把这个算法
直接放在 ML 里会是个好主意吗？xxhash128 是有 C 库的对吗？我们可以写个计算 theory hash 的 C 库，然后链接到 xxxhash 的库，
然后提供给 Isabelle 最后实现进 Performant ML 里你觉得如何？"; lookups do not belong in Theory_Hash ("语义是不一样的").

2026-11-02, the design rounds:
- Round 2: "需要流式吗？"; "我建议 C 代码负责包括遍历 thy 文件，读取 thy 文件在内的所有工作。要跨平台编写。然后直接暴露一个
  接口供 ML 调用。如果 Python 端需要的话，也可以走 CPython 调用同一份 C 你觉得如何？"; xxhash compiled in, not a system
  libxxhash: "没问题。编译也行"; load failure -> ERROR naming the build command, no fallback: "赞同";
  "此外我建议把 C 代码编进 Thread_CPU 一个库。库名可讨论"; "Python 端不需要调用了吗？"
- Round 3: "遍历" = "读完这个文件的内容"; "那我建议给 Isabelle/ML 暴露的接口也是流式的。接口 signature 定一下";
  library name kept: "赞同不改名"; delete the Python implementation now: "好"; "赞同第 5 条：拆分方式";
  "赞同第 6 条：resolve_theory 改放进重新打开的 Theory 结构，并加上位置参数"; "第 7 条我反对 Native_Library，建议各个
  structure 各自维护各自的" (each structure keeps its own loading code); "第八条你可以自决。允许任意使用 cslh19".
- Round 4: the XXHASH signature with xxh128 owning the state's lifetime: "批准"; the composition in ML, no
  th_persistent_hash: "好".
- Round 5 (decisions on plan review 1):
  1. "赞同单独建 Theory_Hash_Store" -- relaxes round 3's split: no same-name Theory_Hash in Isabelle_RPC.
  2. glibc: "接受 2.34 而且这个问题早就讨论过。也跟你没关系啊，你重新拿出来干嘛？" -- nothing changes; do not raise.
  3. Windows ML-level check: "按你建议来" = a permanent, ungated windows-latest leg of performant-ml's
     `verify`, before publish (section 6.3).
  4. Load-ERROR text: "按你建议来" = section 4.2's text.
  5. Recipe license fields: "一起做建议，按你建议来" = a separate task fixing all four recipes together
     (section 10), not part of this plan.

## 4. The design (all approved)

### 4.1 C: library/native/xxhash.c in libperformant_isabelle_ml

xxhash.h of xxHash v0.8.3 (github.com/Cyan4973/xxHash, tag v0.8.3; BSD-2-Clause, notice in its header)
vendored unmodified under library/native/; README records URL, tag, the file's SHA-256 and the license.
Compiled in with XXH_INLINE_ALL, so none of its symbols is exported. Exported (Windows:
__declspec(dllexport), as thread_cpu.c does):

    void *xxh128_create(void);                             /* fresh state, seed 0; NULL if out of memory */
    void  xxh128_update(void *st, const uint8_t *buf, size_t len);
    int   xxh128_update_file(void *st, const char *path);  /* path: UTF-8, platform form; 0, or errno */
    void  xxh128_digest(void *st, uint8_t out[16]);        /* canonical big-endian */
    void  xxh128_free(void *st);

xxh128_update_file opens in binary mode and feeds the file in 64 KiB blocks, never holding it whole; a
read error (ferror) is a failure, so a directory or an unreadable file never hashes as empty. On Windows
the UTF-8 path is converted to UTF-16 (MultiByteToWideChar, CP_UTF8, MB_ERR_INVALID_CHARS; failure ->
EINVAL) and opened with _wfopen(L"rb"); elsewhere fopen("rb"). Failure returns errno (EIO when errno is
0). Python, if it ever needs these, calls the same functions through ctypes (not built now).

### 4.2 ML: library/xxhash.ML, structure XXHash

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

Implementation:
- Its own loading code (round-3 ruling), the same shape as thread_cpu.ML:139-160: platform directory from
  ML_System.platform minus "_32", Foreign.loadLibraryIndirect, symbols via getSymbol + buildCallN, and a
  wrapper turning Foreign.Foreign into ERROR with the text (round 5):
      <loader message>
      build (or rebuild) it with library/native/build <platform>, then restart Isabelle
  (Thread_CPU's text stays: its symbols are in every library version.)
- state = a `Foreign.Memory.voidStar option Synchronized.var`, NONE meaning freed -- one source of truth
  (precedent event_log.ML). update and update_file make their C call inside Synchronized.change and raise
  Fail on NONE, so an escaped state (even from a Future still running after xxh128 returned) never reaches
  freed C memory, and concurrent updates cannot interleave inside the C state.
- xxh128, in Thread_CPU's uninterruptible shape: create (NULL -> ERROR); run f with interrupts restored,
  captured with Exn.capture0; then ONE Synchronized.change_result that digests if f succeeded, frees and
  sets NONE, all under the lock; finally the captured result is released.
- update passes the bytes (Byte.stringToBytes, a cast) with Foreign.cByteArray; update_file passes
  File.platform_path p with cString; nonzero result -> IO.Io {name = the platform path, function =
  "XXHash.update_file", cause = OS.SysErr ("errno " ^ code, NONE)}.
- Concurrent use is serialized and memory-safe, but the digest then depends on the order of the updates.

### 4.3 Theory_Hash in Performant_Isabelle_ML: library/theory_hash.ML

The computing part of today's Theory_Hash, moved; exactly one Theory_Hash exists in every context:

    signature THEORY_HASH = sig
      type hash = Word8Vector.vector
      exception Cannot_Hash of theory
      val hash_of : theory -> hash
      val hash_of_long : Context.generic -> string -> hash
      val theory_of : hash -> theory option
      val is_persistent : hash -> bool
      val hasher : hash -> word
      val to_hex : hash -> string
      val process_id : unit -> string
      val get_theory_path : theory -> Path.T
    end
    structure Theory_Hash : THEORY_HASH

The persistent branch of hash_of, handler layout fixed:
1. Today's guarded block stays (theory_hash.ML:211-216), yielding the Path.T: get_theory_path plus
   File.is_file inside the catch-all `\<^try> ... catch _ => raise Cannot_Hash thy`. Its comment says that
   File.is_file runs the same File.platform_path update_file runs later (file.ML:41, :89), so a Windows
   path-conversion failure becomes Cannot_Hash here.
2. Outside that block:

       XXHash.xxh128 (fn st =>
         (XXHash.update st name;
          XXHash.update st "\000";
          XXHash.update_file st file;
          List.app (XXHash.update st o Byte.bytesToString) parent_hashes))
       handle IO.Io _ => raise Cannot_Hash thy

   then the lowest bit of byte 0 cleared. No handler in hash_of catches the loader's ERROR. Callers that
   turn lookup errors into NONE (Context_Callbacks.entry_of_name, context.ML:308; ns_filter, :1097;
   Isa-Mini's retrieve, agent_server.ML `try`) treat it like any other lookup error -- entries without
   keys; the paths without such a handler report it with its build command.
The memo (cache by theory identifier, hash_to_thy), the WIP branch, theory_of, hasher, to_hex, process_id,
get_theory_path move unchanged; the header moves with "computed via Python RPC" replaced by "computed
natively by XXHash", situations 1-3 unchanged. hash_of_long's registry miss calls
Theory.resolve_theory (Context.proof_of context) (long, Position.none). No RPC anywhere: a persistent hash
no longer needs a Python host.

### 4.4 Theory.resolve_theory: library/resolve_theory.ML

Performant_Isabelle_ML reopens Isabelle's Theory (precedent: accounted_timeout.ML reopens Timeout; no clash
by section 2):

    structure Theory = struct open Theory
      (* Theory.check, except that the context's own theory is found even when
         unfinished; long name iff the name contains ".". *)
      val resolve_theory : Proof.context -> string * Position.T -> theory
    end

Body, built on Pure's hook (as Theory.check itself is): thy = Proof_Context.theory_of ctxt; long =
{long = String.isSubstring "." name}; self = Context.theory_name long thy; then
Theory.check_theory {get = fn a => if a = self then thy else Context.get_theory long thy a,
all = fn () => map (Context.theory_name long) (thy :: Theory.ancestors_of thy)} ctxt (name, pos).
So the markup report at pos covers the own theory too; lookup, error text and the long/base rule are
today's.

### 4.5 Isabelle_RPC after the move: Theory_Hash_Store (round 5, relaxation of round 3)

Tools/theory_hash.ML holds no Theory_Hash any more:

    structure Theory_Hash_Store : sig val store_theory_hash : theory -> unit end
    (* store_cmd ("Theory_Hash.store") + store_theory_hash, as today *)

plus the two global callbacks, unchanged (names "Theory_Hash.theory_name_of" and
"Theory_Hash.process_serial_of" are RPC wire names; they call Theory_Hash.theory_of from
Performant_Isabelle_ML). Why not a same-name Theory_Hash: section 2 (first parent wins; Minilang_AoA
imports Minilang before Isabelle_RPC). The name follows the code's existing term: Python's
open_theory_hash_store and the procedure "Theory_Hash.store". Wire names and Python untouched.
resolve_theory call sites switch to Theory.resolve_theory: context.ML:314, :1188 (`try`), :1571;
Universal_Key.ML:308 alias (or its two uses); Test_Name_Spaces:31.

### 4.6 Python

Delete theory_xxhash128, the procedure "xxhash128_theory" and `import xxhash` from
Isabelle_RPC_Host/theory_hash.py; drop python-xxhash from conda/recipe.yaml and pyproject.toml.
is_persistent, theory_name_of, the "Theory_Hash.store" procedure and the registry stay.
list_theory_hash.py: delete the host thread, --rpc-addr and the then unused imports (no host needed).

### 4.7 Unchanged

Every hash value (bit for bit), the WIP hash, the memo, reading the file from disk at hash time, the
lookup order of hash_of_long, the Python registry, the RPC wire names and the callbacks.

## 5. Implementation steps

Performant_Isabelle_ML:
1. library/native: xxhash.h (v0.8.3, vendored), xxhash.c (4.1), test_xxhash.c (6.1).
   build: add xxhash.c to `sources`; build test_xxhash per target (binary name set in the target's case
   branch: test_xxhash, test_xxhash.exe on Windows) and run it on ALL five targets against the staged
   library; keep the POSIX-only test_thread_cpu and the Windows 64-bit-PE + tc_* export check unchanged;
   create a scratch directory with mktemp -d, pass it to test_xxhash, remove it in the existing EXIT trap.
   Residue: .gitignore and conda/recipe.yaml's residue rm list exactly library/native/test_xxhash and
   library/native/test_xxhash.exe (never a glob: test_xxhash* would match test_xxhash.c).
   README: two sources; the library is now required by Theory_Hash; the Windows DLL is loaded before
   release (test_xxhash); xxhash.h provenance. build's header and Windows comment updated likewise.
2. library/xxhash.ML (4.2), library/resolve_theory.ML (4.4), library/theory_hash.ML (4.3); load order in
   Performant_Isabelle_ML.thy after hash_table.ML and term_digest.ML: xxhash.ML, resolve_theory.ML,
   theory_hash.ML; Performant_Isabelle_ML.thy:10-11 ("optional") updated.
3. Test/xxhash_checks.ML (no theory header; ONE copy of every check value, shared by XXHash_Test and the
   CI check, 6.4): pinned XXHash digests (a string whole and split; a file the check writes itself, larger
   than 64 KiB, with CR, LF and 0x1A bytes), the golden theory hashes, Main's recomputation procedure
   (6.4). Test/XXHash_Test.thy (by hand; `imports "../Performant_Isabelle_ML"`, on logic HOL, so Main
   comes from a heap and this checkout's sources are tested; its header documents the batch recipe
   measured on cslh19 -- a scratch copy with the session-qualified import and a ROOT
   `session S = HOL + sessions Performant_Isabelle_ML`)
   loads it with ML_file and adds: an escaped state (also via a Future used
   after xxh128 returned) -> Fail, a missing file and a directory -> IO.Io; Theory.resolve_theory on the
   own theory, an ancestor and an unknown name (ERROR "Unknown ancestor theory"). Main's golden value
   comes from 6.2.
4. release-conda.yml: `verify` becomes a matrix over ubuntu-latest and windows-latest (6.3), both legs
   the same steps; Check_Native's parent becomes Performant_Isabelle_HOL, and it loads a copy of
   Test/xxhash_checks.ML (actions/checkout, copy that file only; the code under test is the installed
   package) plus the Thread_CPU read. Reworded lines, by rule: the native job's header; every line naming
   thread_cpu.ML as the code that computes the library's directory or file name (name both loaders); the
   lines describing a missing library only as a missing clock (release-conda.yml:344-346,
   recipe.yaml:89-93; add the hash_of ERROR); the Windows DLL is now loaded before release.
5. SKILL.md, Readme.md and .claude/skills/performant-isabelle-ml/SKILL.md entries (XXHash, Theory_Hash,
   Theory.resolve_theory); recipe about.description; CHANGELOG `## Unreleased`: Theory_Hash moved here; a
   persistent hash_of needs the native library (no RPC host, no fallback); git checkouts re-run
   library/native/build <platform> after pulling and restart Isabelle; a stale library reports an
   undefined symbol xxh128_create.

Isabelle_RPC:
6. Tools/theory_hash.ML reduced to 4.5; resolve_theory call sites of 4.5; context.ML:1572-1576's inline
   path code -> File.platform_path (Theory_Hash.get_theory_path thy).
7. FIRST 6.2 on cslh19 (file level and theory level) on the trees of steps 1-6 while the Python procedure
   is still present; on any difference stop and report to the owner. Its theory level yields Main's golden
   value for step 3 and confirms the other three against the live RPC path. Then: Python per 4.6;
   conda/recipe.yaml:199 ("The five pyproject dependencies") and :202 (the xxhash mapping) with it;
   registry.md's xxhash128_theory row; the skill's references/modules.md and SKILL.md
   (Theory_Hash and XXHash live in Performant_Isabelle_ML; Theory_Hash_Store here); stale test comments
   and messages (Test_Cache_Scope.thy:6-10 and :63-68 -- its last check's message says the persistent
   xxh128 branch was not exercised --, Test_Universal_Key.thy:11-14, Test_Thm_Key_Cache.thy:7-9).
8. conda/recipe.yaml: performant-ml floor = the new release; under a 0.3.0 the `<0.3.0` cap moves too.

Semantic_Embedding (check its working tree first: another agent may be porting it):
9. store_theory_hash -> Theory_Hash_Store.store_theory_hash at interpret_command.ML:93,
   semantic_interpretation_app.ML:95, semantic_store.ML:2435; semantic_store.ML:2425 ->
   Theory.resolve_theory (Context.proof_of context) (name, Position.none); interpret_command.ML: delete
   resolve_root and its comment, call Theory.resolve_theory ctxt (name, pos); theory_structure.ML: delete
   the dead resolve_theory (and its signature line), get_theory_file_path = File.platform_path o
   Theory_Hash.get_theory_path; Test/Entity_Position_Refusal_Test.thy comment; recipe floors. Its own
   build/test only if it builds on Isabelle2026 then.

All three:
10. Sweep: /usr/bin/grep -rnI -i over Isabelle_RPC, Performant_Isabelle_ML and Semantic_Embedding (not
    archive, ai-artifacts, build products, backups) for xxhash128_theory, theory_xxhash128,
    Theory_Hash.store_theory_hash, Theory_Hash.resolve_theory, 'RPC host', 'Python host', 'round trip',
    'entry points', 'optional', 'xxhash', 'thread_cpu.ML' (judge a thread_cpu.ML hit only where a line says
    which code locates or loads the native library); every hit updated or justified.
11. After step 9: 6.2's test-theory runs and mutation check on cslh19.

## 6. Verification (mine to decide, round 3)

6.1 C self-test (every `./build`, all five targets): test_xxhash takes the staged library (argv[1]) and
the scratch directory (argv[2]) and resolves the five xxh128_* names at run time (dlopen/dlsym on POSIX,
LoadLibrary/GetProcAddress under _WIN32), so the Windows DLL is loaded before release. Expected digests
pinned from python-xxhash for inputs covering every XXH3 length class (0, 1-3, 4-8, 9-16, 17-128, 129-240,
241-1024, multi-block > 1 MiB); the same inputs fed in random splits give the one-shot digest; files of
those lengths via xxh128_update_file (a 0-byte file, one larger than the 64 KiB block), a file with a
non-ASCII name (on Windows created with _wfopen and a literal wide name, never a narrow fopen of UTF-8
bytes), a missing file and a directory (both nonzero).

6.2 One-off differential on cslh19, BEFORE the Python path is deleted (isolated environment as in the RPC
port: /var/tmp/<new dir>, copies of the trees, own USER_HOME, `isabelle build -v -j 2 -o threads=10`):
- File level: every .thy of Isabelle2026 and the AFP: name + NUL + file through the new C library (ctypes
  harness, scratch) vs Python theory_xxhash128(name, path, []); byte-identical for all.
- Theory level: a scratch session on the new trees with the old Python procedure still present: for every
  theory reachable from heaps Pure, HOL, HOL-Library (built there), Performant_Isabelle_ML, Isabelle_RPC,
  native hash_of vs the old RPC path recomputed alongside; results written to a file, not writeln.
- Any difference: no switch, report to the owner.
- The test theories of both repositories run there; mutation check: the C self-test must fail for a wrong
  digest, a dropped byte and a dropped read-error check.
- Only if the owner picks a 0.2.x version: build Isabelle_RPC at tag v0.5.2 and the current
  auto_sledgehammer (git archive) on the new Performant_Isabelle_ML there and run Isabelle_RPC's test
  theories -- the pairing conda would hand out.

6.3 Windows ML level (round 5): performant-ml's `verify` job is a matrix over ubuntu-latest and
windows-latest, the two legs running the same steps (re-review OD-R4: owner left the layout to me, "具体
实现上的，在不改变设计的前提下，你可以自决"; chosen: both legs build Performant_Isabelle_ML and
Performant_Isabelle_HOL -- the win-64 isabelle package ships the HOL heap, so only SSymb.thy and the check
are built -- and one Check_Native whose parent is Performant_Isabelle_HOL). The Windows leg is not gated by
an input, and no Windows step swallows a failure (no continue-on-error, no `exit /b 0`, no check that only
warns); publish already needs verify. It installs the locally built package (precedents in section 2:
Semantic_Embedding's verify job, this workflow's smoke job). The check's session directory reaches -d as
a relative path (cd "$RUNNER_TEMP"; build -d chk ...), because a native Windows path fails Path.explode;
isabelle.bat keeps the working directory (CHERE_INVOKING). Check_Native loads Test/xxhash_checks.ML
(6.4) and asserts with `error`, never writeln: every value there, plus the Thread_CPU read. On Windows,
Main's hash covers the bytes of every .thy Main depends on in the win-64 package.

6.4 Golden theory hashes (permanent, ONE copy in Test/xxhash_checks.ML, loaded by XXHash_Test and by
Check_Native on both legs): Theory_Hash.to_hex must equal
- Pure: a2d0ad12bc775ef1191131f7e739c4be
- ML_Bootstrap: 8a33ba2baf891d7a6d3dc3d302eb6882 (raw byte 0 is 0x8b: tests the bit clear and an appended
  parent hash)
- Pure.Sessions: ae76da35940e1bff0bff0b39580308ac (long name; the base-name variant would be
  a832920181cfa6823a6f5e3f32a80000)
- Main: several parents, parents_of order (value from 6.2).
Values from review 1's recomputation; the final values are taken from the live Python RPC path during 6.2
and cross-checked with python-xxhash -- never copied from the new hash_of. Comment next to them: golden
values over Isabelle2026's stock sources; a mismatch on an unchanged Isabelle means the formula changed,
which re-keys every DB. At an Isabelle upgrade: Pure, ML_Bootstrap and Pure.Sessions are recomputed
directly from their single files with the header's formula; Main with the recorded procedure (in the same
file): an ML block that, for Main and every ancestor, writes the long name, File.platform_path of
Theory_Hash.get_theory_path, and the long names of Theory.parents_of in order to a file (no hash_of, no
XXHash, a file, not writeln), plus a few lines of python-xxhash folding that list bottom-up with the
formula. Run once during 6.2: its Main value must equal the live RPC path's.

## 7. Review, commits, release

- After implementation: the owner's two-turn adversarial code review; fixes I may decide go back to review
  before committing; nothing changes before the owner agrees. The CHANGELOG texts are shown with it.
- Commits on the default branch of each repo, push origin only; new files need per-file approval
  (xxhash.h, xxhash.c, test_xxhash.c, xxhash.ML, resolve_theory.ML, theory_hash.ML, XXHash_Test.thy,
  xxhash_checks.ML); MLML pointers with `git add -u`.
- Report to the owner when done: other git checkouts (cslh19's shared one, the MBZUAI fleet) need
  library/native/build and an Isabelle restart when next pulled -- the owner's operational call; until
  then some entity lookups there return entries without keys, next to the loud ERROR elsewhere (4.3).
- Download counter (conda session's rule, notified 2026-11-02): pause before every run that downloads from
  the channel (SKILL conda-release section 4), but do NOT resume it (skip that step of section 10); the
  conda session resumes it after all releases. Until it announces the switch to conda-ci.qiyuan.me.
- Release order (on the owner's order, SKILL conda-release): performant-ml, then isabelle-rpc (floor on
  the new performant-ml), then Semantic_Embedding when it is released for Isabelle2026. Version numbers
  are the owner's. Facts for that choice (conda.qiyuan.me, 2026-11-02): no Isabelle2026 build of
  isabelle-minilang or isabelle-semantic-embedding exists, so a performant-ml 0.3.0 breaks no existing
  install; but under 0.3.0 auto-sledgehammer 0.3.0's `<0.3.0` cap and the new isabelle-rpc's floor cannot
  both hold, and conda then silently falls back to isabelle-rpc 0.5.2 + performant-ml 0.2.1 rather than
  failing, until auto-sledgehammer's cap moves. Under a 0.2.x every cap holds, and conda may pair the new
  performant-ml with isabelle-rpc 0.5.2 (tested in 6.2). Removing Theory_Hash.resolve_theory and
  Theory_Hash.store_theory_hash breaks no published package.

## 8. Working rules

- Design elements need explicit approval; pure implementation choices with no design/functional impact are
  mine ("不影响设计，不影响功能的，只是纯粹的实现技术的，没有任何代价/坏处的，就完全不需要跟我讨论啊").
- Settled questions are not re-raised (round 5, glibc).
- Test everything testable, on cslh19 (its shared MLML checkout is old -- never touch it).
- No `isabelle build` on this machine without the owner's command; never -c/-f.

## 9. Plan review 1 (workflow wf_af0e3e7a-e7d, 2026-11-02; Opus xhigh, 4 reviewers, 15 merged concerns,
## one defender each, judge): not ready; owner decided round 5; fixes applied above

Full JSON: the run's journal.jsonl under the session's subagents/workflows/wf_af0e3e7a-e7d/.
Owner decisions: OD1/C5 -> 4.5 Theory_Hash_Store; OD2/C9 -> nothing (glibc settled); OD3/C2 -> 6.3;
OD4/C12 -> 4.2 ERROR text; OD5/C13 -> section 10.
Agent fixes applied: A1 (4.2 comments, 4.3 handler layout), A2 (6.4), A3 (4.2 Synchronized.var), A4 (4.4
check_theory), A5 (steps 6, 9), A6 (6.1, step 1), A7 (4.1, 6.1, step 3), A8 (step 1), A9 (steps 1, 2, 5,
section 7), A10 (4.1), A11 (steps 7, 10, 4.6), A12 (section 7, 6.2).
The judge asked for a focused re-review of: 6.3, 6.4, 4.2's state, 6.1's run-time loading, 4.5.
Rejected by the judge (not to be re-raised): C1's premise and its fix (a), C2 (c)(f), C3's details, C4's
is_file-as-guard, C8's fact, C9's scope, C10's details, C11's glob, C12's fleet step, C13 in scope, C14
overreach, C15's shadow framing.

## 9a. Plan re-review (workflow wf_9509e31a-f5d, 2026-11-02; 3 reviewers, 9 merged concerns, one
## defender each, judge): READY once the agent fixes are written in by hand. OD-R4 left to me by the
## owner (2026-11-03) -> same steps on both legs (6.3). All fixes R1-R8 now written into the text above.

Full JSON: journal.jsonl under subagents/workflows/wf_9509e31a-f5d/. Judge: R2/R3 are minor (each fails
loudly in the first dry run; publish needs verify); the three Pure golden values re-computed and correct.
- Owner decision OD-R4 (R2 + R4): where Main's golden hash runs in CI. Options: same steps on both legs,
  Check_Native's parent Performant_Isabelle_HOL (DEVIATES from the approved Windows-leg cost; judge's
  recommendation); two sessions Check_Native (both legs) + Check_Main (Linux only); no Main in CI.
- Agent fixes, not yet applied (no plan re-review needed): R1 scope 4.3's last sentence (callers with
  `handle ERROR _ => NONE` -- context.ML:308, :1097, Isa-Mini retrieve -- see missing keys) + a clause in
  section 7's report; R2 write the OD-R4 layout into 6.3/6.4/step 4, XXHash_Test's header names its heap;
  R3 precedents = Semantic_Embedding's verify job (:243-430) and this workflow's smoke (:545-561), -d as a
  relative path, no Windows step swallows a failure; R5 one shared ML file under Test/ for the check values,
  loaded by XXHash_Test and copied into the CI check (new file -> approval list); R6 record Main's
  independent recomputation (ML dump of names/paths/parents_of + python-xxhash fold), run once in 6.2;
  R7 schedule 6.2 at the start of step 7 and the test runs/mutation check after step 9; R8 header text
  "computed natively by XXHash", sweep terms 'xxhash' and 'thread_cpu.ML', step 4's line rule, Isabelle_RPC
  recipe.yaml:199/:202.
- Rejected: R9 (rename theory_hash.ML), R1-b (a load probe at heap build), R3's five-dispatch list, R5's
  session-qualified import, R7's slot, R8's extra terms.

## 9b. Implementation record (2026-11-03)

cslh19 isolated environment: /var/tmp/xxhash2026 (src/ copies, home/ USER_HOME with both copies in
etc/components, run_build.sh, runtest/ and diff/ scratch sessions, logs).
- Steps 1-3 done locally: library/native/{xxhash.h (v0.8.3, SHA-256 17973c0d...e4b, same as the release
  tarball's), xxhash.c, test_xxhash.c, build}; library/{xxhash.ML, resolve_theory.ML, theory_hash.ML};
  Performant_Isabelle_ML.thy load order; Test/{xxhash_checks.ML, XXHash_Test.thy}.
  XXHash_Test does not run 6.1's vectors: the XXH3 length classes are decided in C and checked by
  test_xxhash on every build; xxhash.ML has no length-dependent code; its marshalling is pinned by
  xxhash_checks.ML (every byte value including NUL, split updates, a file over 64 KiB) and the
  golden hashes; a second copy would break the one-copy rule (code review K7).
  Native build: here and on cslh19, both self-tests OK; only tc_* and xxh128_* exported. Mutation check
  of test_xxhash (here): reversed digest bytes, a dropped byte in update, a dropped byte in the file
  read, no ferror check -- each fails the build and installs nothing.
- Batch runs need a scratch session with a session-qualified import (a path import into another
  session's directory is "Implicit use of directory" in batch builds; the Test theories are meant for
  interactive use, as before). XXHash_Test (copy) on cslh19: all checks pass. Its WIP check was wrong at
  first: under a batch build the session's own theories are Resources.loaded_theory (Semantic_Embedding
  Test_All.thy precedent); now it checks that the hash kind follows Resources.loaded_theory.
- Step 6 done locally (Theory_Hash_Store, resolve_theory call sites); Isabelle_RPC builds on cslh19.
- 6.2 file level: 12522 .thy files (Isabelle2026/src + afp-2026-10-26/thys, 349 MB) identical; harness
  mutation-checked (without the NUL, and a flipped bit: all differ).
- 6.2 theory level: 283 theories (Pure, HOL, HOL-Library from the registry + Performant_Isabelle_ML,
  Isabelle_RPC, the scratch theory as ancestors) native hash_of == old Python path, 0 different. Main
  7038a01d75d8546b0858d3c5d0078089 by the native path, the live Python RPC path, and the independent
  recomputation (dump_graph + the Python fold) -- now in Test/xxhash_checks.ML.
- Semantic_Embedding: another session ("semantic embedding 2026") is porting it, uncommitted, in the
  same files; I sent it the step-9 list and did not edit. It reports an owner-approved Isabelle_RPC
  change of its own (its "Part 0": context.ML entry_of_name/entry_def_pos, Test_Name_Spaces.thy,
  isabelle-rpc 0.5.3) touching the same two files as step 6 -> commit order and which release carries
  what: the owner decides (the other session asked the owner).
- Mistake: ran `isabelle process_theories` with no arguments locally to see its usage; it ran an
  empty ad-hoc session "Draft" (no theories, 1 s). Reported to the owner.
- Steps 4, 5, 7, 10 done locally: verify matrix (ubuntu + windows, Check_Native on
  Performant_Isabelle_HOL loading a checked-out Test/xxhash_checks.ML, plus a failing control
  session); README, Readme/SKILL x3, recipe (summary, description, residue names, comments),
  .gitignore, CHANGELOG `## Unreleased`; Python theory_xxhash128 / "xxhash128_theory" / python-xxhash
  removed (recipe, pyproject), list_theory_hash.py without a host; Isabelle_RPC skill docs and test
  comments. Sweep: remaining hits are about RPC hosts in general, not theory hashing.
- Final runs on cslh19 (trees with Python deleted): Isabelle_RPC + Isabelle_RPC_Test build OK
  (0 legacy; the 11 context.ML warnings are the old ones shifted by one line; theory_hash.ML:219's
  old warning moved to Performant_Isabelle_ML with the code); XXHash_Test with Main OK; RPC pytest
  13 passed (with isabelle on PATH); C mutation check repeated on cslh19 (3 mutants fail, nothing
  installed; original passes). The local library/native/x86_64-linux rebuilt (superset).
- Not yet run anywhere: the release workflow (needs a dry run on GitHub; the owner orders releases).
- Step 8 is OPEN, blocked on the owner's version number, and is done before isabelle-rpc's dispatch:
  0.2.1 lacks Theory_Hash and Theory.resolve_theory, so the floor rises with the next isabelle-rpc
  release; under a 0.3.0 the `<0.3.0` cap moves too, and the recipe comment then names the first
  release that ships both. Step 9 is with the "semantic embedding 2026" session; step 11 follows it.

## 9c. Code review 1 (workflow wf_e2863292-b53, 2026-11-03; 4 reviewers, 11 merged concerns K1-K11,
## one defender each, judge): acceptance MET once the agent fixes are applied (K2, K6 re-reviewed)

Full JSON: journal.jsonl under subagents/workflows/wf_e2863292-b53/. Owner (2026-11-03): K10 "按你建议来";
on the rest "不需要跟我讨论的我不予置评" -> all fixes applied (K1-K11 as below).
- Owner decision K10: CHANGELOG's first bullet should say store_theory_hash stays in Isabelle_RPC as
  Theory_Hash_Store.store_theory_hash [judge: add the clause; Isabelle_RPC's removals go into its
  commit message, no Isabelle_RPC CHANGELOG].
- Agent fixes: K1 XXHash_Test header documents the measured batch recipe (scratch dir, qualified
  import copy, `session S = HOL + sessions Performant_Isabelle_ML`), interactive line only once seen
  to pass; plan step 3's example fixed. K2 digest via Foreign.Memory.alloca (re-review; re-run the
  checks). K4 theory_hash.ML header "loaded theories (heap or session build)", the marker comment,
  drop the repeated Path.explode paragraph. K5 resolve_theory.ML: precise no-clash sentence, inline
  ascription `sig include THEORY val resolve_theory ... end`. K6 test_xxhash.c: chdir(SCRATCH_DIR),
  relative names only, no CP_ACP conversion (re-review; rebuild, wine runs, mutation check). K7 step 3
  and 9b: XXHash_Test does not run 6.1's vectors (one-copy rule). K8 the ancestor-by-base-name check
  uses the parent, plus a mutation check of it. K9 Isabelle_RPC test headers name the native library
  as the requirement. K11 9b: step 8 open until the owner names the version.
- Rejected: K3 (the approved guarded block and its old warning), K2-b, K4-b, K5-b, K6-b, K7-b, K10-b,
  K11-b, K1-b.
- After the fixes: local build + mutation check OK; mingw cross-build under wine OK (ASCII dir, and a
  Chinese dir under code page 936; under 1252 a Chinese dir fails loudly at chdir, accepted as K6-b);
  cslh19: native build, Performant_Isabelle_ML, Isabelle_RPC, Isabelle_RPC_Test OK (0 legacy),
  XXHash_Test copy OK, two resolve_theory mutants fail it (the second exactly at the new
  ancestor-by-base-name check). Interactive run on HOL NOT verified: Isabelle-MCP fails here with
  "No module named 'fastmcp.server.tasks.routing'".
- Re-review (workflow wf_bd32a1b7-2c3): acceptance MET; one comment fix (test_xxhash.c, the chdir
  comment overclaimed "no code-page conversion"), applied; no rebuild or further review needed.
- Owner, 2026-11-03: new files approved ("批准", the 8 files + this plan); order "按你建议来吧":
  Performant_Isabelle_ML commits now; Isabelle_RPC only after the "semantic embedding 2026" session's
  Part 0 is committed and isabelle-rpc 0.5.3 released. Measured: the new Performant_Isabelle_ML with
  Isabelle_RPC's committed HEAD builds Isabelle_RPC + Isabelle_RPC_Test green (cslh19, home2/).
  The other session applies Part 0 to the working tree AND the index (Tools/context.ML,
  test/Test_Name_Spaces.thy), so my uncommitted edits stay and Part 0 is not undone later; before
  committing Isabelle_RPC, re-run the cslh19 tests on the tree with Part 0 in it.
- Order confirmed by the owner in the other session ("确认", relayed 2026-11-03): (1) Part 0 alone on
  Isabelle_RPC main, released as isabelle-rpc 0.5.3; (2) my Isabelle_RPC commit on top; (3) the
  Semantic_Embedding port commits against 0.5.3 with the old Theory_Hash names; (4) I apply step 9 to
  Semantic_Embedding after that port commit. Part 0 is not implemented yet (the port has open design
  questions); the other session messages me when 0.5.3 is out.
- conda session, 2026-11-03 (download-counter fix phase 2, owner-approved): CI downloads move to
  https://conda-ci.qiyuan.me (not counted). Isabelle_RPC done in 380435a (release-conda.yml only; my
  uncommitted edits intact). For Performant_Isabelle_ML the conda session adds a 5-line commit ON TOP
  of my commit (both -c conda.qiyuan.me in verify -> conda-ci, plus step/job names): tell it when my
  commit is pushed. A dry run on a commit before that conversion cannot be reused: dry-run the latest
  commit after it. Until the conda session announces the switch, pause the counter as before.
- Commit drafts shown to the owner; awaiting approval. Also asked: a GitHub dry run of
  performant-ml's release (the only check of the other four platforms; macOS ML level stays unchecked).

## 10. Separate tasks and pending items

- Recipe license fields (owner, round 5: separate task, all four together): Performant_Isabelle_ML,
  auto_sledgehammer, Isabelle_RPC and isabelle-packaging-ci recipes say BSD-3-Clause. LICENSE files:
  Performant_Isabelle_ML MIT, auto_sledgehammer LGPL, Isabelle_RPC and isabelle-packaging-ci none -- the
  intended license of those two must be asked when the task starts. performant-ml then also lists
  BSD-2-Clause for xxhash.h.
- From the RPC port (asked, unanswered): record the downstream same-kind fixes and this task in
  MLML/ai-artifacts/ISABELLE2026_MIGRATION_PLAN.md?; Isabelle/VSCode as a dialog responder: this session
  or another?; delete cslh19:/var/tmp/isabelle_rpc_port2026?
