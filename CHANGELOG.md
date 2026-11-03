# Changelog

## Unreleased

- `Theory_Hash` moved here from Isabelle_RPC (`library/theory_hash.ML`), all but
  `store_theory_hash`, which stays there as `Theory_Hash_Store.store_theory_hash`;
  every hash is the same, bit for bit.  A persistent hash is now computed natively
  by the new `XXHash` (`library/xxhash.ML`: streaming XXH3 128-bit through
  `library/native/xxhash.c`, which vendors xxHash v0.8.3) -- no RPC host, and no
  fallback: without the native library `hash_of` raises an ERROR naming
  `library/native/build <platform>`.
- Git checkouts: re-run `library/native/build <platform>` after pulling, then restart
  Isabelle (a running process keeps the library it loaded).  A library built before
  this release reports an undefined symbol `xxh128_create`.
- `Theory.resolve_theory` (`library/resolve_theory.ML`; Isabelle's `Theory` is
  reopened): `Theory.check`, except that the context's own theory is found even while
  unfinished.  It replaces Isabelle_RPC's `Theory_Hash.resolve_theory`.
- The native library's self-test runs on all five targets, Windows included
  (`test_xxhash`), and the release workflow's verify job runs on all five too, so
  each platform's library is also called from Isabelle/ML before a release.

## 0.2.1 (2026-11-02)

- Requires Isabelle2026 (conda: `isabelle >=2026,<2026.1`).
- `library/rescue_foreign.ML` is gone: Isabelle2026 no longer hides Poly/ML's
  `Foreign`, so every session sees it without this library.

## 0.2.0 (2026-10-03)

- `Thread_CPU`: per-thread CPU clocks, `timing`/`cpu_timing` measuring the
  calling thread's CPU, and `apply {thread_cpu, wall}`, a timeout charged in
  the calling thread's CPU with an optional wall-clock limit for liveness
  (`library/thread_cpu.ML`).
- Poly/ML's `Foreign` is bound again below this session.
- `Dynamic_Array`: mutable growable arrays with stack, middle insert/delete,
  stable in-place sort and binary search (`library/dynamic_array.ML`).
- The conda package now ships the native library `libperformant_isabelle_ml`
  prebuilt for x86_64-linux, arm64-linux, x86_64-darwin, arm64-darwin and
  x86_64-windows.  **The Linux builds require glibc 2.34 or newer** (Ubuntu
  22.04, Debian 12, RHEL 9, or later); **the macOS builds are stamped for macOS
  11.0 or newer** but were measured only on macOS 14 (arm64) and 15 (Intel).
  On an older system the library does not load: `Thread_CPU.self` is NONE,
  `timing` reports no thread CPU, and `apply` enforces only its wall-clock
  limit (warning, with the loader's error) or fails when given none;
  `library/native/build <platform>` inside the installed component builds a
  local copy with no such requirement.
- Also since 0.1.0: the race engine, the accounted timeout, Merely_Rewrite,
  PLPR_Pattern, the iNet collection functors, Theory_Data_With_Constructor,
  Event_Log / Exception_Log, and the `Performant_Isabelle_HOL` session (SSymb).

## 0.1.0 (2026-07-18)

- First release: the mutable hash tables and the iNet discrimination net,
  packaged for conda as the `Performant_Isabelle_ML` session.
