# Changelog

## 0.2.0 (unreleased)

- `Thread_CPU`: per-thread CPU clocks and a timeout charged in the calling
  thread's CPU (`library/thread_cpu.ML`).
- Poly/ML's `Foreign` is bound again below this session.
- The conda package now ships the native library `libperformant_isabelle_ml`
  prebuilt for x86_64-linux, arm64-linux, x86_64-darwin, arm64-darwin and
  x86_64-windows.  **The Linux builds require glibc 2.34 or newer** (Ubuntu
  22.04, Debian 12, RHEL 9, or later); **the macOS builds are stamped for macOS
  11.0 or newer** but were measured only on macOS 14 (arm64) and 15 (Intel).
  On an older system the first use of `Thread_CPU` reports the loader's error,
  and `library/native/build <platform>` inside the installed component builds
  a local copy with no such requirement.
- Also since 0.1.0: the race engine, the accounted timeout, Merely_Rewrite,
  PLPR_Pattern, the iNet collection functors, Theory_Data_With_Constructor,
  Event_Log / Exception_Log, and the `Performant_Isabelle_HOL` session (SSymb).

## 0.1.0 (2026-07-18)

- First release: the mutable hash tables and the iNet discrimination net,
  packaged for conda as the `Performant_Isabelle_ML` session.
