# Thread CPU clocks: what was measured

The evidence behind `library/thread_cpu.ML` and `library/native/thread_cpu.c`.
Every number below was observed; the headers of those two files state the
contract that follows from it and cite this file.  Dates are 2026-09-03.
Sections 3 and 4 were measured on the probe runners against the three entry
points of `library/native/thread_cpu.c` as they stand here (each section names
its run and commit); any change to what those entry points compute retires the
section and must be re-measured.  One change has been made since: the `TC_API`
export declarations at the top of thread_cpu.c, which enter no function body
and are empty off Windows -- the Windows export table they guarantee is checked
instead by `library/native/build`.

## 1. Why a per-thread clock at all

`Timing.result`'s `cpu` is `getrusage(RUSAGE_SELF)`: the whole process
(`polyml/src/libpolyml/timing.cpp:468`).  Wall clock charges a thread for the
machine's load and for everybody's garbage collections.  Measured on the
development machine (x86_64-linux, 14 cores, `isabelle ML_process -l Pure`):

```
burn  (alone)        : wall 500022 us, thread CPU 499521 us, wall-CPU    501 us, process GC meanwhile      0 us
churn (alone)        : wall 505022 us, thread CPU 475819 us, wall-CPU  29203 us, process GC meanwhile  24182 us
burn  (8 bg churners): wall 909961 us, thread CPU 160662 us, wall-CPU 749299 us, process GC meanwhile 657025 us
churn (8 bg churners): wall 558191 us, thread CPU  95313 us, wall-CPU 462878 us, process GC meanwhile 210571 us
apply 100 ms on a churner with 8 bg churners: TIMEOUT at CPU 100109 us, wall 576034 us
```

`burn` allocates nothing, `churn` allocates as fast as it can.  With eight other
threads churning, the non-allocating thread lost 657 ms of 910 ms wall to their
stop-the-world collections, and none of it appears on its own CPU clock.  Under
that pressure a 100 ms CPU budget fired at 100.1 ms of CPU while 576 ms of wall
had passed.

## 2. Linux (development machine, and ubuntu-latest as control)

Runner figures in this section come from the same run as section 3.  The
local overshoot and post-exit figures were taken with an earlier shape of the
test theory (wall-bounded burns); the current shape was re-run on the
development machine and stays inside them (20 samples of a 20 ms budget: min
64 us, max 106 us).

- Accuracy: a 40 ms wall burn reads 36-40 ms of CPU; 100 ms reads 100.005 ms on
  the runner.  A 50 ms sleep reads 26-62 us.  A parent reading a worker's clock
  saw 192 ms over 200 ms of its own busy wall.
- Resolution: nanoseconds (raw readings are not round).
- `Thread_CPU.apply`: 50 ms budget fired at 50.08-50.10 ms of CPU; 20 samples of
  a 20 ms budget overshot, across the two machines, by min 22-51 us, mean
  0.4-0.7 ms, max 1.0-1.8 ms (`poll_floor` is 1 ms; the rest is scheduling
  latency); eight concurrent
  budgets of 10..80 ms each fired within 1.1 ms of its own budget; nesting
  with `Timeout.apply` in both directions fires the inner one.
- After the thread ends: `pthread_join` returns when the kernel clears the tid
  word it waits on, a few microseconds before the task is released; in that
  window the clock still reads (observed once: the final total, immediately
  after the join), then `clock_gettime` fails with EINVAL and `read` is NONE
  (typically on the first read, at most 6 us after the join).
- The clockid is `(~tid << 3) | 6`, i.e. it encodes the thread id.  A clockid
  synthesised from another thread's id reads that thread, so a stale handle
  whose id has been recycled would read a stranger.  No recycling was observed
  in 2400 short-lived threads on the runner.  (This corrects an earlier note
  that concluded "no tid-reuse hazard" from the EINVAL observation alone.)
- One `tc_read`: 150-370 ns locally, 850 ns on the runner.

## 3. macOS, arm64 (macos-14, Apple M1) and Intel (macos-15-intel, i7-8700B)

Probe: `xqyww123/isabelle-packaging-ci`, workflow `thread-cpu-probe.yml`,
run 33718652056, commit 2d002e6.

- Compiles as-is with clang, `-Wall -Wextra`, zero warnings, both architectures.
- Accuracy: 100 ms burn reads 99.955 / 99.959 ms; 100 ms sleep reads 13 / 37
  us; cross-thread 98.6 / 98.9 ms over 100 ms of the parent's wall.
- Resolution: microseconds (`thread_basic_info` carries seconds + microseconds;
  every raw reading ends in 000).
- After the thread ends: `thread_info` fails on the first read after the join
  in all but one of six passes; once, the final total was still readable for
  0.134 ms.
- **Port-name reuse without a send right** (the branch as first written,
  `pthread_mach_thread_np` alone): after the worker ended, 27 of 2000 (arm64,
  1.35 %) and 50 of 2000 (Intel, 2.5 %) newly created threads received the dead
  worker's exact port name, and reading the stale handle while such a thread
  lived returned that thread's CPU (about 0.5 ms, exactly what it had been told
  to burn), not -1.  Reading afterwards returned -1, which is why a naive
  post-mortem check misses this.
- **With a send right** (`mach_port_mod_refs(..., MACH_PORT_RIGHT_SEND, 1)` in
  `tc_self`, `mach_port_deallocate` in `tc_free`; the shipped branch): zero
  collisions in 2000 threads on either architecture; `thread_info` still fails
  after the thread ends (-1); `mach_port_deallocate` returns KERN_SUCCESS.
  Positive control: after `tc_free` gave the right back, 9 of 400 (arm64) and
  7 of 400 (Intel) further threads received the name again -- the right is what
  prevents reuse, and a read after `free` is a use-after-free.
- One `tc_read`: about 670 ns on arm64, 1.4-1.9 us on Intel.

## 4. Windows (windows-latest, MSYS2 mingw-w64 gcc 16)

Same probe and run as section 3 (run 33718652056, commit 2d002e6 of
`xqyww123/isabelle-packaging-ci`); the earlier runs of that day
(commits 4f76ff2, e7df96a) agree on every Windows figure.

- Compiles as-is with mingw64 gcc, `-Wall -Wextra`, zero warnings.
- **Resolution of `GetThreadTimes` is the scheduler tick, 15.625 ms.**  In a
  200 ms tight loop of 614-685 thousand reads, 11-14 distinct values were
  seen; the smallest and the largest step between distinct values were both
  exactly 15625 us.  A 3 ms burn advanced the reading by 0 in 8-9 of 10 trials
  and by 15.625 ms in the rest.  `QueryThreadCycleTime` in the same loop
  changed on every read (step about 0.22 us at 2356 MHz) but counts cycles,
  not time; it was not adopted.  A 100 ms burn therefore reads 93.75 or
  109.375 ms depending on tick alignment.
- Sleep: exactly 0.
- After the thread ends: the duplicated handle keeps returning the final total
  (312.5 ms for a 300 ms burn), stable over 7.6 million reads in one second,
  across 2000 short-lived threads and 32 live ones; the handle's value is not
  reissued while it is open.  After `tc_free` (`CloseHandle`) a read returns
  -1 -- until the value is reissued: 71 of 400 later threads received it, and
  reading the freed handle then reported that thread (0, below one tick).
- One `tc_read`: 107-177 ns, the cheapest of the three platforms.

## 5. Not measured

- The macOS collision rate under Poly/ML's real thread-creation pattern (the
  1.4-2.5 % above is under a synthetic churn of 2000 threads).
- Whether raising the Windows timer resolution (`timeBeginPeriod`) changes what
  `GetThreadTimes` accumulates; the default was measured.
- The frequency and worst case of the post-join window on macOS (seen once).
