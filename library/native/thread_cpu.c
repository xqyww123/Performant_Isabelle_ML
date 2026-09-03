/*  thread_cpu.c -- per-thread CPU clocks for Isabelle/ML (library/thread_cpu.ML).
    Part of libperformant_isabelle_ml, the native half of Performant_Isabelle_ML;
    tc_ abbreviates thread_cpu.

    Three entry points, identical on every platform, so the ML side needs no
    platform switch of its own:

      tc_self()    an opaque handle for the CALLING thread's CPU clock.  Must run
                   ON the thread being measured.  Returns 0 on failure.  The
                   handle is valid process-wide: any other thread may pass it to
                   tc_read.  That is what makes a watchdog thread possible.
      tc_read(h)   CPU nanoseconds consumed by that thread, or -1 if the handle
                   cannot be read.
      tc_free(h)   release the handle.  Exactly once, after the last read.

    A handle is meaningful while its thread lives.  Read it and free it before
    the thread ends; what a read returns afterwards differs per platform (below),
    and a read AFTER tc_free is a use-after-free on macOS and Windows: the
    handle's value is recycled to a new thread and the read reports that thread.

    Why a C shim at all: each platform reports thread CPU through a different
    struct (timespec / thread_basic_info / FILETIME).  Encoding those layouts
    by hand in ML is where this would rot: Foreign.Memory's accessors index in
    units of the read width, not bytes, and getting that wrong returns
    plausible-looking garbage rather than an error.  Here the headers define
    the layouts.

    Per-platform contract.  Every figure is measured (Linux locally and on a
    GitHub runner; macOS arm64 and Intel, and Windows, on GitHub runners); the
    numbers and the probe are in archive/THREAD_CPU_MEASUREMENTS.md.

      Linux    clockid from pthread_getcpuclockid; nanosecond resolution.  Once
               the thread is gone clock_gettime fails (EINVAL) and tc_read is
               -1.  The clockid encodes the thread id, so after the id is
               recycled a stale handle would read a stranger; no recycling was
               observed in 2400 short-lived threads.  tc_free is a no-op.
      macOS    the thread's Mach port, with a SEND RIGHT taken by tc_self and
               released by tc_free.  Microsecond resolution.  Once the thread
               has exited thread_info fails and tc_read is -1.  The right is
               what keeps the port name from being reissued: without it, 1.4-2.5%
               of new threads received the dead thread's exact name, and a read
               of the stale handle then reported the NEW thread's CPU.  Holding
               the right makes that impossible; releasing it (tc_free) makes it
               possible again, hence the rule above.
      Windows  a duplicated thread handle read with GetThreadTimes.  Resolution
               is the scheduler tick, 15.625 ms: every step measured exactly
               15625 us, and a 3 ms burn read as 0 in 8-9 of 10 trials.  A CPU
               budget there is meaningful only in multiples of that tick (a
               few tens of ms and up); that is accepted, not worked around --
               QueryThreadCycleTime is ~0.2 us fine but counts cycles, not time.
               The handle keeps the thread's final total readable after it
               exits, until tc_free closes it; after that the handle value is
               reissued (71 of 400 new threads received it), hence the rule.   */

#include <stdint.h>

#if defined(_WIN32)
/* Windows resolves these by name (GetProcAddress).  Declared exported here so
   the export table is guaranteed rather than inherited from ld's export-all
   default, which any later dllexport or .def would switch off. */
#define TC_API __declspec(dllexport)
#else
#define TC_API
#endif

TC_API int64_t tc_self(void);
TC_API int64_t tc_read(int64_t h);
TC_API void tc_free(int64_t h);

#if defined(_WIN32)

#include <windows.h>

int64_t tc_self(void)
{
  HANDLE dup;
  /* GetCurrentThread() is a pseudo-handle, meaningful only to the calling
     thread; duplicate it so a watchdog thread can use it. */
  if (!DuplicateHandle(GetCurrentProcess(), GetCurrentThread(),
                       GetCurrentProcess(), &dup,
                       THREAD_QUERY_INFORMATION, FALSE, 0))
    return 0;
  return (int64_t)(intptr_t)dup;
}

int64_t tc_read(int64_t h)
{
  FILETIME creation, exit, kernel, user;
  ULARGE_INTEGER k, u;
  if (h == 0) return -1;
  if (!GetThreadTimes((HANDLE)(intptr_t)h, &creation, &exit, &kernel, &user))
    return -1;
  k.LowPart = kernel.dwLowDateTime; k.HighPart = kernel.dwHighDateTime;
  u.LowPart = user.dwLowDateTime;   u.HighPart = user.dwHighDateTime;
  /* FILETIME counts 100 ns units. */
  return (int64_t)((k.QuadPart + u.QuadPart) * 100ULL);
}

void tc_free(int64_t h)
{
  if (h != 0) CloseHandle((HANDLE)(intptr_t)h);
}

#elif defined(__APPLE__)

#include <pthread.h>
#include <mach/mach.h>

int64_t tc_self(void)
{
  mach_port_t port = pthread_mach_thread_np(pthread_self());
  if (port == MACH_PORT_NULL) return 0;
  /* pthread_mach_thread_np hands out the name without a reference; take one,
     so the name stays ours until tc_free and cannot be reissued meanwhile. */
  if (mach_port_mod_refs(mach_task_self(), port, MACH_PORT_RIGHT_SEND, 1) != KERN_SUCCESS)
    return 0;
  return (int64_t)port;
}

int64_t tc_read(int64_t h)
{
  thread_basic_info_data_t info;
  mach_msg_type_number_t count = THREAD_BASIC_INFO_COUNT;
  if (h == 0) return -1;
  if (thread_info((thread_act_t)h, THREAD_BASIC_INFO,
                  (thread_info_t)&info, &count) != KERN_SUCCESS)
    return -1;
  return (int64_t)(info.user_time.seconds + info.system_time.seconds) * 1000000000LL
       + (int64_t)(info.user_time.microseconds + info.system_time.microseconds) * 1000LL;
}

void tc_free(int64_t h)
{
  if (h != 0) mach_port_deallocate(mach_task_self(), (mach_port_t)h);
}

#else  /* Linux and other POSIX with per-thread CPU clocks */

#include <pthread.h>
#include <time.h>

int64_t tc_self(void)
{
  clockid_t cid;
  if (pthread_getcpuclockid(pthread_self(), &cid) != 0) return 0;
  /* A thread CPU clockid is never 0 (that is CLOCK_REALTIME), so 0 is free to
     mean failure. */
  return (int64_t)cid;
}

int64_t tc_read(int64_t h)
{
  struct timespec ts;
  if (h == 0) return -1;
  if (clock_gettime((clockid_t)h, &ts) != 0) return -1;   /* EINVAL once the thread is gone */
  return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

void tc_free(int64_t h) { (void)h; }

#endif
