/*  test_thread_cpu.c -- self-test for the thread_cpu entry points, run by ./build.

    Loads the freshly built library the way Poly/ML will (dlopen) and checks
    only relations that hold under any machine load:
      1. a thread's own clock advances, and never faster than wall clock;
      2. a sleeping thread's clock stands still;
      3. another thread can read a worker's clock through the same handle
         (the reader sleeps between reads, so what it sees advance cannot be
         its own clock; the worker burns until told to stop);
      4. after the thread has ended the handle reads -1 (Linux/macOS);
      5. the dead thread's handle is not reissued to new threads while it is
         still held -- on macOS that is what the send right buys, and the
         probe reads the stale handle WHILE each new thread lives, because
         afterwards it reads -1 either way (ai-artifacts/THREAD_CPU_MEASUREMENTS.md).
    Every burn runs until the CLOCK UNDER TEST has advanced by a fixed amount,
    with a wall-clock backstop, so a loaded machine slows the test down instead
    of failing it; a clock that never advances trips the backstop.
    Prints the measurements; exit status 1 on any failure.                 */

#include <dlfcn.h>
#include <pthread.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

typedef int64_t (*self_fn)(void);
typedef int64_t (*read_fn)(int64_t);
typedef void    (*free_fn)(int64_t);

static self_fn tc_self;
static read_fn tc_read;
static free_fn tc_free;

static const double BACKSTOP_S = 10.0;   /* wall seconds before "the clock never advanced" */
static const int64_t MS = 1000000LL;

static double wall_now(void)
{
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + ts.tv_nsec / 1e9;
}

static volatile uint64_t sink;
static void work(void)
{
  uint64_t x = sink + 1;
  for (int i = 0; i < 1000; i++) x = x * 6364136223846793005ULL + 1442695040888963407ULL;
  sink = x;
}

static void nap_1ms(void) { struct timespec nap = {0, 1000000L}; nanosleep(&nap, NULL); }

/* Wait until clock h has advanced by `ns', running `each' between readings:
   work() burns the CALLER's clock, nap_1ms() burns nobody's.  Returns the
   advance actually read, or -1 if the handle could not be read or the
   backstop expired first. */
static int64_t advance_on(int64_t h, int64_t ns, void (*each)(void))
{
  int64_t start = tc_read(h);
  double t0 = wall_now();
  if (start < 0) return -1;
  for (;;) {
    int64_t now = tc_read(h);
    if (now < 0) return -1;
    if (now - start >= ns) return now - start;
    if (wall_now() - t0 > BACKSTOP_S) return -1;
    each();
  }
}

static volatile int64_t shared_handle;   /* volatile: the parent spins on it */
static volatile int stop_worker;

static void *worker(void *arg)
{
  (void)arg;
  double t0 = wall_now();
  shared_handle = tc_self();
  while (!stop_worker && wall_now() - t0 < BACKSTOP_S) work();
  return NULL;
}

/* A short-lived thread for the reuse probe: burns 0.5 ms of its own clock,
   and stays alive until released so the parent can read the stale handle
   while this thread holds whatever name it was given.  The free comes last:
   a probe thread that returned its handle before the parent's read would
   hide the regression this probe exists to catch, since an over-release
   destroys the recycled name and the parent then reads -1. */
static volatile int probe_alive, probe_release;
static void *probe_thread(void *arg)
{
  (void)arg;
  int64_t h = tc_self();
  advance_on(h, MS / 2, work);
  probe_alive = 1;
  while (!probe_release) { struct timespec nap = {0, 100000L}; nanosleep(&nap, NULL); }
  tc_free(h);
  return NULL;
}

int main(int argc, char **argv)
{
  if (argc != 2) { fprintf(stderr, "usage: %s LIBRARY\n", argv[0]); return 1; }
  void *lib = dlopen(argv[1], RTLD_NOW);
  if (!lib) { fprintf(stderr, "dlopen failed: %s\n", dlerror()); return 1; }
  tc_self = (self_fn)dlsym(lib, "tc_self");
  tc_read = (read_fn)dlsym(lib, "tc_read");
  tc_free = (free_fn)dlsym(lib, "tc_free");
  if (!tc_self || !tc_read || !tc_free) { fprintf(stderr, "missing symbol\n"); return 1; }

  int failures = 0;

  /* 1. own clock: advances, and no faster than wall */
  int64_t h = tc_self();
  if (h == 0) { fprintf(stderr, "tc_self failed\n"); return 1; }
  double t0 = wall_now();
  int64_t cpu = advance_on(h, 50 * MS, work);
  double wall_ms = (wall_now() - t0) * 1e3;
  if (cpu < 0) { printf("own thread:   FAIL: the clock could not be read, or never advanced by 50 ms in %.3f s\n", wall_now() - t0); return 1; }
  printf("own thread:   clock advanced %.3f ms in %.3f ms of wall\n", cpu / 1e6, wall_ms);
  if (cpu / 1e6 > wall_ms + 0.5) { printf("  FAIL: clock ran faster than wall\n"); failures++; }

  /* 2. sleeping accrues no CPU */
  int64_t s0 = tc_read(h);
  struct timespec nap = {0, 100 * 1000000L};
  nanosleep(&nap, NULL);
  int64_t s1 = tc_read(h);
  printf("sleep:        100 ms of sleep advanced the clock %.3f ms\n", (s1 - s0) / 1e6);
  if (s1 - s0 > 5 * MS) { printf("  FAIL: a sleeping thread accrued CPU\n"); failures++; }
  tc_free(h);

  /* 3. cross-thread read; 4. the handle after the thread has ended */
  pthread_t t;
  shared_handle = 0;
  stop_worker = 0;
  if (pthread_create(&t, NULL, worker, NULL) != 0) { fprintf(stderr, "pthread_create failed\n"); return 1; }
  t0 = wall_now();
  while (shared_handle == 0 && wall_now() - t0 < BACKSTOP_S) { /* wait for the worker to publish its handle */ }
  if (tc_read(shared_handle) < 0) {
    printf("cross-thread: FAIL: the parent cannot read the worker's handle while the worker is alive\n");
    failures++;
  } else {
    int64_t own = tc_self();
    int64_t own0 = tc_read(own);
    t0 = wall_now();
    int64_t seen = advance_on(shared_handle, 50 * MS, nap_1ms);   /* the parent watches the worker's clock */
    int64_t own_spent = tc_read(own) - own0;
    tc_free(own);
    if (seen < 0) { printf("cross-thread: FAIL: the worker's clock never advanced by 50 ms in %.3f s\n", wall_now() - t0); failures++; }
    else {
      printf("cross-thread: worker clock advanced %.3f ms as read by the parent, which spent %.3f ms of its own CPU\n",
             seen / 1e6, own_spent / 1e6);
      if (own_spent * 5 >= seen) { printf("  FAIL: the parent read its own clock, not the worker's\n"); failures++; }
    }
  }
  stop_worker = 1;
  pthread_join(t, NULL);
  /* pthread_join returns when the kernel clears the thread's tid word, a few
     microseconds BEFORE the task itself is released; until then the clock
     still reads.  So: poll, and report how long the handle outlived the join. */
  t0 = wall_now();
  int64_t after;
  int reads = 0;
  do { after = tc_read(shared_handle); reads++; } while (after != -1 && wall_now() - t0 < 1.0);
  printf("after exit:   handle invalid after %.3f ms and %d read(s) (last value %lld)\n",
         (wall_now() - t0) * 1e3, reads, (long long)after);
  if (after != -1) { printf("  FAIL: handle still reads 1 s after join\n"); failures++; }

  /* 5. name reuse while the stale handle is still held: 400 short-lived
     threads, the stale handle read while each one lives. */
  int collisions = 0, probes = 0;
  t0 = wall_now();
  for (int i = 0; i < 400 && wall_now() - t0 < BACKSTOP_S; i++) {
    pthread_t p;
    probe_alive = 0; probe_release = 0;
    if (pthread_create(&p, NULL, probe_thread, NULL) != 0) break;
    while (!probe_alive) { /* the probe thread burns its 0.5 ms */ }
    if (tc_read(shared_handle) >= 0) collisions++;
    probe_release = 1;
    pthread_join(p, NULL);
    probes++;
  }
  printf("reuse probe:  %d of %d new threads made the dead worker's handle readable\n", collisions, probes);
#if defined(__APPLE__)
  if (probes < 400) {
    printf("  FAIL: only %d of 400 probe threads ran in %.3f s; the send-right check proves nothing\n",
           probes, wall_now() - t0);
    failures++;
  }
  if (collisions) { printf("  FAIL: the macOS send right is missing: a new thread was given the dead worker's port name\n"); failures++; }
#endif
  tc_free(shared_handle);

  /* read cost */
  h = tc_self();
  t0 = wall_now();
  for (int i = 0; i < 1000000; i++) sink = (uint64_t)tc_read(h);
  printf("read cost:    %.0f ns per tc_read\n", (wall_now() - t0) * 1e9 / 1e6);
  tc_free(h);

  printf(failures ? "FAILED\n" : "OK\n");
  return failures ? 1 : 0;
}
