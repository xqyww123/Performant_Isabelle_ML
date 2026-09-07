(*  Title:  library/thread_cpu.ML
    Author: Qiyuan Xu (with AI assistance)

The CPU clock of one thread, a measurement in it, and a timeout charged in it.

WHY.  Timing.result's cpu is getrusage(RUSAGE_SELF): the whole process, all
workers at once (polyml timing.cpp:468).  A single-threaded computation
running beside other workers cannot be metered by it, and wall clock charges
it for the machine's load and for everybody's garbage collections: Poly/ML's
GC stops the world, and a thread that allocated nothing lost 657 ms of 910 ms
wall to other threads' GCs, none of it on its own CPU clock (measured;
ai-artifacts/THREAD_CPU_MEASUREMENTS.md holds every figure cited here).  The
operating system keeps a CPU clock per thread; this module reads it.

THE MECHANISM.  library/native/thread_cpu.c, three C entry points that are
the same on Linux, macOS and Windows: tc_self yields a process-wide handle to
the CALLING thread's CPU clock, tc_read reads it in nanoseconds, tc_free
releases it.  Because the handle is valid from any thread, one manager thread
can watch every guarded computation, which is what makes `apply' possible.
The C header states the per-platform contract; the parts a caller must know
are in the signature comment below.

The library is libperformant_isabelle_ml, found under
library/native/<platform>/ next to this file, where <platform> is ML_PLATFORM
with a compact-object "_32" stripped from the architecture: Isabelle's stock
default is ML_system_64 = false, so ML_PLATFORM is then x86_64_32-linux while
the directory is x86_64-linux (this machine runs ML_system_64 = true and
reports x86_64-linux directly).  Build it once per machine with
library/native/build <platform> (the conda package ships all five prebuilt;
library/native/README has the details).  It is loaded lazily on first use,
so a heap builds without it.

WITHOUT A CLOCK -- no library, or the operating system refusing this thread
one -- `self' is NONE, a measurement reports no thread CPU, and `apply', if a
CPU limit was asked for at all, enforces only its wall-clock limit (with a
warning) or raises an error when it was given none.  Whether the clock is
there is asked of the loader on every `self': the dlopen handle and symbol
addresses are memoised in volatile refs that Poly/ML resets on heap load
(ForeignMemory.sml:127-135), and a memo of our own would survive in a heap
built on a machine without the library and misreport every machine with it.
A failed attempt costs one failing dlopen.

Foreign itself is hidden by Pure; library/rescue_foreign.ML puts it back and
must precede this file.  Compiled code holds values, not names, so a heap built
from this file works in any later process whether or not the name is bound
there (Isabelle's own SHA1 rests on the same fact, sha1.ML:150-177).

THE TIMEOUT.  `apply {thread_cpu, wall} f x' runs f x under two limits: it
raises Timeout.TIMEOUT once the calling thread has spent `thread_cpu' of CPU
inside it, and -- when `wall' is given -- once `wall' of wall clock has
passed, whichever comes first.  The wall limit is the outer of the two and is
Timeout.apply itself (the accounted one, library/accounted_timeout.ML, which
precedes this file); it exists for liveness, since a thread that blocks -- on
an external prover, a lock, a remote call -- accrues no CPU and would never
reach a CPU limit.  The CPU limit has the shape of Timeout.apply
(timeout.ML:34-56) with Event_Timer replaced by a manager of our own.
Event_Timer cannot serve: its event runs inside Event_Timer's own lock, so it
cannot re-arm itself, and a CPU deadline can only be approached by repeated
wall-clock waits.  The manager waits for the smallest time remaining among
the registrations -- a thread never accrues more CPU than wall time (except
on Windows, where the tick-based clock can credit a thread a whole 15.625 ms
tick it did not fully run), so that wait never runs past a deadline --
re-reads every clock, fires what is due, and waits again.  Each wait is at
least poll_floor (1 ms) so a starved thread does not turn the manager into a
spinner; a limit therefore overshoots by at most poll_floor plus scheduling
latency, plus one tick on Windows (measured on idle Linux machines: 22 us to
1.8 ms of CPU beyond a 20 ms limit, over 20 samples).  One manager thread
serves every registration; it is forked on demand and lives on, exactly as
Event_Timer's does, and like Event_Timer's it is revived by the next register
or cancel if found dead (after a heap reload, say).

Firing is Isabelle_Thread.interrupt_thread on the registered thread, and the
outcome is judged as Timeout.apply judges it: TIMEOUT iff the registration
had fired AND a proper interrupt surfaced, from the body or from the flush
(Isabelle_Thread.expose_interrupt_result) afterwards.  In addition, as
accounted_timeout.ML does for Timeout.apply, a Breakdown surfacing after the
registration fired -- from either limb -- is claimed as our interrupt with
its break flag lost; one predicate judges both limbs so they cannot drift.
*)

signature THREAD_CPU =
sig
  (* A thread's CPU clock: the CPU time the operating system has charged to
     that one thread, monotonic, standing still while the thread sleeps,
     blocks, or is stopped by a garbage collection.

     `self' must run ON the thread to be measured and yields a handle to that
     thread's clock -- NONE without a clock (see WITHOUT A CLOCK above);
     `the_self' is the same clock, or the error saying why there is none.
     The handle is valid process-wide: any thread may `read' it, which is
     what lets one thread watch another.  A reading is the thread's lifetime
     total, so an interval is the difference of two readings.  `free'
     releases the handle: exactly once, after the last read -- a read after
     `free' reports whatever new thread has been given the handle's value
     (macOS, Windows).

     A clock is meant to be read while its thread lives.  Once the thread is
     gone `read' is NONE on Linux and macOS -- within 6 us of the join on
     Linux, once 0.134 ms later on macOS, whose worst case is not measured --
     and on Windows the final total until `free'.  That is what was observed,
     not a guarantee: the handle is an operating-system name (a clockid
     encoding the thread id, a Mach port name, a Windows handle value), and
     once the system reissues that name a read reports the new owner's total;
     the macOS send right and the Windows handle hold the name until `free',
     on Linux nothing does.  All of this is measured
     (ai-artifacts/THREAD_CPU_MEASUREMENTS.md).

     Resolution: nanoseconds on Linux, microseconds on macOS, and on Windows
     the 15.625 ms scheduler tick -- a Windows limit is meaningful only in
     multiples of that tick.  Time.time itself carries microseconds. *)
  type clock
  val self: unit -> clock option
  val the_self: unit -> clock
  val read: clock -> Time.time option
  val free: clock -> unit

  (* Run f x and measure it.  `thread_cpu': the calling thread's CPU inside
     f -- NONE without a clock (no wall-clock stand-in), and excluding garbage
     collection, even of the body's own allocation.  The other three are
     Timing.timing's figures; `cpu' and `gc' are process-wide (WHY above).
     An exception passes through unmeasured. *)
  type timing = {thread_cpu: Time.time option, elapsed: Time.time, cpu: Time.time, gc: Time.time}
  val timing: ('a -> 'b) -> 'a -> timing * 'b
  val cpu_timing: ('a -> 'b) -> 'a -> Time.time option * 'b

  (* Run f x; raise Timeout.TIMEOUT once the calling thread has spent
     `thread_cpu' of CPU inside it, or once `wall' has elapsed when given.
     Only this thread's CPU counts: work in Future/Par_List is invisible and
     a blocked thread never reaches the limit -- give `wall' where liveness
     matters.  As in Timeout.apply, a limit under 1 ms is ignored
     (Timeout.ignored) and timeout_scale scales both.  Without a clock only
     `wall' is enforced, with a warning on every call, or an error when there
     is no `wall' either; an ignored `thread_cpu' never consults the clock.
     Either limit raises Timeout.TIMEOUT -- carrying CPU spent, or wall
     elapsed -- and when both deadlines nearly coincide the outer wall limit
     may claim the inner one's unwinding (Timeout.apply's own nesting
     behaviour, timeout.ML:47-55). *)
  val apply: {thread_cpu: Time.time, wall: Time.time option} -> ('a -> 'b) -> 'a -> 'b
end

structure Thread_CPU: THREAD_CPU =
struct

(** the C library **)

local
  open Foreign

  (*ML_PLATFORM with the compact-object "_32" stripped: the process is still
    64-bit and takes the same library (see the header)*)
  val platform =
    (case space_explode "-" ML_System.platform of
      [arch, os] => perhaps (try (unsuffix "_32")) arch ^ "-" ^ os
    | _ => ML_System.platform)

  val path =
    Resources.master_directory \<^theory> + Path.make ["library", "native", platform,
      if ML_System.platform_is_windows then "performant_isabelle_ml.dll"
      else "libperformant_isabelle_ml.so"]

  val library = loadLibraryIndirect (fn () => File.platform_path path)

  (*the handler sits on the calls, as sha1.ML:193-195 puts it: the library and
    its symbols are memoised thunks and resolve at the first call.  A load
    failure names the path tried, so it is not repeated here*)
  fun explain call x =
    call x handle Foreign.Foreign msg =>
      error (msg ^ "\nbuild it on this machine with library/native/build " ^ platform)
in
  val tc_self = explain (buildCall0 (getSymbol library "tc_self", (), cInt64))
  val tc_read = explain (buildCall1 (getSymbol library "tc_read", cInt64, cInt64))
  val tc_free = explain (buildCall1 (getSymbol library "tc_free", cInt64, cVoid))
end


(** clocks **)

abstype clock = Clock of int
with

(*the calling thread's clock, or the ERROR saying why there is none (the
  loader's message, or the OS refusal); anything else is a fault, re-raised*)
fun self_or_reason () =
  (case Exn.result (fn () =>
      (case tc_self () of
        0 => error "Thread_CPU: the operating system refuses a CPU clock for this thread"
      | h => Clock h)) () of
    res as Exn.Exn (ERROR _) => res
  | Exn.Exn exn => Exn.reraise exn
  | res => res)

(*nanoseconds, or NONE once the handle cannot be read*)
fun read_ns (Clock h) = (case tc_read h of ~1 => NONE | ns => SOME ns)

fun free (Clock h) = tc_free h

end

fun self () = Exn.get_res (self_or_reason ())
fun the_self () = Exn.release (self_or_reason ())

val read = Option.map Time.fromNanoseconds o read_ns

(*the calling thread's own clock, just obtained: a read fails only once the
  thread is gone (thread_cpu.c), which it is not*)
fun read_own clock =
  (case read_ns clock of
    SOME ns => ns
  | NONE => raise Fail "Thread_CPU: impossible: own clock unreadable")

(*run body uninterruptibly on the calling thread's clock (or the ERROR),
  freed exactly once, on every exit; `run' restores the caller's interrupts
  for the body's own work.  capture0, not the managed capture: that one
  consumes the break flag, which apply's flush must still see
  (accounted_timeout.ML)*)
fun with_clock body =
  Thread_Attributes.uninterruptible_body (fn run =>
    (case self_or_reason () of
      res as Exn.Res clock =>
        let val result = Exn.capture0 (fn () => body run res) ()
        in free clock; Exn.release result end
    | absent => body run absent))


(** the measurement **)

type timing = {thread_cpu: Time.time option, elapsed: Time.time, cpu: Time.time, gc: Time.time}

(*the thread readings sit inside the Timing window: thread_cpu is not charged
  for Timing's own start and result, and thread_cpu <= elapsed (up to one tick
  where the clock is coarse)*)
fun timing f x =
  with_clock (fn run => fn res =>
    let
      val ({elapsed, cpu, gc}, (thread_cpu, y)) =
        Timing.timing (fn () =>
          let
            val started = Option.map (fn c => (c, read_own c)) (Exn.get_res res)
            val y = run f x
            val thread_cpu =
              Option.map (fn (c, start) => Time.fromNanoseconds (read_own c - start)) started
          in (thread_cpu, y) end) ()
    in ({thread_cpu = thread_cpu, elapsed = elapsed, cpu = cpu, gc = gc}, y) end)

fun cpu_timing f x = timing f x |>> #thread_cpu


(** the manager **)

(*the manager's shortest wait: bounds its wakeups when a guarded thread is
  starved of CPU, and bounds a limit's overshoot*)
val poll_floor = Time.fromMilliseconds 1

(*one guarded computation; deadline: an absolute reading of `clock', in nanoseconds*)
type registration = {clock: clock, deadline: int, thread: Isabelle_Thread.T}

datatype state =
  State of {registrations: registration Inttab.table, manager: Isabelle_Thread.T option}

val state =
  Synchronized.var "Thread_CPU.state" (State {registrations = Inttab.empty, manager = NONE})

(*nanoseconds remaining; 0 when due, and when the thread is gone*)
fun remaining ({clock, deadline, ...}: registration) =
  (case read_ns clock of
    NONE => 0
  | SOME ns => Int.max (deadline - ns, 0))

(*when to look again: the smallest time remaining, at least poll_floor away;
  NONE = nothing registered, wait for a change*)
fun wake_time (State {registrations, ...}) =
  Inttab.fold (fn (_, r) => fn w =>
      (case w of
        NONE => SOME (remaining r)
      | SOME w => SOME (Int.min (w, remaining r))))
    registrations NONE
  |> Option.map (fn w =>
      Time.now () + Time.fromNanoseconds (Int.max (w, Time.toNanoseconds poll_floor)))

(*fire one due registration, or NONE = nothing due yet.  The interrupt and the
  entry's removal are ONE critical section of `state' (synchronized.ML:83-86):
  a thread that finds its registration gone knows its interrupt was already
  issued, which is what lets `cancel' report "it had fired" and `apply' trust
  it.  Interrupting outside the lock would break that.*)
fun fire (State {registrations, manager}) =
  (case Inttab.get_first (fn (id, r) => if remaining r = 0 then SOME (id, r) else NONE) registrations of
    NONE => NONE
  | SOME (id, {thread, ...}) =>
      (Isabelle_Thread.interrupt_thread thread;
       SOME ((), State {registrations = Inttab.delete id registrations, manager = manager})))

fun manager_loop () =
  (Synchronized.timed_access state wake_time fire; manager_loop ())

(*event_timer.ML:130-132,163,170*)
fun manager_check manager =
  if is_some manager andalso Isabelle_Thread.is_active (the manager) then manager
  else SOME (Isabelle_Thread.fork (Isabelle_Thread.params "thread_cpu") manager_loop)

val new_id = Counter.make ()

fun register (registration: registration) =
  Synchronized.change_result state (fn State {registrations, manager} =>
    let val id = new_id () in
      (id, State {registrations = Inttab.update (id, registration) registrations,
        manager = manager_check manager})
    end)

(*revive the manager if it died; a separate step because forking can raise*)
fun revive () =
  Synchronized.change state (fn State {registrations, manager} =>
    State {registrations = registrations, manager = manager_check manager})

(*true = still pending (withdrawn now); false = it had fired.  The withdrawal
  itself cannot fail: from here the caller may free the clock*)
fun cancel id =
  Synchronized.change_result state (fn State {registrations, manager} =>
    (Inttab.defined registrations id,
      State {registrations = Inttab.delete_safe id registrations, manager = manager}))
  before revive ()


(** the timeout **)

(*the CPU limit on the calling thread's clock, inside with_clock: nothing
  between `register' and cancel's withdrawal can raise, so the clock is never
  freed while registered*)
fun cpu_limit clock limit run f x =
  let
    val start = read_own clock
    val deadline = start + Time.toNanoseconds (Timeout.scale_time limit)
    val id = register {clock = clock, deadline = deadline, thread = Isabelle_Thread.self ()}

    val result = Exn.capture_body (fn () => run f x)

    val was_timeout = not (cancel id)
    val stop = read_own clock
    val test = Isabelle_Thread.expose_interrupt_result ()
    (*our interrupt: proper, or a Breakdown after we fired (the flag-loss case)*)
    fun ours res =
      Exn.is_interrupt_proper_exn res orelse
      (was_timeout andalso
        (case res of Exn.Exn exn => Interrupt_Family.all_breakdown exn | _ => false))
  in
    if was_timeout andalso (ours result orelse ours test)
    then raise Timeout.TIMEOUT (Time.fromNanoseconds (stop - start))
    else (Exn.release test; Exn.release result)
  end

fun apply {thread_cpu, wall} f x =
  let
    (*an ignored limit is no limit: below, SOME means enforced*)
    val wall = Option.mapPartial (fn w => if Timeout.ignored w then NONE else SOME w) wall
    val under_wall = (case wall of NONE => I | SOME w => Timeout.apply w)
  in
    if Timeout.ignored thread_cpu then under_wall f x
    else
      under_wall (fn x =>
        with_clock (fn run =>
          fn Exn.Res clock => cpu_limit clock thread_cpu run f x
           | Exn.Exn (ERROR reason) =>
              (case wall of
                SOME _ =>
                  (warning ("Thread_CPU.apply: the thread CPU clock is unavailable; \
                            \only the wall-clock limit is enforced.\n" ^ reason);
                   run f x)
              | NONE => error ("Thread_CPU.apply: the thread CPU clock is unavailable.\n" ^ reason))
           | Exn.Exn exn => Exn.reraise exn (*self_or_reason: cannot happen*))) x
  end

end
